{-# LANGUAGE RecordWildCards  #-}
--
-- INFOB3CC Concurrency
-- Practical 2: Single Source Shortest Path
--
--    Δ-stepping: A parallelisable shortest path algorithm
--    https://www.sciencedirect.com/science/article/pii/S0196677403000762
--
-- https://ics.uu.nl/docs/vakken/b3cc/assessment.html
--
-- https://cs.iupui.edu/~fgsong/LearnHPC/sssp/deltaStep.html
--

module DeltaStepping (

  Graph, Node, Distance,
  deltaStepping,

) where

import Sample
import Utils

import Control.Concurrent
import Control.Concurrent.MVar
import Control.Monad
import Data.Bits
import Data.Graph.Inductive                                         ( Gr )
import Data.IORef
import Data.IntMap.Strict                                           ( IntMap )
import Data.IntSet                                                  ( IntSet )
import Data.Vector.Storable                                         ( Vector )
import Data.Word
import Foreign.Ptr
import Foreign.Storable
import Text.Printf
import qualified Data.Graph.Inductive                               as G
import qualified Data.IntMap.Strict                                 as Map
import qualified Data.IntSet                                        as Set
import qualified Data.Vector.Mutable                                as V
import qualified Data.Vector.Storable                               as M ( unsafeFreeze )
import qualified Data.Vector.Storable.Mutable                       as M

-- Data types

type Graph    = Gr String Distance  -- Graphs have nodes labelled with Strings and edges labelled with their distance
type Node     = Int                 -- Nodes (vertices) in the graph are integers in the range [0..]
type Distance = Float               -- Distances between nodes are (positive) floating point values


-- | Find the length of the shortest path from the given node to all other nodes
-- in the graph. If the destination is not reachable from the starting node the
-- distance is 'Infinity'.
--
-- Nodes must be numbered [0..]
--
-- Negative edge weights are not supported.
--
-- NOTE: The type of the 'deltaStepping' function should not change (since that
-- is what the test suite expects), but you are free to change the types of all
-- other functions and data structures in this module as you require.
--
deltaStepping
    :: Bool                             -- Whether to print intermediate states to the console, for debugging purposes
    -> Graph                            -- graph to analyse
    -> Distance                         -- delta (step width, bucket width)
    -> Node                             -- index of the starting node
    -> IO (Vector Distance)
deltaStepping verbose graph delta source = do
  -- Get the number of threads available for parallel execution
  num_threads <- getNumCapabilities
  -- Initialise the state: buckets and tentative distances
  (buck, tent) <- initialise graph delta source
  -- Relax the source node to initialize the algorithm
  relax buck tent delta (source, 0)
  -- Perform delta-stepping until all buckets are empty
  deltaStep buck tent num_threads
  -- Convert mutable distances to an immutable vector for return
  M.unsafeFreeze tent
  where
    -- Recursively perform steps of the delta-stepping algorithm
    deltaStep :: Buckets -> TentativeDistances -> Int -> IO ()
    deltaStep buck tent threads = do
      weGood <- allBucketsEmpty buck
      unless weGood $ do
        step verbose graph delta buck tent threads
        deltaStep buck tent threads
-- Initialise algorithm state
--
initialise
    :: Gr String Distance
    -> Distance
    -> Node
    -> IO (Buckets, TentativeDistances)
initialise graph delta source = do
  -- Determine maximum edge weight to calculate bucket count
  let maxWeight = maximum [d | (_, _, d) <- G.labEdges graph]
  let noOfBuckets = ceiling (maxWeight / delta)  -- Dynamically determine bucket count

  -- Create a reference for the index of the first bucket
  firstBucketIndex <- newIORef 0
  -- Initialize buckets as an array of empty sets
  bucketArray <- V.replicate noOfBuckets Set.empty

  let buckets = Buckets firstBucketIndex bucketArray

  -- Initialize tentative distances to infinity
  tentDistances <- M.replicate (G.noNodes graph) infinity
  -- Set the source node's tentative distance to 0
  M.write tentDistances source 0

  return (buckets, tentDistances)


-- Take a single step of the algorithm.
-- That is, one iteration of the outer while loop.
--
step :: Bool -> Graph -> Distance -> Buckets -> TentativeDistances -> Int -> IO ()
step verbose graph delta buck@(Buckets i arr) tent threads = do
  -- Find the smallest non-empty bucket and update the first bucket reference
  smallestBuckIndex <- findNextBucket buck
  writeIORef i smallestBuckIndex

  -- Perform the inner while loop and collect requests for relaxation
  r <- innerWhile graph delta buck tent Set.empty threads

  -- Process long-range requests for edges exceeding delta threshold
  req <- findRequests (>= delta) graph r tent
  relaxRequests buck tent delta req threads

-- Perform the inner while loop of the delta-stepping algorithm
-- Moves through the current bucket and processes nodes with edges < delta
innerWhile :: Graph -> Distance -> Buckets -> TentativeDistances -> IntSet -> Int -> IO (IntSet)
innerWhile graph delta buck@(Buckets i arr) tent toDelete threads = do
  bucketIndex <- readIORef i
  currentIntSet <- V.read arr bucketIndex

  if not (Set.null currentIntSet)
    then do
      -- Find requests for edges with weights < delta
      req <- findRequests (< delta) graph currentIntSet tent
      let onion = Set.union toDelete currentIntSet

      -- Clear the current bucket
      V.write arr bucketIndex Set.empty

      -- Relax the requests and recurse
      relaxRequests buck tent delta req threads
      innerWhile graph delta buck tent onion threads
    else return toDelete
    
-- Adjust the firstBucket index to point to the next non-empty bucket
adjustFirstBucket :: Buckets -> IO ()
adjustFirstBucket Buckets{..} = do
  let bucketCount = V.length bucketArray
  newFirst <- foldM
    (\currentMin i -> do
      bucket <- V.read bucketArray i
      if Set.null bucket then return currentMin else return (min currentMin i))
    bucketCount
    [0 .. bucketCount - 1]
  writeIORef firstBucket newFirst

-- Once all buckets are empty, the tentative distances are finalised, and the
-- algorithm terminates.
--
allBucketsEmpty :: Buckets -> IO Bool
allBucketsEmpty (Buckets i arr) = readIORef i >>= \x -> go (V.drop x arr)
  where
    go :: V.IOVector IntSet -> IO Bool
    go v | V.null v  = return True
         | otherwise = do
             h <- V.read v 0
             if Set.null h
               then go (V.drop 1 v)
               else return False

-- Return the index of the smallest non-empty bucket. Assumes that there is at
-- least one non-empty bucket remaining.
--
findNextBucket :: Buckets -> IO Int
findNextBucket Buckets{..} = do
  bucketIndex <- readIORef firstBucket
  let findNonEmpty idx = do
        bucket <- V.read bucketArray idx
        if Set.null bucket then findNonEmpty ((idx + 1) `mod` V.length bucketArray) else return idx
  findNonEmpty bucketIndex

-- Create requests of (node, distance) pairs that fulfil the given predicate
--
findRequests
    :: (Distance -> Bool)
    -> Gr String Distance
    -> IntSet
    -> TentativeDistances
    -> IO (IntMap Distance)
findRequests p graph v' tent = do
  let bucketContents = Set.elems v'
  let filteredEdges = filter
        (\(from, _, d) -> p d && from `elem` bucketContents)
        (G.labEdges graph)
  requests <- mapM createRequest filteredEdges
  return (Map.unionsWith min requests)
  where
    createRequest :: G.LEdge Float -> IO (IntMap Distance)
    createRequest (v, w, c) = do
      tentativeDistanceV <- M.read tent v
      return (Map.singleton w (tentativeDistanceV + c))

-- Execute requests for each of the given (node, distance) pairs
--
relaxRequests
    :: Buckets
    -> TentativeDistances
    -> Distance
    -> IntMap Distance
    -> Int
    -> IO ()
relaxRequests buckets tent delta req threads = do
  let requests = Map.toAscList req
      requestChunks = chunks (length requests `div` threads + 1) requests
  forkThreads (length requestChunks) (\i -> mapM_ (relax buckets tent delta) (requestChunks !! i))
  where
    chunks n xs = takeWhile (not . null) (map (take n) (iterate (drop n) xs))

-- Execute a single relaxation, moving the given node to the appropriate bucket
-- as necessary
--
relax :: Buckets -> TentativeDistances -> Distance -> (Node, Distance) -> IO ()
relax Buckets{..} tent delta (w, x) = do
  let bs = bucketArray
  tentW <- M.read tent w
  when (x < tentW) $ do
    unless (isInfinite tentW) $
      V.modify bs (Set.delete w) (round $ tentW / delta)
    V.modify bs (Set.insert w) (round $ x / delta)
    M.write tent w x


-- -----------------------------------------------------------------------------
-- Starting framework
-- -----------------------------------------------------------------------------
--
-- Here are a collection of (data)types and utility functions that you can use.
-- You are free to change these as necessary.
--

type TentativeDistances = M.IOVector Distance

data Buckets = Buckets
  { firstBucket   :: {-# UNPACK #-} !(IORef Int)           -- real index of the first bucket (j)
  , bucketArray   :: {-# UNPACK #-} !(V.IOVector IntSet)   -- cyclic array of buckets
  }


-- The initial tentative distance, or the distance to unreachable nodes
--
infinity :: Distance
infinity = 1/0


-- Forks 'n' threads. Waits until those threads have finished. Each thread
-- runs the supplied function given its thread ID in the range [0..n).
--
forkThreads :: Int -> (Int -> IO ()) -> IO ()
forkThreads n action = do
  -- Fork the threads and create a list of the MVars which per thread tell
  -- whether the action has finished.
  finishVars <- mapM work [0 .. n - 1]
  -- Once all the worker threads have been launched, now wait for them all to
  -- finish by blocking on their signal MVars.
  mapM_ takeMVar finishVars
  where
    -- Create a new empty MVar that is shared between the main (spawning) thread
    -- and the worker (child) thread. The main thread returns immediately after
    -- spawning the worker thread. Once the child thread has finished executing
    -- the given action, it fills in the MVar to signal to the calling thread
    -- that it has completed.
    --
    work :: Int -> IO (MVar ())
    work index = do
      done <- newEmptyMVar
      _    <- forkOn index (action index >> putMVar done ())  -- pin the worker to a given CPU core
      return done


printVerbose :: Bool -> String -> Graph -> Distance -> Buckets -> TentativeDistances -> IO ()
printVerbose verbose title graph delta buckets distances = when verbose $ do
  putStrLn $ "# " ++ title
  printCurrentState graph distances
  printBuckets graph delta buckets distances
  putStrLn "Press enter to continue"
  _ <- getLine
  return ()

-- Print the current state of the algorithm (tentative distance to all nodes)
--
printCurrentState
    :: Graph
    -> TentativeDistances
    -> IO ()
printCurrentState graph distances = do
  printf "  Node  |  Label  |  Distance\n"
  printf "--------+---------+------------\n"
  forM_ (G.labNodes graph) $ \(v, l) -> do
    x <- M.read distances v
    if isInfinite x
       then printf "  %4d  |  %5v  |  -\n" v l
       else printf "  %4d  |  %5v  |  %f\n" v l x
  --
  printf "\n"

printBuckets
    :: Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
printBuckets graph delta Buckets{..} distances = do
  first <- readIORef firstBucket
  mapM_
    (\idx -> do
      let idx' = first + idx
      printf "Bucket %d: [%f, %f)\n" idx' (fromIntegral idx' * delta) ((fromIntegral idx'+1) * delta)
      b <- V.read bucketArray (idx' `rem` V.length bucketArray)
      printBucket graph b distances
    )
    [ 0 .. V.length bucketArray - 1 ]

-- Print the current bucket
--
printCurrentBucket
    :: Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
printCurrentBucket graph delta Buckets{..} distances = do
  j <- readIORef firstBucket
  b <- V.read bucketArray (j `rem` V.length bucketArray)
  printf "Bucket %d: [%f, %f)\n" j (fromIntegral j * delta) (fromIntegral (j+1) * delta)
  printBucket graph b distances

-- Print a given bucket
--
printBucket
    :: Graph
    -> IntSet
    -> TentativeDistances
    -> IO ()
printBucket graph bucket distances = do
  printf "  Node  |  Label  |  Distance\n"
  printf "--------+---------+-----------\n"
  forM_ (Set.toAscList bucket) $ \v -> do
    let ml = G.lab graph v
    x <- M.read distances v
    case ml of
      Nothing -> printf "  %4d  |   -   |  %f\n" v x
      Just l  -> printf "  %4d  |  %5v  |  %f\n" v l x
  --
  printf "\n"