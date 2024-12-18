{-# LANGUAGE RecordWildCards  #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant return" #-}
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
import Data.Maybe


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
  threadCount <- getNumCapabilities             -- the number of (kernel) threads to use: the 'x' in '+RTS -Nx'

  -- Initialise the algorithm
  (buckets, distances)  <- initialise graph delta source
  printVerbose verbose "initialse" graph delta buckets distances

  let
    -- The algorithm loops while there are still non-empty buckets
    loop = do
      done <- allBucketsEmpty buckets
      if done
      then return ()
      else do
        printVerbose verbose "result" graph delta buckets distances
        step verbose threadCount graph delta buckets distances
        loop
  loop

  printVerbose verbose "result" graph delta buckets distances
  -- Once the tentative distances are finalised, convert into an immutable array
  -- to prevent further updates. It is safe to use this "unsafe" function here
  -- because the mutable vector will not be used any more, so referential
  -- transparency is preserved for the frozen immutable vector.
  --
  -- NOTE: The function 'Data.Vector.convert' can be used to translate between
  -- different (compatible) vector types (e.g. boxed to storable)
  --
  M.unsafeFreeze distances

-- Initialise algorithm state
--
initialise
    :: Graph
    -> Distance
    -> Node
    -> IO (Buckets, TentativeDistances)
initialise graph delta source = do
  let nodeCount = G.order graph -- Total number of nodes in the graph

  -- Create an array of tentative distances and initialize all nodes to infinity
  distances <- M.replicate nodeCount infinity

  -- Set the distance of the source node to 0
  M.write distances source 0.0

  -- Create the cyclic bucket array with an initial size (e.g., 1 + maxBucketIndex)
  let bucketCount = max 1 (ceiling (fromIntegral nodeCount / delta))
  bucketArray <- V.replicate bucketCount Set.empty

  -- Add the source node to the first bucket
  let firstBucketIndex = 0
  V.modify bucketArray (Set.insert source) firstBucketIndex

  -- Create an IORef to keep track of the index of the first non-empty bucket
  firstBucket <- newIORef firstBucketIndex

  -- Return the initialized state
  return (Buckets { firstBucket = firstBucket, bucketArray = bucketArray }, distances)


-- Take a single step of the algorithm.
-- That is, one iteration of the outer while loop.
--
step
    :: Bool
    -> Int
    -> Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
step verbose threadCount graph delta buckets@Buckets{..} distances = do
  -- Retrieve the first non-empty bucket
  currentBucketIndex <- readIORef firstBucket
  currentBucket <- V.read bucketArray (currentBucketIndex `mod` V.length bucketArray)
  
  if Set.null currentBucket
    then do
      -- Find the next non-empty bucket
      nextBucketIndex <- findNextBucket buckets
      writeIORef firstBucket nextBucketIndex
    else do
      -- Process all light edges (weight <= delta)
      lightRequests <- findRequests
        threadCount
        (<= delta)
        graph
        currentBucket
        distances
      relaxRequests threadCount buckets distances delta lightRequests
      
      -- Re-check the current bucket for updates after processing light edges
      currentBucket <- V.read bucketArray (currentBucketIndex `mod` V.length bucketArray)
      
      -- Process all heavy edges (weight > delta)
      heavyRequests <- findRequests
        threadCount
        (> delta)
        graph
        currentBucket
        distances
      relaxRequests threadCount buckets distances delta heavyRequests

      -- Empty the current bucket
      V.write bucketArray (currentBucketIndex `mod` V.length bucketArray) Set.empty

      -- Update the first bucket to point to the next non-empty bucket
      nextBucketIndex <- findNextBucket buckets
      writeIORef firstBucket nextBucketIndex
      
      -- Debug output if verbose mode is enabled
      when verbose $ do
        printVerbose verbose "step" graph delta buckets distances


-- Once all buckets are empty, the tentative distances are finalised and the
-- algorithm terminates.
--
allBucketsEmpty :: Buckets -> IO Bool
allBucketsEmpty Buckets{..} = do
  -- Get the current state of the buckets
  let bucketCount = V.length bucketArray -- `V.length` is not in IO, so we use `let`
  allEmpty <- allM (\i -> do
    bucket <- V.read bucketArray i
    return (Set.null bucket)) [0 .. bucketCount - 1]
  return allEmpty

-- Helper function to apply a monadic predicate to all elements of a list
allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ [] = return True
allM p (x:xs) = do
  q <- p x
  if q then allM p xs else return False


-- Return the index of the smallest on-empty bucket. Assumes that there is at
-- least one non-empty bucket remaining.
--
findNextBucket :: Buckets -> IO Int
findNextBucket Buckets{..} = do
  let totalBuckets = V.length bucketArray -- Get the total number of buckets
  startIndex <- readIORef firstBucket
  let indices = [startIndex .. startIndex + totalBuckets - 1]
  foldM findNonEmpty (-1) indices
  where
    -- Helper function to locate the first non-empty bucket
    findNonEmpty :: Int -> Int -> IO Int
    findNonEmpty acc idx
      | acc /= -1 = return acc -- Stop searching if a non-empty bucket is found
      | otherwise = do
          let index = idx `mod` V.length bucketArray -- Ensure cyclic indexing
          bucket <- V.read bucketArray index
          if Set.null bucket
            then return acc -- Continue searching
            else return index

-- Safe indexing function for lists
safeIndex :: [a] -> Int -> Maybe a
safeIndex xs i
  | i < 0 || i >= length xs = Nothing
  | otherwise = Just (xs !! i)

divideWork :: Int -> [a] -> [[a]]
divideWork n xs =
  let chunkSize = ceiling (fromIntegral (length xs) / fromIntegral n)
  in takeWhile (not . null) (map (take chunkSize) (iterate (drop chunkSize) xs))

-- Create requests of (node, distance) pairs that fulfil the given predicate
--
findRequests
    :: Int                        -- Number of threads
    -> (Distance -> Bool)         -- Predicate to filter distances
    -> Graph                      -- The graph to process
    -> IntSet                     -- Subset of nodes to process
    -> TentativeDistances         -- Current tentative distances
    -> IO (IntMap Distance)       -- Resulting requests (node -> distance)
findRequests threadCount predicate graph nodes distances = do
  resultMap <- newIORef Map.empty
  let nodeList = Set.toList nodes
      chunks = divideWork threadCount nodeList
  forkThreads threadCount (processChunk resultMap) chunks
  readIORef resultMap
  where
    -- Process a chunk of nodes, updating the resultMap
    processChunk resultMap _ chunk = do
      forM_ chunk $ \node -> do
        dist <- M.read distances node
        when (predicate dist) $ do
          let edges = G.out graph node  -- Outgoing edges (node, neighbor, weight)
          forM_ edges $ \(from, to, weight) -> do
            let newDistance = dist + weight
            atomicModifyIORef' resultMap (\m -> (Map.insertWith min to newDistance m, ()))


-- Execute requests for each of the given (node, distance) pairs
--
relaxRequests
    :: Int                    -- Number of threads
    -> Buckets                -- The structure holding buckets
    -> TentativeDistances     -- Current tentative distances
    -> Distance               -- Delta (bucket width)
    -> IntMap Distance        -- Requests (node -> new tentative distance)
    -> IO ()
relaxRequests threadCount buckets distances delta requests = do
  let requestList = Map.toList requests
      chunks = divideWork threadCount requestList
  forkThreads threadCount processChunk chunks
  where
    processChunk _ chunk = forM_ chunk $ \(node, newDistance) -> relax buckets distances delta (node, newDistance)


-- Execute a single relaxation, moving the given node to the appropriate bucket
-- as necessary
--
relax
    :: Buckets
    -> TentativeDistances
    -> Distance
    -> (Node, Distance) -- (w, x) in the paper
    -> IO ()
relax Buckets{..} distances delta (node, newDistance) = do
  currentDistance <- M.read distances node
  when (newDistance < currentDistance) $ do
    -- Atomically update the distance and check if the update was successful
    (success, _) <- casIOVectorFloat distances node currentDistance newDistance
    when success $ do
      -- Calculate the old and new bucket indices
      let oldBucketIdx = floor (currentDistance / delta)
          newBucketIdx = floor (newDistance / delta)
      when (oldBucketIdx /= newBucketIdx) $ do
        -- Remove from old bucket (if applicable)
        V.modify bucketArray (Set.delete node) (oldBucketIdx `mod` V.length bucketArray)
        -- Add to new bucket
        V.modify bucketArray (Set.insert node) (newBucketIdx `mod` V.length bucketArray)


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
forkThreads :: Int -> (Int -> [a] -> IO ()) -> [[a]] -> IO ()
forkThreads n action chunks = do
  finishVars <- forM [0 .. n - 1] $ \i -> do
    let chunk = fromMaybe [] (safeIndex chunks i)
    done <- newEmptyMVar
    _ <- forkOn i (action i chunk >> putMVar done ())
    return done
  mapM_ takeMVar finishVars


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
      b <- V.read bucketArray (idx' `mod` V.length bucketArray)
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
  b <- V.read bucketArray (j `mod` V.length bucketArray)
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