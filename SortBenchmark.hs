{-# LANGUAGE BangPatterns #-}
import Criterion.Main
import Control.Monad.ST
import Data.Array.ST
import Data.Foldable
import Control.Monad
import Control.Arrow
import System.Random
import Data.List
import qualified Data.Heap as DH -- from heap package
import qualified Data.PQueue.Min as DPQMin -- from pqueue package
import Data.Array.Base (unsafeRead, unsafeWrite)
import qualified Data.Vector.Algorithms.Intro as DVAI
import qualified Data.Vector.Unboxed as U
import System.Random.MWC
import Test.QuickCheck

-- STUArray qsort
-- http://stackoverflow.com/questions/11481675/using-vectors-for-performance-improvement-in-haskell
stuquick :: [Int] -> [Int]
stuquick [] = []
stuquick xs = runST (do
    let !len = length xs
    arr <- newListArray (0,len-1) xs
    myqsort arr 0 (len-1)
    -- Can't use getElems for large arrays, that overflows the stack, wth?
    let pick acc i
            | i < 0     = return acc
            | otherwise = do
                !v <- unsafeRead arr i
                pick (v:acc) (i-1)
    pick [] (len-1))

myqsort :: STUArray s Int Int -> Int -> Int -> ST s ()
myqsort a lo hi
   | lo < hi   = do
       let lscan p h i
               | i < h = do
                   v <- unsafeRead a i
                   if p < v then return i else lscan p h (i+1)
               | otherwise = return i
           rscan p l i
               | l < i = do
                   v <- unsafeRead a i
                   if v < p then return i else rscan p l (i-1)
               | otherwise = return i
           swap i j = do
               v <- unsafeRead a i
               unsafeRead a j >>= unsafeWrite a i
               unsafeWrite a j v
           sloop p l h
               | l < h = do
                   l1 <- lscan p h l
                   h1 <- rscan p l1 h
                   if (l1 < h1) then (swap l1 h1 >> sloop p l1 h1) else return l1
               | otherwise = return l
       piv <- unsafeRead a hi
       i <- sloop piv lo hi
       swap i hi
       myqsort a lo (i-1)
       myqsort a (i+1) hi
   | otherwise = return ()

-- adapter for stdlib introsort
-- ibidem
vsort :: [Int] -> [Int]
vsort xs = runST (do
    v <- U.unsafeThaw $ U.fromList xs
    DVAI.sort v
    s <- U.unsafeFreeze v
    return $ U.toList s)

-- heapsort
hsort :: [Int] -> [Int]
hsort xs = DH.toAscList (DH.fromList xs :: DH.MinHeap Int)

-- another heapsort

hpqsort :: [Int] -> [Int]
hpqsort xs = DPQMin.toAscList (DPQMin.fromList xs)

-- http://stackoverflow.com/questions/5268156/how-do-you-do-an-in-place-quicksort-in-haskell
partitionz arr left right pivotIndex = do
    pivotValue <- readArray arr pivotIndex
    swap arr pivotIndex right
    storeIndex <- foreachWith [left..right-1] left (\i storeIndex -> do
        val <- readArray arr i
        if (val <= pivotValue)
            then do
                 swap arr i storeIndex
                 return (storeIndex + 1)
            else do
                 return storeIndex )
    swap arr storeIndex right
    return storeIndex

qsort arr left right = when (right > left) $ do
    let pivotIndex = left + ((right-left) `div` 2)
    newPivot <- partitionz arr left right pivotIndex

    qsort arr left (newPivot - 1)
    qsort arr (newPivot + 1) right

-- wrapper to sort a list as an array
sortList xs = runST $ do
    let lastIndex = length xs - 1
    arr <- newListArray (0,lastIndex) xs :: ST s (STUArray s Int Int)
    qsort arr 0 lastIndex
    newXs <- getElems arr
    return newXs

-- helpers
swap arr left right = do
    leftVal <- readArray arr left
    rightVal <- readArray arr right
    writeArray arr left rightVal
    writeArray arr right leftVal

-- foreachWith takes a list, and a value that can be modified by the function, and
-- it returns the modified value after mapping the function over the list.  
foreachWith xs v f = foldlM (flip f) v xs

-- qsorts below
-- http://en.literateprograms.org/Quicksort_%28Haskell%29#chunk use:qsort.hs
qsort1 []     = []
qsort1 (p:xs) = qsort1 lesser ++ [p] ++ qsort1 greater
    where
        lesser  = [ y | y <- xs, y < p ]
        greater = [ y | y <- xs, y >= p ]

qsort3 :: Ord a => [a] -> [a]
qsort3 x = qsort3' x []

qsort3' [] y     = y
qsort3' [x] y    = x:y
qsort3' (x:xs) y = part xs [] [x] []  
    where
        part [] l e g = qsort3' l (e ++ (qsort3' g y))
        part (z:zs) l e g 
            | z > x     = part zs l e (z:g) 
            | z < x     = part zs (z:l) e g 
            | otherwise = part zs l (z:e) g

-- end of quicksorts
-- first of heapsorts
-- http://stackoverflow.com/questions/932721/efficient-heaps-in-purely-functional-languages
treefold f zero [] = zero
treefold f zero [x] = x
treefold f zero (a:b:l) = treefold f zero (f a b : pairfold l)
    where 
        pairfold (x:y:rest) = f x y : pairfold rest
        pairfold l = l -- here l will have fewer than 2 elements

data Heap a = Nil | Node a [Heap a]
heapify x = Node x []

heapsort :: Ord a => [a] -> [a]    
heapsort = flatten_heap . merge_heaps . map heapify    
    where 
        merge_heaps :: Ord a => [Heap a] -> Heap a
        merge_heaps = treefold merge_heap Nil

        flatten_heap Nil = []
        flatten_heap (Node x heaps) = x:flatten_heap (merge_heaps heaps)

        merge_heap heap Nil = heap
        merge_heap node_a@(Node a heaps_a) node_b@(Node b heaps_b)
            | a < b = Node a (node_b: heaps_a)
            | otherwise = Node b (node_a: heaps_b)

-- bottomup mergesort, hopefully
-- http://en.literateprograms.org/Merge_sort_(Haskell)
merge :: (a -> a -> Bool) -> [a] -> [a] -> [a]
merge pred xs []         = xs
merge pred [] ys         = ys
merge pred (x:xs) (y:ys)
    | pred x y = x: merge pred xs (y:ys)
    | otherwise = y: merge pred (x:xs) ys

mergesort pred [] = []
mergesort pred xs = go [[x] | x <- xs]
  where
    go xs@(_:_:_)  = go (pairs xs)
    go [xs]        = xs
    pairs (x:y:xs) = merge pred x y : pairs xs
    pairs xs       = xs

msort :: [Int] -> [Int]
msort xs = mergesort (<=) xs

split2 :: [a] -> ([a],[a])
split2 xs = go xs xs where
  go (x:xs) (_:_:zs) = (x:us,vs) where (us,vs)=go xs zs
  go    xs   _       = ([],xs)

mergesort2 :: (a -> a -> Bool) -> [a] -> [a]
mergesort2 pred []   = []
mergesort2 pred [x]  = [x]
mergesort2 pred xs = merge pred (mergesort2 pred xs1) (mergesort2 pred xs2)
  where
    (xs1,xs2) = split2 xs

msort2 :: [Int] -> [Int]
msort2 xs = mergesort2 (<=) xs

-- end of sorts, start auxiliary

randomLst :: Int -> StdGen -> [Int]
randomLst n = take n . unfoldr (Just . random)

randomLst2 :: Int -> Int -> [Int]
randomLst2 n seed = take n . randomRs (0, 500000) . mkStdGen $ seed

-- test examples, unused atm
sortit n = sortList (randomLst n (mkStdGen 1020))

sortit1 n = qsort1 (randomLst n (mkStdGen 1020))

sortit3 n = qsort3 (randomLst n (mkStdGen 1020))

sortitstu n = stuquick (randomLst n (mkStdGen 1020))

sortitv n = vsort (randomLst n (mkStdGen 1020))

sortith n = hsort (randomLst n (mkStdGen 1020))

-- http://cseweb.ucsd.edu/classes/wi11/cse230/lectures/quickcheck.html
-- usage: quickCheckN 10000 prop_qsort_isOrdered

isOrdered (x1:x2:xs) = x1 <= x2 && isOrdered (x2:xs)
isOrdered _ = True

prop_qsort_isOrdered :: [Int] -> Bool
prop_qsort_isOrdered = isOrdered . qsort1

quickCheckN n = quickCheckWith $ stdArgs { maxSuccess = n }

type V = U.Vector Int

-- some more testing stuff

minuses :: [Int] -> [Int]
minuses xs = map negate xs

minusesmonadic :: [Int] -> [Int]
minusesmonadic xs = xs >>= (\x -> [-x])

--

numbers :: IO (V, V)
numbers = do
  short <- withSystemRandom . asGenIO $ \gen -> uniformVector gen 20000
  long  <- withSystemRandom . asGenIO $ \gen -> uniformVector gen 500000
  return (short, long)

-- to run
-- http://www.serpentine.com/criterion/tutorial.html
-- ghc -O --make SortBenchmark
-- SortBenchmark.exe --output sortbench.html
-- if fails - chcp 65001

main :: IO ()
main = defaultMain [
     env numbers $ \ ~(short, long) ->
     bgroup "clean map" [ bench "20000"  $ nf minuses (U.toList short)
               , bench "500000"  $ nf minuses (U.toList long)
               ],
     env numbers $ \ ~(short, long) ->
     bgroup "monadic map" [ bench "20000"  $ nf minusesmonadic (U.toList short)
               , bench "500000"  $ nf minusesmonadic (U.toList long)
               ],
     env numbers $ \ ~(short, long) ->
     bgroup "qsort funct. less space" [ bench "20000"  $ nf qsort3 (U.toList short)
               , bench "500000"  $ nf qsort3 (U.toList long)
               ],
     env numbers $ \ ~(short, long) ->
     bgroup "qsort functional" [ bench "20000" $ nf qsort1 (U.toList short)
               , bench "500000"  $ nf qsort1 (U.toList long)
               ],
     env numbers $ \ ~(short, long) ->
     bgroup "qsort" [ bench "20000" $ nf sortList (U.toList short)
               , bench "500000" $ nf sortList (U.toList long)
               ],
     env numbers $ \ ~(short, long) ->
     bgroup "imperative qsort" [ bench "20000" $ nf stuquick (U.toList short)
               , bench "500000" $ nf stuquick (U.toList long)
               ],
     env numbers $ \ ~(short, long) ->
     bgroup "built-in introsort" [ bench "20000" $ nf vsort (U.toList short)
               , bench "500000" $ nf vsort (U.toList long)
               ],
     env numbers $ \ ~(short, long) ->
     bgroup "leftist heapsort in-line" [ bench "20000" $ nf heapsort (U.toList short)
               , bench "500000" $ nf heapsort (U.toList long)
               ],
     env numbers $ \ ~(short, long) ->
     bgroup "PQueue heapsort" [ bench "20000" $ nf hpqsort (U.toList short)
               , bench "500000" $ nf hpqsort (U.toList long)
               ],
     env numbers $ \ ~(short, long) ->
     bgroup "Leftist Heap heapsort" [ bench "20000" $ nf hsort (U.toList short)
               , bench "500000" $ nf hsort (U.toList long)
               ],
     env numbers $ \ ~(short, long) ->
     bgroup "bottom-up mergesort" [ bench "20000" $ nf msort (U.toList short)
               , bench "500000" $ nf msort (U.toList long)
               ],
     env numbers $ \ ~(short, long) ->
     bgroup "top-down mergesort" [ bench "20000" $ nf msort2 (U.toList short)
               , bench "500000" $ nf msort2 (U.toList long)
               ]
     ]

