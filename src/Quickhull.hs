{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeOperators     #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use guards" #-}

-- https://hackage.haskell.org/package/accelerate-1.3.0.0/docs/Data-Array-Accelerate.html

module Quickhull (

  Point, Line, SegmentedPoints,
  quickhull,

  -- Exported for display
  initialPartition,
  partition,

  -- Exported just for testing
  propagateL, shiftHeadFlagsL, segmentedScanl1,
  propagateR, shiftHeadFlagsR, segmentedScanr1,

) where

import Data.Array.Accelerate
import Data.Array.Accelerate.Debug.Trace
import qualified Prelude                      as P
import Data.Array.Accelerate.Data.Maybe (isJust)


-- Points and lines in two-dimensional space
--
type Point = (Int, Int)
type Line  = (Point, Point)

-- This algorithm will use a head-flags array to distinguish the different
-- sections of the hull (the two arrays are always the same length).
-- 
-- 
-- A flag value of 'True' indicates that the corresponding point is
-- definitely on the convex hull. The points after the 'True' flag until
-- the next 'True' flag correspond to the points in the same segment, and
-- where the algorithm has not yet decided whether or not those points are
-- on the convex hull.
--
type SegmentedPoints = (Vector Bool, Vector Point)


-- Core implementation
-- -------------------

-- Initialise the algorithm by first partitioning the array into two
-- segments. Locate the left-most (p₁) and right-most (p₂) points. The
-- segment descriptor then consists of the point p₁, followed by all the
-- points above the line (p₁,p₂), followed by the point p₂, and finally all
-- of the points below the line (p₁,p₂).
--
-- To make the rest of the algorithm a bit easier, the point p₁ is again
-- placed at the end of the array. 
--
-- We indicate some intermediate values that you might find beneficial to
-- compute.
--

initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
      p1, p2 :: Exp Point
      p1 = the $ minimum points
      p2 = the $ maximum points

      isUpper :: Acc (Vector Bool)
      isUpper = map (pointIsLeftOfLine (T2 p1 p2)) points

      isLower :: Acc (Vector Bool)
      isLower = map (pointIsRightOfLine (T2 p1 p2)) points

      offsetUpper :: Acc (Vector Int)
      countUpper  :: Acc (Scalar Int)
      T2 offsetUpper countUpper = scanl' (+) 0 (map boolToInt isUpper)

      offsetLower :: Acc (Vector Int)
      countLower  :: Acc (Scalar Int)
      T2 offsetLower countLower = scanl' (+) 0 (map boolToInt isLower)

      -- ah yes
      p = points

      -- compute the index in the result array for each point (if it is present)
      destination :: Acc (Vector (Maybe DIM1))
      destination = zipWith5 combine p isUpper isLower offsetUpper offsetLower
        where
          combine :: Exp Point -> Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp (Maybe DIM1)
          combine p isUp isLow up low =
            cond isUp (Just_ $ I1 $ 1 + up) $
            cond isLow (Just_ $ I1 $ 2 + the countUpper + low) $
            cond (p == p1) (Just_ $ I1 0) $
            cond (p == p2) (Just_ $ I1 $ 1 + the countUpper) $
            Nothing_
      
      -- place each point into its corresponding segment of the result  
      newPoints :: Acc (Vector Point)
      newPoints = permute const result (destination !) points
        where
          result = generate (I1 arrsize) (const p1)
          arrsize = the countUpper + the countLower + 3

      -- create head flags array demarcating the initial segments
      headFlags :: Acc (Vector Bool)
      headFlags = map (\x -> x == p1 || x == p2) newPoints 
  in T2 headFlags newPoints


-- The core of the algorithm processes all line segments at once in
-- data-parallel. This is similar to the previous partitioning step, except
-- now we are processing many segments at once.
--
-- For each line segment (p₁,p₂) locate the point furthest from that line
-- p₃. This point is on the convex hull. Then determine whether each point
-- p in that segment lies to the left of (p₁,p₃) or the right of (p₂,p₃).
-- These points are undecided.
--
-- The algorithm then propagates the undecided points to the left and right
partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) = T2 newHeadFlags newPoints
    where
      --if two points consecutively are on the convex hull, then there are no more points in the segment
      noMorePointsInSegment :: Exp Bool -> Exp Bool -> Exp Bool
      noMorePointsInSegment current next = current && next

      --if the current point is on the convex hull, then the next point is not on the convex hull
      nextPointIsNotOnConvexHull :: Exp Bool -> Exp Bool -> Exp Bool
      nextPointIsNotOnConvexHull current next = current && not next

      furthestPoint :: Exp Line -> Acc (Vector Point) -> Acc (Scalar Point)
      furthestPoint line = fold1 (\p1 p2 -> cond (pointIsLeftOfLine line p1) p1 p2)

-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
--Quickhull, the algorithm
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull = init . asnd . awhile (any not . afst)  partition . initialPartition 


-- Helper functions
-- ----------------

propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL = segmentedScanl1 const

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR = segmentedScanr1 const 

shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL = stencil becomeRightNeighbour padWithTrue_
  where
    becomeRightNeighbour :: Stencil3 Bool -> Exp Bool
    becomeRightNeighbour (_, _, r) = r

    padWithTrue_ :: Boundary (Array DIM1 Bool)
    padWithTrue_ = function $ const True_

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR = stencil becomeLeftNeighbour padWithTrue_
  where
    becomeLeftNeighbour :: Stencil3 Bool -> Exp Bool
    becomeLeftNeighbour (l, _, _) = l

    padWithTrue_ :: Boundary (Array DIM1 Bool)
    padWithTrue_ = function $ const True_

segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 f bs vs = map snd (scanl1 (segmented f) zipped)
  where
    zipped = zip bs vs

segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 f bs vs = map snd (scanr1 (flip $ segmented f) zipped)
  where
    zipped = zip bs vs


-- Given utility functions
-- -----------------------

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

--this is not given, but makes it pleasent to write isLower
pointIsRightOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsRightOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y < c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

segmented :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (bF ? (bV, f aV bV))

