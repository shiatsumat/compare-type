{-# LANGUAGE Trustworthy,
    TypeOperators,
    PolyKinds, DataKinds,
    TypeFamilies,
    UndecidableInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module: Type.Compare
-- Copyright: (c) Yusuke Matsushita 2015
-- License: BSD3
-- Maintainer: Yusuke Matsushita
-- Stability: provisional
-- Portability: portable
--
-- Compare two types of any (possibly different) kinds.
--------------------------------------------------------------------------------

module Type.Compare (
    -- * Base
    Compare,
    LargestK(Largest), SmallestK(Smallest),
    CompareUser,
    -- * Utility
    OrdCase, CompareCase,
    type (<!), type (>=!), type (>!), type (<=!),
    Max, Min
  ) where

import Data.Ord
import GHC.TypeLits

type family (a :: Ordering) $$ (b :: Ordering) :: Ordering where
  LT $$ b = LT
  GT $$ b = GT
  EQ $$ b = b
infixl 0 $$

-- | The largest type (and kind) on 'Compare'.
data LargestK = Largest
-- | The smallest type (and kind) on 'Compare'.
data SmallestK = Smallest

-- | Compare two types of any (possibly different) kinds.
-- Since `Compare` itself is a closed type family, add instances to `CompareUser` if you want to compare other types.
type family Compare (a :: k) (b :: k') :: Ordering where

  Compare (Down a) (Down b) = Compare b a

  Compare Largest Largest = EQ
  Compare _' Largest = LT
  Compare Largest _' = GT
  Compare Smallest Smallest = EQ
  Compare _' Smallest = GT
  Compare Smallest _' = LT

  Compare False False = EQ
  Compare False True = LT
  Compare True False = GT
  Compare True True = EQ

  Compare LT LT = EQ
  Compare LT EQ = LT
  Compare LT GT = LT
  Compare EQ LT = GT
  Compare EQ EQ = EQ
  Compare EQ GT = LT
  Compare GT LT = GT
  Compare GT EQ = GT
  Compare GT GT = EQ

  Compare m n = CmpNat m n

  Compare s t = CmpSymbol s t

  Compare Nothing Nothing = EQ
  Compare Nothing (Just b) = LT
  Compare (Just a) Nothing = GT
  Compare (Just a) (Just b) = Compare a b

  Compare (Left _') (Right _'') = LT
  Compare (Right _') (Left _'') = GT
  Compare (Left a) (Left b) = Compare a b
  Compare (Right a) (Right b) = Compare a b

  Compare '[] '[] = EQ
  Compare '[] (b ': bs) = LT
  Compare (a ': as) '[] = GT
  Compare (a ': as) (b ': bs) = Compare a b $$ Compare as bs

  Compare '() '() = EQ
  Compare '(a1, a2) '(b1, b2) = Compare a1 b1 $$ Compare a2 b2
  Compare '(a1, a2, a3) '(b1, b2, b3) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3
  Compare '(a1, a2, a3, a4) '(b1, b2, b3, b4) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4
  Compare '(a1, a2, a3, a4, a5) '(b1, b2, b3, b4, b5) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5
  Compare '(a1, a2, a3, a4, a5, a6) '(b1, b2, b3, b4, b5, b6) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5 $$ Compare a6 b6
  Compare '(a1, a2, a3, a4, a5, a6, a7) '(b1, b2, b3, b4, b5, b6, b7) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5 $$ Compare a6 b6 $$ Compare a7 b7
  Compare '(a1, a2, a3, a4, a5, a6, a7, a8) '(b1, b2, b3, b4, b5, b6, b7, b8) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5 $$ Compare a6 b6 $$ Compare a7 b7 $$ Compare a8 b8
  Compare '(a1, a2, a3, a4, a5, a6, a7, a8, a9) '(b1, b2, b3, b4, b5, b6, b7, b8, b9) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5 $$ Compare a6 b6 $$ Compare a7 b7 $$ Compare a8 b8 $$ Compare a9 b9
  Compare '(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) '(b1, b2, b3, b4, b5, b6, b7, b8, b9, b10) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5 $$ Compare a6 b6 $$ Compare a7 b7 $$ Compare a8 b8 $$ Compare a9 b9 $$ Compare a10 b10

  Compare () () = EQ
  Compare (a1, a2) (b1, b2) = Compare a1 b1 $$ Compare a2 b2
  Compare (a1, a2, a3) (b1, b2, b3) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3
  Compare (a1, a2, a3, a4) (b1, b2, b3, b4) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4
  Compare (a1, a2, a3, a4, a5) (b1, b2, b3, b4, b5) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5
  Compare (a1, a2, a3, a4, a5, a6) (b1, b2, b3, b4, b5, b6) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5 $$ Compare a6 b6
  Compare (a1, a2, a3, a4, a5, a6, a7) (b1, b2, b3, b4, b5, b6, b7) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5 $$ Compare a6 b6 $$ Compare a7 b7
  Compare (a1, a2, a3, a4, a5, a6, a7, a8) (b1, b2, b3, b4, b5, b6, b7, b8) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5 $$ Compare a6 b6 $$ Compare a7 b7 $$ Compare a8 b8
  Compare (a1, a2, a3, a4, a5, a6, a7, a8, a9) (b1, b2, b3, b4, b5, b6, b7, b8, b9) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5 $$ Compare a6 b6 $$ Compare a7 b7 $$ Compare a8 b8 $$ Compare a9 b9
  Compare (a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10) = Compare a1 b1 $$ Compare a2 b2 $$ Compare a3 b3 $$ Compare a4 b4 $$ Compare a5 b5 $$ Compare a6 b6 $$ Compare a7 b7 $$ Compare a8 b8 $$ Compare a9 b9 $$ Compare a10 b10

  Compare a b = CompareUser a b

-- | Compare two types, of any kinds, which are not compared within `Compare`. Users can add instances.
type family CompareUser (a :: k) (b :: k') :: Ordering

type family OrdCase (o :: Ordering) (x :: l1) (y :: l2) (z :: l3) :: l where
  OrdCase LT x _' _'' = x
  OrdCase EQ _' y _'' = y
  OrdCase GT _' _'' z = z

type family CompareCase (a :: k) (b :: k') (x :: l1) (y :: l2) (z :: l3) :: l where
  CompareCase a b x y z = OrdCase (Compare a b) x y z

type family (a :: k) <! (b :: k') :: Bool where
  a <! b = CompareCase a b True False False
type family (a :: k) >=! (b :: k') :: Bool where
  a >=! b = CompareCase a b False True True
type family (a :: k) >! (b :: k') :: Bool where
  a >! b = CompareCase a b False False True
type family (a :: k) <=! (b :: k') :: Bool where
  a <=! b = CompareCase a b True True False
infixl 4 <!, >=!, >!, <=!

type family Max (a :: k1) (b :: k2) :: k where
  Max a b = CompareCase a b b b a
type family Min (a :: k1) (b :: k2) :: k where
  Min a b = CompareCase a b a a b
