{-# LANGUAGE LambdaCase #-}
-- Implement the following functions.
-- When you're done, ghc -Wall -Werror Deque.hs HW5.hs
-- Tells HLS to show warnings, and the file won't be compiled if there are any warnings, e.g.,
-- eval (-- >>>) won't work.
{-# OPTIONS_GHC -Wall -Werror #-}
-- Refines the above, allowing for unused imports.
{-# OPTIONS_GHC -Wno-unused-imports #-}

module HW5 where

import Control.Applicative (liftA2)
import Data.Char (ord)
import Data.Either
import Data.List (foldl', uncons)
import Data.Map (Map, (!?))
import Data.Map qualified as M
import Data.Maybe
import Data.Monoid (All (..), Any (..), First (..), Last (..), Product (..), Sum (..))
import Data.Ord (Down (..))
import Data.Semigroup (Arg (..), Max (..), Min (..))
import Data.Set (Set)
import Data.Set qualified as S
import Deque (Deque)
import Deque qualified as DQ

data FoldMapFunc a m result = FoldMapFunc {agg :: a -> m, finalize :: m -> result}

foldMap' :: (Foldable t, Monoid m) => FoldMapFunc a m result -> t a -> result
foldMap' FoldMapFunc{agg, finalize} = finalize . foldMap agg

-- Section 1: Foldable functions
fmsum :: Num a => FoldMapFunc a (Sum a) a
fmsum = FoldMapFunc Sum getSum

fmor :: FoldMapFunc Bool Any Bool
fmor = FoldMapFunc Any getAny

fmfold :: Monoid a => FoldMapFunc a a a
fmfold = FoldMapFunc id id

fmelem :: Eq a => a -> FoldMapFunc a Any Bool
fmelem x = FoldMapFunc (\y -> Any (y == x)) getAny

fmfind :: (a -> Bool) -> FoldMapFunc a (First a) (Maybe a)
fmfind p = FoldMapFunc (\x -> First (if p x then Just x else Nothing)) getFirst

fmlength :: FoldMapFunc a (Sum Int) Int
fmlength = FoldMapFunc (const (Sum 1)) getSum

fmnull :: FoldMapFunc a All Bool
fmnull = FoldMapFunc (const (All False)) getAll

fmmaximum :: Ord a => FoldMapFunc a (Maybe (Max a)) (Maybe a)
fmmaximum = FoldMapFunc (Just . Max) getMaxMaybe
  where
    getMaxMaybe :: Maybe (Max a) -> Maybe a
    getMaxMaybe = fmap getMax

fmminimum :: Ord a => FoldMapFunc a (Maybe (Min a)) (Maybe a)
fmminimum = FoldMapFunc (Just . Min) getMinMaybe
      where
        getMinMaybe :: Maybe (Min a) -> Maybe a
        getMinMaybe = fmap getMin

fmmaxBy :: Ord b => (a -> b) -> FoldMapFunc a (Maybe (Max (Arg b a))) (Maybe a)
fmmaxBy f = FoldMapFunc (Just . Max . (\x -> Arg (f x) x)) getMaxByMaybe
          where
            getMaxByMaybe :: Maybe (Max (Arg b a)) -> Maybe a
            getMaxByMaybe = fmap (\(Max (Arg _ a)) -> a)
fmminBy :: Ord b => (a -> b) -> FoldMapFunc a (Maybe (Min (Arg b a))) (Maybe a)
fmminBy f = FoldMapFunc (Just . Min . (\x -> Arg (f x) x)) getMinByMaybe
              where
                getMinByMaybe :: Maybe (Min (Arg b a)) -> Maybe a
                getMinByMaybe = fmap (\(Min (Arg _ a)) -> a)

fmtoList :: FoldMapFunc a [a] [a]
fmtoList = FoldMapFunc (: []) id

-- -- Section 2: Deque instances (Don't forget to implement the instances in Deque.hs as well!)
-- newtype DequeWrapper a = DequeWrapper (Deque a) deriving (Show, Eq)
-- instance Semigroup (DequeWrapper a)
-- instance Monoid (DequeWrapper a)
-- instance Foldable DequeWrapper
-- instance Functor DequeWrapper
-- instance Applicative DequeWrapper
-- instance Monad DequeWrapper

-- -- Section 3: Calculator and traverse
-- class Monad f => CalculatorError f where
--   divideByZero :: f Int
--   missingVariable :: String -> f Int

-- runCalculator :: CalculatorError f => Map String Int -> Expr -> f Int

-- -- Instances to implement:
-- instance CalculatorError Maybe

-- data Err = DivByZero | MissingVar String deriving (Show, Eq)
-- instance CalculatorError (Either Err)

-- data Defaults
--   = Defaults
--   -- This replaces the entire division result, not just the denominator!
--   { defaultForDivisionByZero :: Int
--   , defaultForVariable :: String -> Int
--   }
-- instance CalculatorError (Reader Defaults)

-- -- From the lectures:
-- newtype Reader r a = Reader {runReader :: r -> a}
-- instance Functor (Reader r) where
--   fmap f r = Reader $ f . runReader r
-- instance Applicative (Reader r) where
--   pure = Reader . const
--   liftA2 f ra rb = Reader $ \r -> f (runReader ra r) (runReader rb r)
-- instance Monad (Reader r) where
--   ra >>= f = Reader $ \r -> runReader (f $ runReader ra r) r

-- data Expr
--   = Val Int
--   | Var String
--   | Add Expr Expr
--   | Sub Expr Expr
--   | Mul Expr Expr
--   | Div Expr Expr
--   deriving (Show, Eq)

-- -- Section 4: Hangman
-- hangman :: String -> IO Int
