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
fmsum :: Num a => FoldMapFunc a _ a
fmor :: FoldMapFunc Bool _ Bool
fmfold :: Monoid a => FoldMapFunc a _ a
fmelem :: Eq a => a -> FoldMapFunc a _ Bool
fmfind :: (a -> Bool) -> FoldMapFunc a _ (Maybe a)
fmlength :: FoldMapFunc a _ Int
fmnull :: FoldMapFunc a _ Bool
fmmaximum :: Ord a => FoldMapFunc a _ (Maybe a)
fmminimum :: Ord a => FoldMapFunc a _ (Maybe a)
fmmaxBy :: Ord b => (a -> b) -> FoldMapFunc a _ (Maybe a)
fmminBy :: Ord b => (a -> b) -> FoldMapFunc a _ (Maybe a)
fmtoList :: FoldMapFunc a _ [a]

-- Section 2: Deque instances (Don't forget to implement the instances in Deque.hs as well!)
newtype DequeWrapper a = DequeWrapper (Deque a) deriving (Show, Eq)
instance Semigroup (DequeWrapper a)
instance Monoid (DequeWrapper a)
instance Foldable DequeWrapper
instance Functor DequeWrapper
instance Applicative DequeWrapper
instance Monad DequeWrapper

-- Section 3: Calculator and traverse
class Monad f => CalculatorError f where
  divideByZero :: f Int
  missingVariable :: String -> f Int

runCalculator :: CalculatorError f => Map String Int -> Expr -> f Int

-- Instances to implement:
instance CalculatorError Maybe

data Err = DivByZero | MissingVar String deriving (Show, Eq)
instance CalculatorError (Either Err)

data Defaults
  = Defaults
  -- This replaces the entire division result, not just the denominator!
  { defaultForDivisionByZero :: Int
  , defaultForVariable :: String -> Int
  }
instance CalculatorError (Reader Defaults)

-- From the lectures:
newtype Reader r a = Reader {runReader :: r -> a}
instance Functor (Reader r) where
  fmap f r = Reader $ f . runReader r
instance Applicative (Reader r) where
  pure = Reader . const
  liftA2 f ra rb = Reader $ \r -> f (runReader ra r) (runReader rb r)
instance Monad (Reader r) where
  ra >>= f = Reader $ \r -> runReader (f $ runReader ra r) r

data Expr
  = Val Int
  | Var String
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | Div Expr Expr
  deriving (Show, Eq)

-- Section 4: Hangman
hangman :: String -> IO Int
