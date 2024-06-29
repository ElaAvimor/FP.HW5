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

-- Section 3: Calculator and traverse
class Monad f => CalculatorError f where
  divideByZero :: f Int
  missingVariable :: String -> f Int

runCalculator :: CalculatorError f => Map String Int -> Expr -> f Int
runCalculator vars = \case
  Val x -> pure x
  Var x -> maybe (missingVariable x) pure (vars !? x)
  Add x y -> liftA2 (+) (runCalculator vars x) (runCalculator vars y)
  Sub x y -> liftA2 (-) (runCalculator vars x) (runCalculator vars y)
  Mul x y -> liftA2 (*) (runCalculator vars x) (runCalculator vars y)
  Div x y -> do
    y' <- runCalculator vars y
    if y' == 0 then divideByZero else liftA2 div (runCalculator vars x) (pure y')

-- Instances to implement:
instance CalculatorError Maybe
  where
    divideByZero = Nothing
    missingVariable _ = Nothing

data Err = DivByZero | MissingVar String deriving (Show, Eq)
instance CalculatorError (Either Err)
  where
    divideByZero = Left DivByZero
    missingVariable = Left . MissingVar

data Defaults
  = Defaults
  -- This replaces the entire division result, not just the denominator!
  { defaultForDivisionByZero :: Int
  , defaultForVariable :: String -> Int
  }
instance CalculatorError (Reader Defaults)
  where
    divideByZero = Reader $ \defaults -> defaultForDivisionByZero defaults
    missingVariable x = Reader $ \defaults -> defaultForVariable defaults x

-- -- From the lectures:
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

-- -- Section 4: Hangman
hangman :: String -> IO Int
hangman word = do
  let wordSet = removeSpacesFromSet (makeTheSetLower (S.fromList word))
  -- let wordLength = length word
  let initialDisplay = initialDisplayWithSpaces word
  let initialGameState = GameState word wordSet initialDisplay "" (getTheLengthOftheSet wordSet) 0 False
  playGame initialGameState

playGame :: GameState -> IO Int
playGame gameState = do
  putStrLn $ display gameState
  let promptMessage = if lastGuessCorrect gameState then "Try again: " else "Guess a letter: "
  putStr promptMessage
  guess <- getChar
  _ <- getLine  -- consume the newline character
  if not (isLetter guess)
    then do
      putStrLn $ "Invalid letter guess " ++ [guess] ++ "!"
      playGame gameState
    else do
      let previousWrongGuesses = wrongGuesses gameState
      let newGameState = updateGameState gameState (toLower guess)
      let currentWrongGuesses = wrongGuesses newGameState
      if currentWrongGuesses > previousWrongGuesses
        then putStrLn "Wrong guess!"
        else pure ()
      if isWin newGameState
        then do
          putStrLn "Very good, the word is:"
          putStrLn $ word newGameState
          pure $ calculateScore newGameState
        else playGame newGameState

updateGameState :: GameState -> Char -> GameState
updateGameState gameState guess =
  let newGuesses = if guess `elem` guesses gameState then guesses gameState else guess : guesses gameState
      newDisplay = updateDisplay (word gameState) (display gameState) (toLower guess)
      isWrongGuess = not (guess `elem` wordSet gameState)
      newWrongGuesses = if isWrongGuess then 1 else 0
  in gameState {display = newDisplay, guesses = newGuesses, wrongGuesses = wrongGuesses gameState + newWrongGuesses, lastGuessCorrect = isWrongGuess}

updateDisplay :: String -> String -> Char -> String
updateDisplay [] _ _ = []
updateDisplay _ [] _ = []
updateDisplay (w:ws) (d:ds) guess
  | w == ' ' = ' ' : updateDisplay ws ds guess
  | toLower w == guess = w : updateDisplay ws ds guess
  | otherwise = d : updateDisplay ws ds guess


isGameOver :: GameState -> Bool
isGameOver = isWin

isWin :: GameState -> Bool
isWin gameState = all (`elem` guesses gameState) (S.toList (wordSet gameState))

calculateScore :: GameState -> Int
calculateScore gameState = max 0 (calculateTotalGuesses gameState - maxGuesses gameState)

calculateTotalGuesses :: GameState -> Int
calculateTotalGuesses gameState = maxGuesses gameState + wrongGuesses gameState

isLetter :: Char -> Bool
isLetter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

nub :: Eq a => [a] -> [a]
nub = nubBy (==)

nubBy :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq = foldl' (\seen x -> if any (eq x) seen then seen else seen ++ [x]) []

toLower :: Char -> Char
toLower c
  | c >= 'A' && c <= 'Z' = toEnum (fromEnum c + 32)
  | otherwise = c

makeTheSetLower :: Set Char -> Set Char
makeTheSetLower = S.fromList . map toLower . S.toList

getTheLengthOftheSet :: Set Char -> Int
getTheLengthOftheSet = length . S.toList

removeSpacesFromSet :: Set Char -> Set Char
removeSpacesFromSet = S.filter (/= ' ')

initialDisplayWithSpaces :: String -> String
initialDisplayWithSpaces = map (\c -> if c == ' ' then ' ' else '_')


data GameState = GameState
  { word :: String
  , wordSet :: Set Char
  , display :: String
  , guesses :: String
  , maxGuesses :: Int
  , wrongGuesses :: Int
  , lastGuessCorrect :: Bool
  }
  deriving (Show, Eq)
