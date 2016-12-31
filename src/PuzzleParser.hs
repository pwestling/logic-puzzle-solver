module PuzzleParser where

import           BoolExpressions
import           Data.Either
import           Data.List
import           Data.Maybe
import           Debug.Trace
import           LogicPuzzleSolver
import           Text.Parsec

instance Monoid Puzzle where
  mempty = Puzzle [] []
  mappend (Puzzle classes1 rules1) (Puzzle classes2 rules2) = Puzzle (classes1 ++ classes2) (rules1 ++ rules2)

puzzleStr :: Parsec String (Class,[Class]) Puzzle
puzzleStr = mconcat <$> line `sepBy` char ';'

line :: Parsec String (Class,[Class]) Puzzle
line = try pClass <|> rule

anything :: Parsec String (Class,[Class]) String
anything = many1 (noneOf ";" <|> space)

var = do
  spaces
  s <- many1 $ letter <|> digit <|> oneOf ".$"
  (_,classes) <- getState
  spaces
  let contained = s `elem` concat classes
  if contained
    then
      return s
    else
      unexpected $ "Parsed var " ++ s ++ " is not a member of any class. Var must be declared before use."

rule :: Parsec String (Class,[Class]) Puzzle
rule = try eitherRule <|> try pairMatchRule <|> try isNotRule <|> try isRule <|> try disjointRule
        <|> try lessThanRule <|> try greaterThanRule

eitherRule = do
  v1 <- var
  string "is either"
  v2 <- var
  string "or"
  v3 <- var
  return $ Puzzle [] [v1 `isOneOf` v2 $ v3]

pairMatchRule = do
  v1 <- var
  v2 <- var
  string "match to"
  v3 <- var
  v4 <- var
  return $ Puzzle [] [[v1,v2] `matchTo` [v3,v4]]

isRule = do
  v1 <- var
  string "is"
  v2 <- var
  return $ Puzzle [] [v1 `is` v2]

isNotRule = do
  v1 <- var
  string "is not"
  v2 <- var
  return $ Puzzle [] [v1 `isNot` v2]

disjointRule = do
  spaces
  string "disjoint"
  vars <- many1 var
  return $ Puzzle [] [allDisjointRule vars]

comparisonRule symbol word fn stepFn = do
  var1 <- var
  string symbol <|> string word
  var2 <- var
  numStr <- optionMaybe (string "by" >> spaces >> many1 digit)
  let num = read <$> numStr
  (numClass,otherClasses) <- getState
  let x = seq (trace $ show numClass) 0
  let term = maybe (fn var1 var2  numClass) (stepFn var1 var2 numClass) num
  return $ Puzzle [] [term]

lessThanRule = comparisonRule "<" "less than" lessThan nLessThan
greaterThanRule = comparisonRule ">" "greater than" greaterThan nGreaterThan

pClass :: Parsec String (Class,[Class]) Puzzle
pClass = do
  spaces
  string "class"
  spaces
  num <- optionMaybe (string "numeric" >> spaces)
  names <- many1 (noneOf " ;") `sepBy` spaces
  (numClass, otherClasses) <- getState
  let newState = if isJust num then (names, names : otherClasses) else (numClass, names : otherClasses)
  if not (null otherClasses) && length (head otherClasses) /= length names
    then
      unexpected $ "All classes must be the same length: Mismatch on " ++ show names ++" and " ++ show (head otherClasses)
    else
      putState newState
  return $ Puzzle [names] []


pz =  runParser puzzleStr ([],[]) "" "class numeric 4 5 6 7 8 9 10; class bask comp frui rare teas tele toas; class brad chris eve harry neil pablo zach; class appl bing font lake matt oakd urba; frui < comp by 3; tele is either lake or 7; neil > chris; rare is not urba; frui is not urba; chris > harry by 1; bask is either 8 or appl; bing is not eve; pablo 4 match to frui matt; 8 is not oakd; neil < brad by 3; comp 10 match to brad bing; oakd is not neil; toas is not brad; teas is not neil; toas is not neil; disjoint font 8 teas toas 9 rare 5"

k (Right pz ) = solveAndPrint pz

l = k pz
