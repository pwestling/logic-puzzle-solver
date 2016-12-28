{-# LANGUAGE OverloadedStrings #-}

module LogicPuzzleSolver where

import           BoolExpressions
import           BoolSolver
import           Data.List       as L

data Pair a = Pair a a deriving (Eq,Ord)
data Puzzle = Puzzle [Class] [Term (Pair ClassMember)]

type Class = [ClassMember]
type ClassMember = String

instance (Show a) => Show (Pair a) where
  show (Pair a b) = show a ++ "=" ++ show b

pair :: Ord a => a -> a -> Pair a
pair a1 a2
  | a1 <= a2 = Pair a1 a2
  | otherwise = Pair a2 a1

singlePairExclusive :: (Ord a) => [a] -> [a] -> a -> a -> Term (Pair a)
singlePairExclusive c1 c2 el1 el2 = ands $ Var truePair : falseVars
  where
    truePair = pair el1 el2
    isNotTruePair = not . (==) truePair
    falsePairs = L.filter isNotTruePair $ L.map (pair el1) c2 ++ L.map (pair el2) c1
    falseVars = nots $ L.map Var falsePairs

optionsForVar :: Ord a => [a] -> [a] -> a -> Term (Pair a)
optionsForVar c1 c2 el1 = ors $ L.map (singlePairExclusive c1 c2 el1) c2

oneToOnePairing :: (Ord a) => [a] -> [a] -> Term (Pair a)
oneToOnePairing n1 n2 = ands $ L.map (optionsForVar n1 n2) n1

joinConstraint :: Ord a => a -> a -> a -> Term (Pair a)
joinConstraint a b c = ors [ands [Var (pair a b), Var (pair b c), Var (pair a c)],
                            ands [notvar (pair a b), notvar (pair b c), notvar (pair a c)],
                            ands [notvar (pair a b), notvar (pair b c), Var (pair a c)],
                            ands [Var (pair a b), notvar (pair b c), notvar (pair a c)],
                            ands [notvar (pair a b), Var (pair b c), notvar (pair a c)]]

allJoinConstraints :: (Ord a) => [[a]] -> Term (Pair a)
allJoinConstraints classes
  | L.length classes > 2 = ands $ L.map joins setsOfThree
    where
      setsOfThree = L.filter ((== 3).length) $ subsequences classes
      joins [a,b,c] = ands $ joinConstraint <$> a <*> b <*> c

allPairingConstraints :: (Ord a) => [[a]] -> Term (Pair a)
allPairingConstraints classes = ands $ L.map oto classPairs
  where
    classPairs = L.filter ((== 2).length) $ subsequences classes
    oto [a,b] = oneToOnePairing a b

solve :: Puzzle -> Maybe (Assignment (Pair ClassMember))
solve (Puzzle classes rules) = truths <$> createAssignment (ands $ [allPairingConstraints classes, allJoinConstraints classes] ++ rules)

nLessThan :: (Ord a) => a -> a -> [a] -> Int -> Term (Pair a)
nLessThan a b cs n = nLessThanHelper a b cs (drop n cs) where
  nLessThanHelper el1 el2 (v1:_) [v2] = And (Var (pair el1 v1)) (Var (pair el2 v2))
  nLessThanHelper el1 el2 (v1:el1Vals) (v2:el2Vals) =
    Or (And (Var (pair el1 v1)) (Var (pair el2 v2))) (nLessThanHelper el1 el2 el1Vals el2Vals)

lessThan :: Ord a => a -> a -> [a] -> Term (Pair a)
lessThan a b cs = ors $ L.map (nLessThan a b cs) [1..(length cs - 1)]

greaterThan :: Ord a => a -> a -> [a] -> Term (Pair a)
greaterThan a b = lessThan b a

nGreaterThan :: Ord a => a -> a -> [a] -> Int -> Term (Pair a)
nGreaterThan a b = nLessThan b a

isOneOf :: Ord a => a -> [a] -> Term (Pair a)
isOneOf a [b] = Var (pair a b)
isOneOf a (b:bs) = xor (Var (pair a b)) (isOneOf a bs)

allDisjointRule :: (Ord a) => [a] -> Term (Pair a)
allDisjointRule [a1,a2] = notvar (pair a1 a2)
allDisjointRule (a:as) = And (ands $ map (notvar.pair a) as) (allDisjointRule as)

matchTo :: (Ord a) => [a] -> [a] -> Term (Pair a)
matchTo [a1,a2] [b1,b2] = ands [Or (mkAnd (pair a1 b1) (pair a2 b2)) (mkAnd (pair a1 b2) (pair a2 b1)),
                                      notvar $ pair a1 a2,
                                      notvar $ pair b1 b2]
matchTo _ _ = error "matchTo only works on a pair of pairs"

is :: (Ord a) => a -> a -> Term (Pair a)
is a b = Var $ pair a b

isNot :: (Ord a) => a -> a -> Term (Pair a)
isNot a b = notvar $ pair a b
