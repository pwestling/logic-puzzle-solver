{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module BoolSolver where

import           Data.List       as L
import           Data.Map.Strict as M
import           Data.Maybe
import           Safe            as S

import           BoolExpressions

type Assignment a = M.Map a Bool

consistent :: Assignment a -> Term a -> Bool
consistent a t = fromMaybe True (consistentHelper a t) where
  consistentHelper a (Var n) = M.lookup n a
  consistentHelper a (Not t) = fmap not (consistentHelper a t)
  consistentHelper a (Or t1 t2) = Just $ consistent a t1 || consistent a t2
  consistentHelper a (And t1 t2) = Just $ consistent a t1 && consistent a t2

getVars :: (Eq a, Ord a) => Term a -> [a]
getVars t = nub $ f t where
  f (Var s) = [s]
  f (And t1 t2) = f t1 ++ f t2
  f (Or t1 t2) = f t1 ++ f t2
  f (Not t) = f t

nextGuess :: (Eq a, Ord a) => Assignment a -> a -> [a] -> Term a -> Maybe (Assignment a)
nextGuess assign curr others term
  | isJust trueGuess = trueGuess
  | otherwise = falseGuess
  where
    next = headMay others
    remain = tail others
    trueGuess = nextSearchStep assignFalse next remain term
    falseGuess = nextSearchStep assignTrue next remain term
    assignFalse = M.insert curr False assign
    assignTrue = M.insert curr True assign

nextSearchStep :: (Eq a, Ord a) => Assignment a -> Maybe a -> [a] -> Term a -> Maybe (Assignment a)
nextSearchStep currAssign currVar nextVars term
  | isConsistent && isNothing currVar = Just currAssign -- Success Here
  | isConsistent && isJust guess = guess -- Success at a deeper level
  | otherwise = Nothing -- Go back
  where
    isConsistent = consistent currAssign term
    curVarVal = fromMaybe (error "Should only eval if there's a next term") currVar
    guess = nextGuess currAssign curVarVal nextVars term

createAssignment :: (Eq a, Ord a) => Term a -> Maybe (Assignment a)
createAssignment t = nextSearchStep M.empty (headMay vars) (tail vars) t where
  vars = getVars t

singlePairExclusive :: (Ord a) => [a] -> [a] -> a -> a -> Term (a, a)
singlePairExclusive c1 c2 el1 el2 = ands $ Var truePair : falseVars
  where
    truePair = (el1,el2)
    isNotTruePair = not . (==) truePair
    falsePairs = L.filter isNotTruePair $ L.map (el1,) c2 ++ L.map (,el2) c1
    falseVars = nots $ L.map Var falsePairs

optionsForVar :: Ord a => [a] -> [a] -> a -> Term (a, a)
optionsForVar c1 c2 el1 = ors $ L.map (singlePairExclusive c1 c2 el1) c2

oneToOnePairing :: (Ord a) => [a] -> [a] -> Term (a,a)
oneToOnePairing n1 n2 = ands $ L.map (optionsForVar n1 n2) n1

joinConstraint :: Ord t => t -> t -> t -> Term (t, t)
joinConstraint a b c = ors [ands [Var (a,b), Var (b,c), Var (a,c)],
                            ands [notvar (a,b), notvar (b,c), notvar (a,c)],
                            ands [notvar (a,b), notvar (b,c), Var (a,c)],
                            ands [Var (a,b), notvar (b,c), notvar (a,c)],
                            ands [notvar (a,b), Var (b,c), notvar (a,c)]]

allJoinConstraints :: (Ord a) => [[a]] -> Term (a,a)
allJoinConstraints classes
  | L.length classes > 2 = ands $ L.map joins setsOfThree
    where
      setsOfThree = L.filter ((== 3).length) $ subsequences classes
      joins [a,b,c] = ands $ joinConstraint <$> a <*> b <*> c

allPairingConstraints :: (Ord a) => [[a]] -> Term (a,a)
allPairingConstraints classes = ands $ L.map oto classPairs
  where
    classPairs = L.filter ((== 2).length) $ subsequences classes
    oto [a,b] = oneToOnePairing a b

truths :: Assignment a -> Assignment a
truths = M.filter id

--nLessThan :: Integer -> a -> a -> [a] -> Term (a,a)
--nLessThan n el1 el2 (c:cs) = Or (And )

data Puzzle = Puzzle [[String]] [Term (String,String)]

solve :: Puzzle -> Maybe (Assignment (String,String))
solve (Puzzle classes rules) = truths <$> createAssignment (ands $ [allPairingConstraints classes, allJoinConstraints classes] ++ rules)
