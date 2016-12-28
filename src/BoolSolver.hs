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
  consistentHelper an (Var n) = M.lookup n an
  consistentHelper an (Not t1) = fmap not (consistentHelper an t1)
  consistentHelper an (Or t1 t2) = Just $ consistent an t1 || consistent an t2
  consistentHelper an (And t1 t2) = Just $ consistent an t1 && consistent an t2

getVars :: (Ord a) => Term a -> [a]
getVars t = nub $ f t where
  f (Var s) = [s]
  f (And t1 t2) = f t1 ++ f t2
  f (Or t1 t2) = f t1 ++ f t2
  f (Not t1) = f t1

nextGuess :: (Ord a) => Assignment a -> a -> [a] -> Term a -> Maybe (Assignment a)
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

createAssignment :: (Ord a) => Term a -> Maybe (Assignment a)
createAssignment t = nextSearchStep M.empty (headMay vars) (tail vars) t where
  vars = getVars t

truths :: Assignment a -> Assignment a
truths = M.filter id
