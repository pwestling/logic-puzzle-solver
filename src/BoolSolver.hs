{-# LANGUAGE OverloadedStrings #-}

module BoolSolver
    (
      Assignment,
      consistent,
      getVars,
      createAssignment
    ) where

import           Data.List       as L
import           Data.Map.Strict as M
import           Data.Maybe
import           Safe            as S

import           BoolExpressions

type Assignment = M.Map Name Bool

consistent :: Assignment -> Term -> Bool
consistent a t = fromMaybe True (consistentHelper a t) where
  consistentHelper a (Var n) = M.lookup n a
  consistentHelper a (Not t) = fmap not (consistentHelper a t)
  consistentHelper a (Or t1 t2) = Just $ consistent a t1 || consistent a t2
  consistentHelper a (And t1 t2) = Just $ consistent a t1 && consistent a t2

getVars :: Term -> [Name]
getVars t = nub $ f t where
  f (Var s) = [s]
  f (And t1 t2) = f t1 ++ f t2
  f (Or t1 t2) = f t1 ++ f t2
  f (Not t) = f t

nextGuess :: Assignment -> Name -> [Name] -> Term -> Maybe Assignment
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

nextSearchStep :: Assignment -> Maybe Name -> [Name] -> Term -> Maybe Assignment
nextSearchStep currAssign currVar nextVars term
  | isConsistent && isNothing currVar = Just currAssign -- Success Here
  | isConsistent && isJust guess = guess -- Success at a deeper level
  | otherwise = Nothing -- Go back
  where
    isConsistent = consistent currAssign term
    curVarVal = fromMaybe (error "Should only eval if there's a next term") currVar
    guess = nextGuess currAssign curVarVal nextVars term

createAssignment :: Term -> Maybe Assignment
createAssignment t = nextSearchStep M.empty (headMay vars) (tail vars) t where
  vars = getVars t

type Class = [Name]
