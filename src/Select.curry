------------------------------------------------------------------------
--- This library provides some useful operations to select components
--- in AbstractCurry programs, i.e., it provides a collection of
--- selector functions for AbstractCurry.
---
--- @version May 2016
--- @category meta
------------------------------------------------------------------------

module Select
  ( progName, imports, functions, constructors, types, publicFuncNames
  , publicConsNames, publicTypeNames

  , typeName, typeVis, typeCons
  , consName, consVis
  , isBaseType, isPolyType, isFunctionalType, isIOType, isIOReturnType
  , argTypes, resultType, tvarsOfType, tconsOfType, modsOfType

  , funcName, funcArity, funcComment, funcVis, funcType, funcRules
  , ruleRHS

  , varsOfPat, varsOfExp, varsOfFDecl, varsOfRule

  , isPrelude
  ) where

import FlatCurry.Types
import AbstractCurry.Types(pre)
import List(union)

------------------------------------------------------------------------
-- Selectors for curry programs

-- Returns the name of a given Curry program.
progName :: Prog -> String
progName (Prog modname _ _ _ _) = modname

--- Returns the imports (module names) of a given Curry program.
imports :: Prog -> [String]
imports (Prog _ ms _ _ _) = ms

--- Returns the function declarations of a given Curry program.
functions :: Prog -> [FuncDecl]
functions (Prog _ _ _ fs _) = fs

--- Returns all constructors of given Curry program.
constructors :: Prog -> [ConsDecl]
constructors = concatMap typeCons . types

--- Returns the type declarations of a given Curry program.
types :: Prog -> [TypeDecl]
types (Prog _ _ ts _ _) = ts

--- Returns the names of all visible functions in given Curry program.
publicFuncNames :: Prog -> [QName]
publicFuncNames = map funcName . filter ((== Public) . funcVis) . functions

--- Returns the names of all visible constructors in given Curry program.
publicConsNames :: Prog -> [QName]
publicConsNames = map consName
                . filter ((== Public) . consVis)
                . constructors

--- Returns the names of all visible types in given Curry program.
publicTypeNames :: Prog -> [QName]
publicTypeNames = map typeName . filter ((== Public) . typeVis) . types

------------------------------------------------------------------------
-- Selectors for type expressions

--- Returns the name of a given type declaration
typeName :: TypeDecl -> QName
typeName (Type    n _ _ _) = n
typeName (TypeSyn n _ _ _) = n

--- Returns the visibility of a given type declaration
typeVis :: TypeDecl -> Visibility
typeVis (Type    _ vis _ _) = vis
typeVis (TypeSyn _ vis _ _) = vis

--- Returns the constructors of a given type declaration.
typeCons :: TypeDecl -> [ConsDecl]
typeCons (Type    _ _ _ cs) = cs
typeCons (TypeSyn _ _ _ _ ) = []

--- Returns the name of a given constructor declaration.
consName :: ConsDecl -> QName
consName (Cons n _ _ _) = n

--- Returns the visibility of a given constructor declaration.
consVis :: ConsDecl -> Visibility
consVis (Cons _ _ vis _) = vis

--- Returns true if the type expression is a base type.
isBaseType :: TypeExpr -> Bool
isBaseType texp = case texp of
  TCons _ args -> null args
  _             -> False

--- Returns true if the type expression contains type variables.
isPolyType :: TypeExpr -> Bool
isPolyType (TVar                _) = True
isPolyType (FuncType domain range) = isPolyType domain || isPolyType range
isPolyType (TCons      _ typelist) = any isPolyType typelist

--- Returns true if the type expression is a functional type.
isFunctionalType :: TypeExpr -> Bool
isFunctionalType texp = case texp of
  FuncType _ _ -> True
  _            -> False

--- Returns true if the type expression is (IO t).
isIOType :: TypeExpr -> Bool
isIOType texp = case texp of
  TCons tc _ -> tc == pre "IO"
  _           -> False

--- Returns true if the type expression is (IO t) with t/=() and
--- t is not functional
isIOReturnType :: TypeExpr -> Bool
isIOReturnType (TVar            _) = False
isIOReturnType (FuncType      _ _) = False
isIOReturnType (TCons tc typelist) =
  tc==pre "IO" && head typelist /= TCons (pre "()") []
  && not (isFunctionalType (head typelist))

--- Returns all argument types from a functional type
argTypes :: TypeExpr -> [TypeExpr]
argTypes (TVar         _) = []
argTypes (TCons      _ _) = []
argTypes (FuncType t1 t2) = t1 : argTypes t2

--- Return the result type from a (nested) functional type
resultType :: TypeExpr -> TypeExpr
resultType (TVar          n) = TVar n
resultType (TCons name args) = TCons name args
resultType (FuncType   _ t2) = resultType t2

--- Returns all type variables occurring in a type expression.
tvarsOfType :: TypeExpr -> [TVarIndex]
tvarsOfType (TVar         v) = [v]
tvarsOfType (FuncType t1 t2) = tvarsOfType t1 ++ tvarsOfType t2
tvarsOfType (TCons   _ args) = concatMap tvarsOfType args

--- Returns all type constructors used in the given type.
tconsOfType :: TypeExpr -> [QName]
tconsOfType (TVar         _) = []
tconsOfType (FuncType t1 t2) = tconsOfType t1 `union` tconsOfType t2
tconsOfType (TCons tc tys)   = foldr union [tc] $ map tconsOfType tys

--- Returns all modules used in the given type.
modsOfType :: TypeExpr -> [String]
modsOfType = map fst . tconsOfType

------------------------------------------------------------------------
-- Selectors for function definitions

--- Returns the name of a given function declaration.
funcName :: FuncDecl -> QName
funcName (Func n _ _ _ _) = n

--- Returns the arity of a given function declaration.
funcArity :: FuncDecl -> Int
funcArity (Func _ a _ _ _) = a

--- Returns the documentation comment of a given function declaration.
funcComment :: FuncDecl -> String
funcComment (Func _ _ _ _ _) = ""

--- Returns the visibility of a given function declaration.
funcVis :: FuncDecl -> Visibility
funcVis (Func _ _ vis _ _) = vis

--- Returns the type of a given function declaration.
funcType :: FuncDecl -> TypeExpr
funcType (Func _ _ _ texp _) = texp

--- Returns the rule of a given function declaration.
funcRules :: FuncDecl -> Rule
funcRules (Func _ _ _ _ rule) = rule

------------------------------------------------------------------------
-- Selectors for rules.

--- Returns the right-hand side of a rule.
ruleRHS :: Rule -> Maybe Expr
ruleRHS (Rule _ rhs) = Just rhs
ruleRHS (External _) = Nothing

------------------------------------------------------------------------
-- Operations to compute the variables occurring in a pattern or expression:

--- Returns list of all variables occurring in a pattern.
--- Each occurrence corresponds to one element, i.e., the list might
--- contain multiple elements.
varsOfPat :: Pattern -> [VarIndex]
varsOfPat (Pattern _ vs) = vs
varsOfPat (LPattern   _) = []

--- Returns list of all variables occurring in an expression.
--- Each occurrence corresponds to one element, i.e., the list might
--- contain multiple elements.
varsOfExp :: Expr -> [VarIndex]
varsOfExp (Var              v) = [v]
varsOfExp (Lit              _) = []
varsOfExp (Comb      _ _ exps) = concatMap varsOfExp exps
varsOfExp (Let     vbinds exp) =
  concatMap (\(v,e) -> v : varsOfExp e) vbinds ++ varsOfExp exp
varsOfExp (Free        vs exp) = vs ++ varsOfExp exp
varsOfExp (Or           e1 e2) = varsOfExp e1 ++ varsOfExp e2
varsOfExp (Case _ ce branches) =
  varsOfExp ce ++ concatMap (\(Branch p e) -> varsOfPat p ++ varsOfExp e) branches
varsOfExp (Typed te _)       = varsOfExp te

--- Returns list of all variables occurring in a function declaration.
--- Each occurrence corresponds to one element, i.e., the list might
--- contain multiple elements.
varsOfFDecl :: FuncDecl -> [VarIndex]
varsOfFDecl (Func _ _ _ _ r) = varsOfRule r

--- Returns list of all variables occurring in a rule.
--- Each occurrence corresponds to one element, i.e., the list might
--- contain multiple elements.
varsOfRule :: Rule -> [VarIndex]
varsOfRule (Rule vs exp) = vs ++ varsOfExp exp
varsOfRule (External    _) = []

------------------------------------------------------------------------
-- Operations to compute the function names declared in functions:

--- @return The declared function name of given function declaration in a list.
funcNamesOfFDecl :: FuncDecl -> [QName]
funcNamesOfFDecl (Func qn _ _ _ _) = [qn]

------------------------------------------------------------------------
--- Tests whether a module name is the prelude.
isPrelude :: String -> Bool
isPrelude m = m == "Prelude"

------------------------------------------------------------------------
