------------------------------------------------------------------------
--- This library provides some useful operations to write programs
--- that generate AbstractCurry programs in a more compact and readable way.
---
--- @version February 2016
--- @category meta
------------------------------------------------------------------------

module FlatCurry.Build where

import FlatCurry.Types
import AbstractCurry.Types (pre)

infixr 9 ~>

------------------------------------------------------------------------
-- Goodies to construct type expressions

--- A function type.
(~>) :: TypeExpr -> TypeExpr -> TypeExpr
t1 ~> t2 = FuncType t1 t2

--- A base type.
baseType :: QName -> TypeExpr
baseType t = TCons t []

--- Constructs a list type from an element type.
listType :: TypeExpr -> TypeExpr
listType a = TCons (pre "[]") [a]

--- Constructs a tuple type from list of component types.
tupleType :: [TypeExpr] -> TypeExpr
tupleType ts | l==0 = baseType (pre "()")
             | l==1 = head ts
             | otherwise = TCons (pre ('(' : take (l-1) (repeat ',') ++ ")"))
                                  ts
 where l = length ts

--- Constructs an IO type from a type.
ioType :: TypeExpr -> TypeExpr
ioType a = TCons (pre "IO") [a]

--- Constructs a Maybe type from element type.
maybeType :: TypeExpr -> TypeExpr
maybeType a = TCons (pre "Maybe") [a]

--- The type expression of the String type.
stringType :: TypeExpr
stringType = baseType (pre "String")

--- The type expression of the Int type.
intType :: TypeExpr
intType = baseType (pre "Int")

--- The type expression of the Float type.
floatType :: TypeExpr
floatType = baseType (pre "Float")

--- The type expression of the Bool type.
boolType :: TypeExpr
boolType = baseType (pre "Bool")

--- The type expression of the Char type.
charType :: TypeExpr
charType = baseType (pre "Char")

--- The type expression of the unit type.
unitType :: TypeExpr
unitType = baseType (pre "()")

--- The type expression of the Time.CalendarTime type.
dateType :: TypeExpr
dateType = baseType ("Time", "CalendarTime")

------------------------------------------------------------------------
-- Goodies to construct function declarations

--- Constructs a function declaration from a given qualified function name,
--- arity, visibility, type expression and list of defining rules.
cfunc :: QName -> Int -> CVisibility -> TypeExpr -> [CRule] -> CFuncDecl
cfunc = CFunc

--- Constructs a function declaration from a given comment,
--- qualified function name,
--- arity, visibility, type expression and list of defining rules.
cmtfunc :: String -> QName -> Int -> CVisibility -> TypeExpr -> [CRule]
        -> CFuncDecl
cmtfunc = CmtFunc

--- Constructs a simple rule with a pattern list and an
--- unconditional right-hand side.
simpleRule :: [CPattern] -> Expr -> CRule
simpleRule pats rhs = CRule pats (CSimpleRhs rhs [])

--- Constructs a simple rule with a pattern list, an
--- unconditional right-hand side, and local declarations.
simpleRuleWithLocals :: [CPattern] -> Expr -> [CLocalDecl] -> CRule
simpleRuleWithLocals pats rhs ldecls = CRule pats (CSimpleRhs rhs ldecls)

--- Constructs a rule with a possibly guarded right-hand side
--- and local declarations.
--- A simple right-hand side is constructed if there is only one
--- `True` condition.
guardedRule :: [CPattern] -> [(Expr,Expr)] -> [CLocalDecl] -> CRule
guardedRule pats gs ldecls
  | length gs == 1 && fst (head gs) == CSymbol (pre "True")
              = CRule pats (CSimpleRhs (snd (head gs)) ldecls)
  | otherwise = CRule pats (CGuardedRhs gs ldecls)

--- Constructs a guarded expression with the trivial guard.
noGuard :: Expr -> (Expr, Expr)
noGuard e = (CSymbol (pre "True"), e)

------------------------------------------------------------------------
-- Goodies to construct expressions and patterns

--- An application of a qualified function name to a list of arguments.
applyF :: QName -> [Expr] -> Expr
applyF f es = foldl CApply (CSymbol f) es 

--- An application of an expression to a list of arguments.
applyE :: Expr -> [Expr] -> Expr
applyE f args = foldl CApply f args

--- A constant, i.e., an application without arguments.
constF :: QName -> Expr
constF f = applyF f []

--- An application of a variable to a list of arguments.
applyV :: CVarIName -> [Expr] -> Expr
applyV v es = foldl CApply (CVar v) es 

-- Applies the Just constructor to an AbstractCurry expression.
applyJust :: Expr -> Expr
applyJust a = applyF (pre "Just") [a]

-- Applies the maybe function to three AbstractCurry expressions.
applyMaybe :: Expr -> Expr -> Expr -> Expr
applyMaybe a1 a2 a3 = applyF (pre "maybe") [a1,a2,a3]

--- Constructs a tuple expression from list of component expressions.
tupleExpr :: [Expr] -> Expr
tupleExpr es | l==0 = constF (pre "()")
             | l==1 = head es
             | otherwise = applyF (pre ('(' : take (l-1) (repeat ',') ++ ")"))
                                  es
 where l = length es

-- Constructs a let declaration (with possibly empty local delcarations).
letExpr :: [CLocalDecl] -> Expr -> Expr
letExpr locals cexp = if null locals then cexp else CLetDecl locals cexp

--- Constructs from a pattern and an expression a branch for a case expression.
cBranch :: CPattern -> Expr -> (CPattern, CRhs)
cBranch pattern exp = (pattern, CSimpleRhs exp [])

--- Constructs a tuple pattern from list of component patterns.
tuplePattern :: [CPattern] -> CPattern
tuplePattern ps
  | l==0 = CPComb (pre "()") []
  | l==1 = head ps
  | otherwise = CPComb (pre ('(' : take (l-1) (repeat ',') ++ ")")) ps
 where l = length ps

--- Constructs, for given n, a list of n PVars starting from 0.
pVars :: Int -> [CPattern]
pVars n = [CPVar (i,"x"++show i) | i<-[0..n-1]] 

--- Converts an integer into an AbstractCurry expression.
pInt :: Int -> CPattern
pInt x = CPLit (CIntc x)

--- Converts a float into an AbstractCurry expression.
pFloat :: Float -> CPattern
pFloat x = CPLit (CFloatc x)

--- Converts a character into a pattern.
pChar :: Char -> CPattern
pChar x = CPLit (CCharc x)

--- Constructs an empty list pattern.
pNil :: CPattern
pNil = CPComb (pre "[]") []

--- Constructs a list pattern from list of component patterns.
listPattern :: [CPattern] -> CPattern
listPattern []     = pNil
listPattern (p:ps) = CPComb (pre ":") [p, listPattern ps]

--- Converts a string into a pattern representing this string.
stringPattern :: String -> CPattern
stringPattern = CPLit . CStringc

--- Converts a list of AbstractCurry expressions into an
--- AbstractCurry representation of this list.
list2ac :: [Expr] -> Expr
list2ac []     = constF (pre "[]")
list2ac (c:cs) = applyF (pre ":") [c, list2ac cs]

--- Converts an integer into an AbstractCurry expression.
cInt :: Int -> Expr
cInt x = CLit (CIntc x)

--- Converts a float into an AbstractCurry expression.
cFloat :: Float -> Expr
cFloat x = CLit (CFloatc x)

--- Converts a character into an AbstractCurry expression.
cChar :: Char -> Expr
cChar x = CLit (CCharc x)

--- Converts a string into an AbstractCurry represention of this string.  
string2ac :: String -> Expr
string2ac s = CLit (CStringc s)

--- Converts an index i into a variable named xi.
toVar :: Int -> Expr
toVar i = CVar (1,"x"++show i)

--- Converts a string into a variable with index 1.
cvar :: String -> Expr
cvar s = CVar (1,s)

--- Converts a string into a pattern variable with index 1.
cpvar :: String -> CPattern
cpvar s = CPVar (1,s)

--- Converts a string into a type variable with index 1.
ctvar :: String -> TypeExpr
ctvar s = CTVar (1,s)

------------------------------------------------------------------------
-}