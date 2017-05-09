----------------------------------------------------------------------------
--- This library provides transformation and update operations
--- on AbstractCurry programs.
--- Since the transformations are defined recursively on structured types,
--- they are useful to construct specific transformations on AbstractCurry
--- programs.
--- In particular, this library contains the transformation
--- `renameCurryModule` to rename an AbstractCurry module.
---
--- @author Michael Hanus
--- @version April 2016
--- @category meta
----------------------------------------------------------------------------

module Transform where

import FlatCurry.Types
import Select
import List (nub, union)

--- This type synonym is useful to denote the type of an update,
--- where the first argument is the type of values which are updated
--- by the local update (which acts on types described by the second argument).
type Update a b = (b -> b) -> a -> a

----------------------------------------------------------------------------
-- CurryProg

--- Transforms an AbstractCurry program.
trCProg :: (String -> [String] -> [TypeDecl] -> [FuncDecl] -> [OpDecl] -> a)
        -> Prog -> a
trCProg prog (Prog name imps types funcs ops) =
  prog name imps types funcs ops

{-
--- Updates an AbstractCurry program.
updCProg :: (String      -> String)      ->
            ([String]    -> [String])    ->
            ([CTypeDecl] -> [CTypeDecl]) ->
            ([CFuncDecl] -> [CFuncDecl]) ->
            ([COpDecl]   -> [COpDecl])   -> CurryProg -> CurryProg
updCProg fn fi ft ff fo = trCProg prog
 where
  prog name imps types funcs ops =
    CurryProg (fn name) (fi imps) (ft types) (ff funcs) (fo ops)

--- Updates the name of a Curry program.
updCProgName :: Update CurryProg String
updCProgName f = updCProg f id id id id
-}
----------------------------------------------------------------------------
-- CTypeDecl

--- Transforms a type declaration.
trCTypeDecl :: (QName -> Visibility -> [TVarIndex] -> [ConsDecl] -> a)
            -> (QName -> Visibility -> [TVarIndex] -> TypeExpr   -> a)
            -> TypeDecl -> a
trCTypeDecl typ _  (Type name vis params cs)     = typ   name vis params cs
trCTypeDecl _ tsyn (TypeSyn name vis params syn) = tsyn  name vis params syn
{-
--- update type declaration
updCTypeDecl :: (QName -> QName)
             -> (CVisibility  -> CVisibility)
             -> ([CTVarIName] -> [CTVarIName])
             -> ([CConsDecl]  -> [CConsDecl])
             -> (CTypeExpr    -> CTypeExpr)
             -> (CConsDecl    -> CConsDecl)
             -> CTypeDecl -> CTypeDecl
updCTypeDecl fn fv fp fc fs ft = trCTypeDecl typ tsyn tntyp
 where
  typ   name vis params cs   = CType    (fn name) (fv vis) (fp params) (fc cs)
  tsyn  name vis params syn  = CTypeSyn (fn name) (fv vis) (fp params) (fs syn)
  tntyp name vis params ntyp = CNewType (fn name) (fv vis) (fp params) (ft ntyp)

--- Updates the name of a type declaration.
updCTypeDeclName :: Update CTypeDecl QName
updCTypeDeclName f = updCTypeDecl f id id id id id

-}
----------------------------------------------------------------------------
-- CConsDecl

--- Transforms a constructor declaration.
trCConsDecl :: (QName -> Arity -> Visibility -> [TypeExpr]  -> a) -> ConsDecl -> a
trCConsDecl cons (Cons name ar vis args) = cons name ar vis args
{-
--- Updates a constructor declaration.
updCConsDecl :: (QName -> QName)
             -> (CVisibility  -> CVisibility)
             -> ([CTypeExpr]  -> [CTypeExpr])
             -> ([CFieldDecl] -> [CFieldDecl])
             -> CConsDecl -> CConsDecl
updCConsDecl fn fv fts ffs = trCConsDecl cons rec
 where
  cons name vis args = CCons (fn name) (fv vis) (fts args)
  rec  name vis args = CRecord (fn name) (fv vis) (ffs args)

--- Updates the name of a constructor declaration.
updCConsDeclName :: Update CConsDecl QName
updCConsDeclName f = updCConsDecl f id id id

----------------------------------------------------------------------------
-- CFieldDecl

--- Transforms a constructor declaration.
trCFieldDecl :: (QName -> CVisibility -> CTypeExpr  -> a)
             -> CFieldDecl -> a
trCFieldDecl field (CField name vis texp) = field name vis texp

--- update constructor declaration
updCFieldDecl :: (QName -> QName)
              -> (CVisibility -> CVisibility)
              -> (CTypeExpr   -> CTypeExpr)
              -> CFieldDecl -> CFieldDecl
updCFieldDecl fn fv ft = trCFieldDecl field
 where
  field name vis texp = CField (fn name) (fv vis) (ft texp)

--- Updates the name of a constructor declaration.
updCFieldDeclName :: Update CFieldDecl QName
updCFieldDeclName f = updCFieldDecl f id id
-}
----------------------------------------------------------------------------
-- CTypeExpr

--- Transforms a type expression.
trCTypeExpr :: (TVarIndex -> a)
            -> (QName -> [a] -> a)
            -> (a -> a -> a)
            -> TypeExpr -> a
trCTypeExpr tvar tcons functype texp = trTE texp
 where
  trTE (TVar n)           = tvar n
  trTE (TCons name args)  = tcons name (map trTE args)
  trTE (FuncType from to) = functype (trTE from) (trTE to)
{-
--- Updates all type constructor applications in a type expression.
updTConsApp :: (QName -> [CTypeExpr] -> CTypeExpr) -> CTypeExpr -> CTypeExpr
updTConsApp tcons = trCTypeExpr CTVar tcons CFuncType

----------------------------------------------------------------------------
-- COpDecl

--- Transforms an operator declaration.
trCOpDecl :: (QName -> CFixity -> Int -> a) -> COpDecl -> a
trCOpDecl op (COp name fix prec) = op name fix prec

--- Updates an operator declaration.
updCOpDecl :: (QName -> QName) -> (CFixity -> CFixity) -> (Int -> Int)
           -> COpDecl -> COpDecl
updCOpDecl fn ff fp = trCOpDecl op
 where
  op name fix prec = COp (fn name) (ff fix) (fp prec)

--- Updates the name of an operator declaration.
updCOpName :: Update COpDecl QName
updCOpName f = updCOpDecl f id id
-}
----------------------------------------------------------------------------
-- CFuncDecl

--- Transforms a function declaration
trCFuncDecl :: (String -> QName -> Int -> Visibility -> TypeExpr -> Rule -> a)
            -> FuncDecl -> a
trCFuncDecl func (Func name arity vis t r) = func "" name arity vis t r
{-
--- Updates a function declaration.
updCFuncDecl :: (String -> String)
             -> (QName -> QName)
             -> (Int -> Int)
             -> (CVisibility -> CVisibility)
             -> (CTypeExpr -> CTypeExpr)
             -> ([CRule] -> [CRule])
             -> CFuncDecl -> CFuncDecl
updCFuncDecl fc fn fa fv ft fr = trCFuncDecl func
 where
  func cmt name arity vis t rules =
    if null cmt
    then CFunc (fn name) (fa arity) (fv vis) (ft t) (fr rules)
    else CmtFunc (fc cmt) (fn name) (fa arity) (fv vis) (ft t) (fr rules)
-}
----------------------------------------------------------------------------
-- CRule

--- Transform a rule.
trCRule :: ([TVarIndex] -> Expr -> a)
        -> (String -> a)
        -> Rule -> a
trCRule rule _    (Rule vs exp) = rule vs exp
trCRule _    ext (External s)   = ext s
{-
--- Update a rule.
updCRule :: ([CPattern] -> [CPattern])
         -> (CRhs -> CRhs)
         -> CRule -> CRule
updCRule fp fr = trCRule rule
 where
  rule pats rhs = CRule (fp pats) (fr rhs)

----------------------------------------------------------------------------
-- CRhs

--- Transforms a right-hand side (of a rule or case expression).
trCRhs :: (CExpr -> [CLocalDecl] -> a)
       -> ([(CExpr, CExpr)] -> [CLocalDecl] -> a)
       -> CRhs -> a
trCRhs srhs _ (CSimpleRhs  exp   locals) = srhs exp locals
trCRhs _ grhs (CGuardedRhs gexps locals) = grhs gexps locals

--- Updates right-hand side.
updCRhs :: (CExpr -> CExpr)
        -> ([(CExpr, CExpr)] -> [(CExpr, CExpr)])
        -> ([CLocalDecl]     -> [CLocalDecl])
        -> CRhs -> CRhs
updCRhs fe fg fl = trCRhs srhs grhs
 where
  srhs exp   locals = CSimpleRhs (fe exp) (fl locals)
  grhs gexps locals = CGuardedRhs (fg gexps) (fl locals)

----------------------------------------------------------------------------
-- CLocalDecl

--- Transforms a local declaration.
trCLocalDecl :: (CFuncDecl -> a)
             -> (CPattern -> CRhs -> a)
             -> ([CVarIName] -> a)
             -> CLocalDecl -> a
trCLocalDecl lfun _ _ (CLocalFunc fdecl)  = lfun fdecl
trCLocalDecl _ lpat _ (CLocalPat pat rhs) = lpat pat rhs
trCLocalDecl _ _ vars (CLocalVars vs)     = vars vs

--- Updates a local declaration.
updCLocalDecl :: (CFuncDecl   -> CFuncDecl)
              -> (CPattern    -> CPattern)
              -> (CRhs        -> CRhs)
              -> ([CVarIName] -> [CVarIName])
              -> CLocalDecl   -> CLocalDecl
updCLocalDecl ff fp fr fv = trCLocalDecl lfun lpat lvars
 where
  lfun fdecl   = CLocalFunc (ff fdecl)
  lpat pat rhs = CLocalPat (fp pat) (fr rhs)
  lvars vars   = CLocalVars (fv vars)

----------------------------------------------------------------------------
-- CPattern

--- Transforms a pattern.
trCPattern :: (CVarIName -> a)
           -> (CLiteral -> a)
           -> (QName -> [a] -> a)
           -> (CVarIName -> a -> a)
           -> (QName -> [a] -> a)
           -> (QName -> [CField a] -> a)
           -> CPattern -> a
trCPattern fv fl fc fa ff fr pattern = trP pattern
 where
  trP (CPVar pvar)         = fv pvar
  trP (CPLit lit)          = fl lit
  trP (CPComb c pats)      = fc c (map trP pats)
  trP (CPAs v pat)         = fa v (trP pat)
  trP (CPFuncComb fn pats) = ff fn (map trP pats)
  trP (CPLazy pat)         = trP pat
  trP (CPRecord r fs)      = fr r (map (\(n,p) -> (n,trP p)) fs)

--- Updates a pattern.
updCPattern :: (CVarIName   -> CVarIName)
            -> (CLiteral    -> CLiteral)
            -> (QName       -> QName)
            -> CPattern   -> CPattern
updCPattern fv fl fn = trCPattern pvar plit pcomb pas pfcomb prec
 where
  pvar var = CPVar (fv var)
  plit lit = CPLit (fl lit)
  pcomb c pats = CPComb (fn c) (map (updCPattern fv fl fn) pats)
  pas v pat = CPAs (fv v) (updCPattern fv fl fn pat)
  pfcomb f pats = CPFuncComb (fn f) (map (updCPattern fv fl fn) pats)
  prec r fields = CPRecord (fn r)
                    (map (\ (n,p) -> (fn n, updCPattern fv fl fn p)) fields)
-}

----------------------------------------------------------------------------
-- Branch

--- Transforms a branch
trBranch :: (Pattern -> Expr -> a) -> BranchExpr -> a
trBranch trbr (Branch pat expr) = trbr pat expr

----------------------------------------------------------------------------
-- CExpr

--- Transforms an expression.
trExpr :: (VarIndex -> a)
       -> (Literal -> a)
       -> (CombType -> QName -> [a] -> a)
       -> ([(VarIndex, a)] -> a -> a)
       -> ([VarIndex] -> a -> a)
       -> (a -> a -> a)
       -> (CaseType -> a -> [BranchExpr] -> a)
       -> (a -> TypeExpr -> a)
       -> Expr -> a
trExpr var lit comb trlet trfree or trcase typed expr = trE expr
 where
  trE (Var n) = var n
  trE (Lit l) = lit l
  trE (Comb ct qn exprs) = comb ct qn (map trE exprs)
  trE (Let vbinds exp) = trlet (map (\(v,e) -> (v, trE e)) vbinds) (trE exp)
  trE (Free vs exp) = trfree vs (trE exp)
  trE (Or e1 e2) = or (trE e1) (trE e2)
  trE (Case ct e branches) = trcase ct (trE e) branches
  trE (Typed e te) = typed (trE e) te

{-
----------------------------------------------------------------------------
-- CStatement

--- Transforms a statement (occuring in do expressions or list comprehensions).
trCStatement :: (CExpr -> a)
             -> (CPattern -> CExpr -> a)
             -> ([CLocalDecl] -> a)
             -> CStatement -> a
trCStatement sexp _ _ (CSExpr exp)    = sexp exp
trCStatement _ spat _ (CSPat pat exp) = spat pat exp
trCStatement _ _ slet (CSLet locals)  = slet locals

--- Updates a statement (occuring in do expressions or list comprehensions).
updCStatement :: (CExpr      -> CExpr)
              -> (CPattern   -> CPattern)
              -> (CLocalDecl -> CLocalDecl)
              -> CStatement  -> CStatement
updCStatement fe fp fd = trCStatement sexp spat slet
 where
  sexp exp     = CSExpr (fe exp)
  spat pat exp = CSPat (fp pat) (fe exp)
  slet locals  = CSLet (map fd locals)

----------------------------------------------------------------------------
--- Renames a Curry module, i.e., updates the module name and all qualified
--- names in a program.
renameCurryModule :: String -> CurryProg -> CurryProg
renameCurryModule newname prog =
  updCProgName (const newname) (updQNamesInCProg rnm prog)
 where
  rnm mn@(mod,n) | mod == progName prog = (newname,n)
                 | otherwise            = mn

--- Updates all qualified names in a Curry program.
updQNamesInCProg :: Update CurryProg QName
updQNamesInCProg f =
  updCProg id
           id
           (map (updQNamesInCTypeDecl f))
           (map (updQNamesInCFuncDecl f))
           (map (updCOpName f))

--- Updates all qualified names in a type declaration.
updQNamesInCTypeDecl :: Update CTypeDecl QName
updQNamesInCTypeDecl f =
  updCTypeDecl f id id
               (map (updQNamesInCConsDecl f))
               (updQNamesInCTypeExpr f)
               (updQNamesInCConsDecl f)

--- Updates all qualified names in a constructor declaration.
updQNamesInCConsDecl :: Update CConsDecl QName
updQNamesInCConsDecl f =
  updCConsDecl f id
               (map (updQNamesInCTypeExpr f))
               (map (updQNamesInCFieldDecl f))

--- Updates all qualified names in a record field declaration.
updQNamesInCFieldDecl :: Update CFieldDecl QName
updQNamesInCFieldDecl f = updCFieldDecl f id (updQNamesInCTypeExpr f)

--- Updates all qualified names in a type expression.
updQNamesInCTypeExpr :: (QName -> QName) -> CTypeExpr -> CTypeExpr
updQNamesInCTypeExpr f = updTConsApp (\name args -> CTCons (f name) args)

--- Updates all qualified names in a function declaration.
updQNamesInCFuncDecl :: Update CFuncDecl QName
updQNamesInCFuncDecl f =
  updCFuncDecl id f id id (updQNamesInCTypeExpr f) (map (updQNamesInCRule f))

--- Updates all qualified names in a function declaration.
updQNamesInCRule :: Update CRule QName
updQNamesInCRule f =
  updCRule (map (updQNamesInCPattern f))
           (updQNamesInCRhs f)

--- Updates all qualified names in a function declaration.
updQNamesInCRhs :: Update CRhs QName
updQNamesInCRhs f =
  updCRhs (updQNamesInCExpr f)
          (map (\ (g,e) -> (updQNamesInCExpr f g, updQNamesInCExpr f e)))
          (map (updQNamesInCLocalDecl f))

--- Updates all qualified names in a function declaration.
updQNamesInCLocalDecl :: Update CLocalDecl QName
updQNamesInCLocalDecl f =
  updCLocalDecl (updQNamesInCFuncDecl f)
                (updQNamesInCPattern f)
                (updQNamesInCRhs f)
                id

--- Updates all qualified names in a function declaration.
updQNamesInCPattern :: Update CPattern QName
updQNamesInCPattern f = updCPattern id id f

--- Updates all qualified names in a statement.
updQNamesInCStatement :: Update CStatement QName
updQNamesInCStatement f =
  updCStatement (updQNamesInCExpr f)
                (updQNamesInCPattern f)
                (updQNamesInCLocalDecl f)

updQNamesInCExpr :: Update CExpr QName
updQNamesInCExpr f =
  trExpr CVar CLit (CSymbol . f) CApply lam ldecl doexp lcomp ccase ctyped
         reccon recupd
 where
  lam pats exp = CLambda (map (updQNamesInCPattern f) pats) exp
  ldecl locals exp = CLetDecl (map (updQNamesInCLocalDecl f) locals) exp
  doexp stms = CDoExpr (map (updQNamesInCStatement f) stms)
  lcomp exp stms = CListComp exp (map (updQNamesInCStatement f) stms)
  ccase ct exp bs = CCase ct exp
    (map (\ (pat,rhs) -> (updQNamesInCPattern f pat, updQNamesInCRhs f rhs)) bs)
  ctyped exp texp = CTyped exp (updQNamesInCTypeExpr f texp)
  reccon rec fields = CRecConstr (f rec) (map (\ (l,e) -> (f l,e)) fields)
  recupd exp fields = CRecUpdate exp (map (\ (l,e) -> (f l,e)) fields)

-------------------------------------------------------------------------
--- Extracts all type names occurring in a program.
typesOfCurryProg :: Prog -> [QName]
typesOfCurryProg =
  trCProg (\_ _ types funcs _ ->
              foldr union [] (map (nub . typesOfCTypeDecl) types) ++
              foldr union [] (map (nub . typesOfCFuncDecl) funcs))
-}
--- Extracts all type names occurring in a type declaration.
typesOfCTypeDecl :: TypeDecl -> [QName]
typesOfCTypeDecl =
  trCTypeDecl (\qn _ _ cdecls -> qn : concatMap typesOfConsDecl cdecls)
              (\qn _ _ texp   -> qn : typesOfTypeExpr texp)
              -- (\qn _ _ cdecl  -> qn : typesOfConsDecl cdecl)

typesOfConsDecl :: ConsDecl -> [QName]
typesOfConsDecl =
  trCConsDecl (\_ _ _ texps -> concatMap typesOfTypeExpr texps)
            --(\_ _ fddecls -> concatMap typesOfFieldDecl fddecls)
{-
typesOfFieldDecl :: CFieldDecl -> [QName]
typesOfFieldDecl = trCFieldDecl (\_ _ texp -> typesOfTypeExpr texp)

-}
typesOfTypeExpr :: TypeExpr -> [QName]
typesOfTypeExpr = trCTypeExpr (\_ -> [])
                              (\qn targs -> qn : concat targs)
                              (++)
{-
typesOfCFuncDecl :: FuncDecl -> [QName]
typesOfCFuncDecl =
  trCFuncDecl (\_ _ _ _ texp _ -> typesOfTypeExpr texp)
  -- type annotations in expressions are currently ignored

----------------------------------------------------------------------------
--- Extracts all function (and constructor) names occurring in a program.
funcsOfCurryProg :: Prog -> [QName]
funcsOfCurryProg =
  trCProg (\_ _ types funcs _ ->
              foldr union [] (map (nub . funcsOfCTypeDecl) types) ++
              foldr union [] (map (nub . funcsOfCFuncDecl) funcs))

funcsOfCTypeDecl :: Decl -> [QName]
funcsOfCTypeDecl =
  trCTypeDecl (\_ _ _ cdecls -> concatMap funcsOfConsDecl cdecls)
              (\_ _ _ _      -> [])
              (\_ _ _ cdecl  -> funcsOfConsDecl cdecl)

funcsOfConsDecl :: CConsDecl -> [QName]
funcsOfConsDecl =
  trCConsDecl (\qn _ _       -> [qn])
            --(\qn _ fddecls -> qn : concatMap funcsOfFieldDecl fddecls)


--funcsOfFieldDecl :: CFieldDecl -> [QName]
--funcsOfFieldDecl = trCFieldDecl (\qn _ _ -> [qn])

-}
--- Extracts all function (and constructor) names occurring in a function
--- declaration.
funcsOfCFuncDecl :: FuncDecl -> [QName]
funcsOfCFuncDecl =
  trCFuncDecl (\_ _ _ _ _ rule -> funcsOfCRule rule)


funcsOfCRule :: Rule -> [QName]
funcsOfCRule = trCRule (\_ exp -> funcsOfExpr exp) (\_ -> [])

{-
funcsOfCRhs :: CRhs -> [QName]
funcsOfCRhs =
  trCRhs (\e  ldecls -> funcsOfExpr e ++ concatMap funcsOfLDecl ldecls)
         (\gs ldecls -> concatMap (\ (g,e) -> funcsOfExpr g ++ funcsOfExpr e) gs
                        ++ concatMap funcsOfLDecl ldecls)


funcsOfLDecl :: CLocalDecl -> [QName]
funcsOfLDecl = trCLocalDecl funcsOfCFuncDecl (const funcsOfExpr) (const [])
-}

funcsOfBranch :: BranchExpr -> [QName]
funcsOfBranch = trBranch (\_ expr -> funcsOfExpr expr)

funcsOfExpr :: Expr -> [QName]
funcsOfExpr =
  trExpr (const [])
         (const [])
         (\_ qn es -> qn : concat es)
         (\vbinds e -> concatMap snd vbinds ++ e)
         (\_ e -> e)
         (++)
         (\_ e branches -> concatMap funcsOfBranch branches ++ e)
         (\e _ -> e)
{-
funcsOfStat :: CStatement -> [QName]
funcsOfStat = trCStatement funcsOfExpr
                           (const funcsOfExpr)
                           (concatMap funcsOfLDecl)
-}
-------------------------------------------------------------------------
