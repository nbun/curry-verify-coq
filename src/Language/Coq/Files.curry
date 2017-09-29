module Language.Coq.Files where

import           FlatCurry.Annotated.TypeInference
import           FlatCurry.Annotated.Types
import qualified FlatCurry.Types
import           Language.Coq.Syntax
import           List


data Env = Env
         { funTypes :: [(QName, TypeExpr)]
         }

getFunTypes :: AProg a -> [(QName, TypeExpr)]
getFunTypes (AProg _ _ _ fs _) = map (\(AFunc qn _ _ ty _) -> (qn, ty))
                                     (filter requiredFun fs)

flatCurryToCoq :: FlatCurry.Types.Prog -> IO Root
flatCurryToCoq p = do
  res <- inferProg p
  writeFile "tprog" $ show res
  case res of
    Left e  -> error e
    Right p -> return $ tProg (Env $ getFunTypes p) p

tProg :: Env -> AProg TypeExpr -> Root
tProg env (AProg name imports typedecls functions opdecls) =
  let ttyds = map tTypeDecl typedecls
      tdefs = map (tFunctionDecl env) (filter requiredFun functions)
   in Root $ ttyds ++ tdefs


requiredFun :: AFuncDecl a -> Bool
requiredFun (AFunc qn _ _ _ _) = qn `notElem`
  [("Prelude", "apply"), ("Prelude", "failed")]

propType :: TypeExpr
propType = TCons ("Test.Prop","Prop") []

--------------------------------------------------------------------------------
-- FuncDecl


tFunctionDecl :: Env -> AFuncDecl TypeExpr -> Sentence
tFunctionDecl env fdecl = case isProp fdecl of
                    True  -> tProp env fdecl
                    False -> tFunction env fdecl

tFunction :: Env -> AFuncDecl TypeExpr -> Sentence
tFunction env f@(AFunc qn _ _ tyexpr rule) =
  if isRecFun f then fixdecl else defdecl
  where
    (tys, _)   = funcTyList tyexpr
    tyvars     = nub $ tyVarsOfTyExpr tyexpr
    tyvbinder  = BinderNameType (map (NameIdent . tTVarIndex) tyvars)
                                (TermSort SortType)
    vars       = varsOfRule rule
    args       = zip vars (map tTypeExpr tys)
    bind (v,t) = BinderNameType [NameIdent $ tVarIndex v] t
    binders    = if null tyvars then map bind args
                                else tyvbinder : map bind args
    ty         = tTypeExpr (snd $ funcTyList tyexpr)
    expr       = tRule env rule
    ident      = tQName qn
    defdecl    = SentenceDefinition $ Definition ident binders (Just ty) expr
    fixdecl    = SentenceFixpoint $
                   Fixpoint [FixpointBody ident binders Nothing ty expr]

toBinders :: FlatCurry.Types.TypeExpr -> ARule a -> [Binder]
toBinders ty r = binders
  where
    (tys, _)   = funcTyList ty
    tyvars     = nub $ tyVarsOfTyExpr ty
    tyvbinder  = BinderNameType (map (NameIdent . tTVarIndex) tyvars)
                                (TermSort SortType)
    vars       = varsOfRule r
    args       = zip vars (map tTypeExpr tys)
    bind (v,t) = BinderNameType [NameIdent $ tVarIndex v] t
    binders    = if null tyvars then map bind args
                                else tyvbinder : map bind args

isRecFun :: AFuncDecl TypeExpr -> Bool
isRecFun (AFunc fqn _ _ _ rule)  = isRecRule rule
  where isRecRule (ARule _ _ expr) = isRecExpr expr
        isRecRule (AExternal _ _)  = False

        isRecExpr (AVar _ _)       = False
        isRecExpr (ALit _ _)       = False
        isRecExpr (AComb _ _ (qn, _) es) = fqn == qn || or (map isRecExpr es)
        isRecExpr (ALet _ binds e)  = isRecExpr e
                                           || or (map (isRecExpr . snd) binds)
        isRecExpr (AFree _ _ e)     = isRecExpr e
        isRecExpr (AOr _ e1 e2)     = isRecExpr e1 || isRecExpr e2
        isRecExpr (ACase _ _ e brs) = isRecExpr e  || or (map isRecBranch brs)
        isRecExpr (ATyped _ e _)    = isRecExpr e

        isRecBranch (ABranch _ e) = isRecExpr e

tRule :: Env -> ARule TypeExpr -> Term
tRule env (ARule _ _ e)   = tExpr env e
tRule _ (AExternal _ _) = error "external rule not supported"

tExpr :: Env -> AExpr TypeExpr -> Term
tExpr _ (AVar _ i) = TermQualId $ Ident (tVarIndex i)
tExpr _ (ALit _ l) = tLiteral l
tExpr env (AComb ty ct (qn, fty) exprs) =
  let tyvs = case (ct, lookup qn (funTypes env)) of
               (FuncCall, Just ety)       -> map (tyVar . snd) $ unify ety fty
               (FuncPartCall _, Just ety) -> map (tyVar . snd) $ unify ety fty
               (ConsCall, _)              -> tyVars ty
               (ConsPartCall _, _)        -> tyVars ty
               _                          -> []
  in case qn of
       ("Prelude", "apply") -> TermApp (tExpr env $ head exprs)
                                       (tyvs ++ (map (tExpr env) $ tail exprs))
       _                    -> TermApp f (tyvs ++ map (tExpr env) exprs)
         where f    = TermQualId $ Ident (tQName qn)
tExpr env (ACase _ _ cexpr branches) =
  TermMatch mItem Nothing (map (tBranch env) branches)
    where mItem = MatchItem (tExpr env cexpr) Nothing Nothing
tExpr env (ALet _ binds e) =
  case binds of
    [((i, _), be)] -> TermLet x (tExpr env be) (tExpr env e)
      where x =  TermQualId $ Ident (tVarIndex i)
    _              -> error "ill-formed let expression"
tExpr _ (AFree _ _ _) = error "Free not supported yet"
tExpr _ (AOr _ _ _)   = error "Or not supported yet"
tExpr _ (ATyped _ e tye) = error "Typed not supported yet"

tyVar :: TVarIndex -> Term
tyVar = TermQualId . Ident . tTVarIndex

tyVars :: TypeExpr -> [Term]
tyVars t =  map (TermQualId . Ident . tTVarIndex) (tyVarsOfTyExpr t)

tBranch :: Env -> ABranchExpr TypeExpr -> Equation
tBranch env (ABranch pat expr) = Equation (tPattern pat) (tExpr env expr)

tPattern :: APattern TypeExpr -> Pattern
tPattern (APattern t (qn, _) varTys) =
  PatCtor (Ident (tQName qn)) (tyvs ++ map (tVarIndex . fst) varTys)
  where tyvs = map (const "_") (tyVarsOfTyExpr t)
tPattern (ALPattern _ _)             = error "literal patern not supported yet"

tLiteral :: Literal -> Term
tLiteral (Intc n) | n >= 0    = TermNum n
                  | otherwise = error "Negative integer literals not supported yet"
tLiteral (Floatc _) = error "Float literals not supported yet"
tLiteral (Charc _)  = error "Char literals not supported yet"

tyVarsOfTyExpr :: TypeExpr -> [TVarIndex]
tyVarsOfTyExpr (TVar i)           = [i]
tyVarsOfTyExpr (FuncType dom ran) = tyVarsOfTyExpr dom ++ tyVarsOfTyExpr ran
tyVarsOfTyExpr (TCons _ tyexprs)  = concatMap tyVarsOfTyExpr tyexprs


funcTyList :: TypeExpr ->([TypeExpr], TypeExpr)
funcTyList ty = case ty of
                  f@(FuncType _ _) -> funcTyList' f
                  _                -> ([], ty)

funcTyList' :: TypeExpr -> ([TypeExpr], TypeExpr)
funcTyList' fty@(FuncType dom ran) =
  case fty of
    (FuncType f@(FuncType _ _) _) -> ([f] ++ a, b)
    (FuncType _   (FuncType _ _)) -> (x ++ a,   b)
    (FuncType _                _) -> (x,      ran)
    _                             -> error "This should be impossible..."
  where (x,_) = funcTyList' dom
        (a,b) = funcTyList' ran
funcTyList' tyv@(TVar _)    = ([tyv], tyv)
funcTyList' tyc@(TCons _ _) = ([tyc], tyc)

varsOfRule :: ARule a -> [VarIndex]
varsOfRule (ARule _ vars _) = map fst vars
varsOfRule (AExternal _ _)  = []

--------------------------------------------------------------------------------
-- Property

tProp :: Env -> AFuncDecl TypeExpr -> Sentence
tProp env (AFunc qn _ _ tyexpr rule) = SentenceAssertionProof ass (ProofQed [])
  where ass = Assertion AssTheorem (tQName qn) [] (tPropRule env tyexpr rule)

isProp :: AFuncDecl a -> Bool
isProp (AFunc _ _ _ tyexpr _) = (snd $ funcTyList tyexpr) == propType

tPropRule :: Env -> TypeExpr -> ARule TypeExpr -> Term
tPropRule _ _ (AExternal _ _)    = error "External function in prop found"
tPropRule env ty r@(ARule _ _ expr) =
   case expr of
     AComb _ _ qn es ->
       case qn of
         (("Prelude","apply"), _) ->
           case es of
             (AComb _ FuncCall qn' []) : e ->
               case qn' of
                 (("Test.Prop", "always"), _) ->
                   TermForall (toBinders ty r) (TermEq (tExpr env $ head e) true)
                 _ -> error $ "1 Not supported: " ++ show qn
             _ -> error $ "2 Not supported: " ++ show (head es)
         (("Test.Prop", "always"), _) -> TermForall (toBinders ty r)
                                                (TermEq (tExpr env $ head es) true)
         _ -> error $ "3 Not supported: " ++ show qn
     _ -> error $ "4 Not supported: " ++ show expr
  where true =  TermQualId $ Ident "true"
--------------------------------------------------------------------------------
-- TypeDecl

tTypeDecl :: TypeDecl -> Sentence
tTypeDecl (Type qn _ tvars cdecls) = SentenceInductive $ Inductive [indbody]
  where datatype = TCons qn (map TVar tvars)
        bind tv  = BinderNameType [NameIdent $ tTVarIndex tv] (TermSort SortType)
        binders  = map bind tvars
        ctors    = map (tConsDecl datatype) cdecls
        indbody  = InductiveBody (tQName qn) binders (TermSort SortType) ctors
tTypeDecl (TypeSyn qn _ tvars tyExpr) =
  SentenceDefinition $ Definition (tQName qn) binders Nothing (tTypeExpr tyExpr)
  where binders = map (BinderName . NameIdent . tTVarIndex) tvars

tConsDecl :: TypeExpr -> ConsDecl -> InductiveCtor
tConsDecl datatype (Cons qn _ _ tyexprs) =
  InductiveCtor (tQName qn) [] (Just ty)
  where ty = foldr TermFunction (tTypeExpr datatype) (map tTypeExpr tyexprs)

tTypeExpr :: TypeExpr -> Term
tTypeExpr (TVar i)           = TermQualId $ Ident (tTVarIndex i)
tTypeExpr (FuncType d r)     = TermFunction (tTypeExpr d) (tTypeExpr r)
tTypeExpr (TCons qn tyexprs) = TermApp (TermQualId (Ident $ tQName qn))
                                         (map tTypeExpr tyexprs)

tTypeExprToBinder :: TypeExpr -> Binder
tTypeExprToBinder ty = case ty of
  TVar i -> BinderName $ NameIdent (tTVarIndex i)
  _      -> BinderNameType [] (tTypeExpr ty)

--------------------------------------------------------------------------------
-- Utility functions

tQName :: QName -> Identifier
tQName (_, name) = case name of
                     "Bool"  -> "bool"
                     "True"  -> "true"
                     "False" -> "false"
                     _       -> name

tTVarIndex :: TVarIndex -> Identifier
tTVarIndex i = [chr (i + 65)]

tVarIndex :: VarIndex -> Identifier
tVarIndex i = [chr (i + 97)]

unify :: TypeExpr -> TypeExpr -> [(TVarIndex, TVarIndex)]
unify t1 t2 = nubBy (\(i,_) (j,_) -> i == j) $
  case (t1, t2) of
    (TVar x,         TVar y)         -> [(x, y)]
    (FuncType d1 r1, FuncType d2 r2) -> unify d1 d2 ++ unify r1 r2
    (TCons _ ts1,    TCons _ ts2)    -> concatMap (uncurry unify) (zip ts1 ts2)
    _                                -> error "Type error in original program"