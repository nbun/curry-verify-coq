module Language.Coq.Files where
-- module Files where

import           FlatCurry.Annotated.TypeInference
import           FlatCurry.Annotated.Types
import           Language.Coq.Syntax
import List

-- flatCurryToCoq :: Prog -> IO Root
flatCurryToCoq p = do
  res <- inferProg p
  case res of
    Left e  -> error e
    Right p -> return $ tProg p

--------------------------------------------------------------------------------

tProg :: AProg a -> Root
tProg (AProg name imports typedecls functions opdecls) =
  let ttyds = map tTypeDecl typedecls
      tdefs      = map tFunctionDecl (filter requiredFun functions)
   in Root $ ttyds ++ tdefs


requiredFun :: AFuncDecl a -> Bool
requiredFun (AFunc qn _ _ _ _) = qn `notElem`
  [("Prelude", "apply"), ("Prelude", "failed")]

propType :: TypeExpr
propType = TCons ("Test.Prop","Prop") []

--------------------------------------------------------------------------------
-- FuncDecl


tFunctionDecl :: AFuncDecl a -> Sentence
tFunctionDecl fdecl = case isProp fdecl of
                    True  -> error "prop not implemented yet" -- tProp fdecl
                    False -> tFunction fdecl

tFunction :: AFuncDecl a -> Sentence
tFunction f@(AFunc qn _ _ tyexpr rule) =
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
    ty         = tTypeExpr tyexpr
    expr       = tRule rule
    ident      = tQName qn
    defdecl    = SentenceDefinition $ Definition ident binders (Just ty) expr
    fixdecl    = SentenceFixpoint $
                   Fixpoint [FixpointBody ident binders Nothing ty expr]

isRecFun :: AFuncDecl a -> Bool
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

tRule :: ARule a -> Term
tRule (ARule _ _ e)   = tExpr e
tRule (AExternal _ _) = error "external rule not supported"

tExpr :: AExpr a -> Term
tExpr (AVar _ i) = TermQualId $ Ident (tVarIndex i)
tExpr (ALit _ l) = tLiteral l
tExpr (AComb _ _ (qn, _) exprs) = case qn of
  ("Prelude", "apply") -> TermApp (tExpr $ head exprs) (map tExpr $ tail exprs)
  _                    -> TermApp f (map tExpr exprs)
    where f = TermQualId $ Ident (tQName qn)
tExpr (ACase _ _ cexpr branches) = TermMatch mItem Nothing (map tBranch branches)
  where mItem = MatchItem (tExpr cexpr) Nothing Nothing
tExpr (ALet _ binds e) = error "Let not supported yet"
                          -- case binds of
                            -- [(i, be)] -> PLet ty i (tExpr be) (tExpr e)
                            -- _         -> error "ill-formed let expression"
tExpr (AFree _ _ _) = error "Free not supported yet"
tExpr (AOr _ _ _)   = error "Or not supported yet"
tExpr (ATyped _ e tye) = error "Typed not supported yet"

tBranch :: ABranchExpr a -> Equation
tBranch (ABranch pat expr) = Equation (tPattern pat) (tExpr expr)

tPattern :: APattern a -> Pattern
tPattern (APattern ty (qn, _) varTys) =
  PatCtor (Ident (tQName qn)) (map (tVarIndex . fst) varTys)
tPattern (ALPattern ty lit)           = error "literal patern not supported yet"

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


isProp :: AFuncDecl a -> Bool
isProp (AFunc _ _ _ tyexpr _) = (snd $ funcTyList tyexpr) == propType
{-
splitProp :: ARule a -> (Quantifier, AExpr a)
splitProp (AExternal _ _)  = error "External function in prop found"
splitProp (ARule _ _ expr) =
  case expr of
    AComb _ _ qn es ->
      case qn of
        (("Prelude","apply"), _) ->
          case es of
            (AComb _ FuncCall qn' []) : e ->
              case qn' of
                (("Test.Prop", "always"), _) -> (Forall, head e)
                _ -> error $ "Not supported: " ++ show qn
            _ -> error $ "Not supported: " ++ show (head es)
        _ -> error $ "Not supported: " ++ show qn
    _ -> error $ "Not supported: " ++ show expr

tProp :: AFuncDecl a -> PProperty a
tProp (AFunc qn _ _ tyexpr rule) =
  let (dtys, _) = funcTyList tyexpr
      vars      = varsOfRule rule
      args      = zip vars (map tTypeExpr dtys)
      (quant, expr) = splitProp rule
   in PProp qn (Just quant) args (tExpr expr)
-}
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
tQName (_, name) = name

tTVarIndex :: TVarIndex -> Identifier
tTVarIndex i = [chr (i + 65)]

tVarIndex :: VarIndex -> Identifier
tVarIndex i = [chr (i + 97)]
