module Language.Coq.Files where

import           FlatCurry.Annotated.TypeInference
import qualified FlatCurry.Annotated.Types         as FCAT
import           Language.Coq.Syntax

{-
-- flatCurryToProofCurry :: Prog -> IO (CoqProg TypeExpr)
flatCurryToProofCurry p = do
  res <- inferProg p
  case res of
    Left e  -> error e
    Right p -> return $ tProg p

--------------------------------------------------------------------------------

tProg :: AProg a -> CoqProg a
tProg (AProg name imports typedecls functions opdecls) =
  let ttypedecls = map tTypeDecl typedecls
      tdefs = map tFunctionDecl (filter requiredFun functions)
   in CoqProg name [] (ttypedecls ++ tdefs)


requiredFun :: AFuncDecl a -> Bool
requiredFun (AFunc qn _ _ _ _) = qn `notElem`
  [("Prelude", "apply"), ("Prelude", "failed")]

propType :: TypeExpr
propType = TCons ("Test.Prop","Prop") []
-}
--------------------------------------------------------------------------------
-- FuncDecl


-- tFunctionDecl :: AFuncDecl a -> Sentence
-- tFunctionDecl fdecl = case isProp fdecl of
--                     True  -> PProperty $ tProp fdecl
--                     False -> PFuncDecl $ tFunction fdecl

tFunction :: FCAT.AFuncDecl a -> Sentence
tFunction f@(FCAT.AFunc qn ar _ tyexpr rule) =
  if isRecFun f then fixdecl else defdecl 
  where
    (tys, _)   = funcTyList tyexpr
    vars       = varsOfRule rule
    args       = zip vars (map tTypeExpr tys)
    bind (v,t) = BinderNameType [NameIdent $ tVarIndex v] (tTypeExpr t) args
    binders    = map bind args
    ty         = tTypeExpr tyexpr
    expr       = tRule rule
    ident      = tQName qn
    defdecl    = SentenceDefinition $ Definition ident binders (Just ty) expr
    fixdecl    = SentenceFixpoint $ [FixpointBody ident binders Nothing ty expr]

isRecFun :: FCAT.AFuncDecl a -> Bool
isRecFun (FCAT.AFunc fqn _ _ _ rule)  = isRecRule rule
  where isRecRule (FCAT.ARule _ _ expr) = isRecExpr expr
        isRecRule (FCAT.AExternal _ _)  = False

        isRecExpr (FCAT.AVar _ _)       = False
        isRecExpr (FCAT.ALit _ _)       = False
        isRecExpr (FCAT.AComb _ _ (qn, _) es) = fqn == qn || or (map isRecExpr es)
        isRecExpr (FCAT.ALet _ binds e)  = isRecExpr e
                                           || or (map (isRecExpr . snd) binds)
        isRecExpr (FCAT.AFree _ _ e)     = isRecExpr e
        isRecExpr (FCAT.AOr _ e1 e2)     = isRecExpr e1 || isRecExpr e2
        isRecExpr (FCAT.ACase _ _ e brs) = isRecExpr e  || or (map isRecBranch brs)
        isRecExpr (FCAT.ATyped _ e _)    = isRecExpr e

        isRecBranch (FCAT.ABranch _ e) = isRecExpr e

tRule :: FCAT.ARule a -> Term
tRule (FCAT.ARule _ _ e) = tExpr e
tRule (FCAT.AExternal _ _) = error "external rule not supported"
{-
tExpr :: AExpr a -> PExpr a
tExpr (AVar ty i) = PVar ty i
tExpr (ALit ty l) = PLit ty (tLiteral l)
tExpr (AComb ty ctype qn exprs) = PComb ty (tCombType ctype) qn (map tExpr exprs)
tExpr (ACase ty _ cexpr branches) = PMatch ty (tExpr cexpr) (map tBranch branches)
tExpr (ALet ty binds e) = case binds of
                            [(i, be)] -> PLet ty i (tExpr be) (tExpr e)
                            _         -> error "ill-formed let expression"
tExpr (AFree _ _ _) = error "Free not supported yet"
tExpr (AOr _ _ _)   = error "Or not supported yet"
tExpr (ATyped ty e tye) = PTyped ty (tExpr e) (tTypeExpr tye)

tBranch :: ABranchExpr a -> PBranchExpr a
tBranch (ABranch pat expr) = PBranch (tPattern pat) (tExpr expr)

tPattern :: APattern a -> PPattern a
tPattern (APattern ty nameTy varTys) = PPattern ty nameTy varTys
tPattern (ALPattern ty l)            = PLPattern ty (tLiteral l)

tCombType :: CombType -> PCombType
tCombType FuncCall = PFuncCall
tCombType ConsCall = PConsCall
tCombType (FuncPartCall arity) = PFuncPartCall arity
tCombType (ConsPartCall arity) = PConsPartCall arity

tLiteral :: Literal -> PLiteral
tLiteral (Intc n) | n >= 0    = PIntc n
                 | otherwise = error "Negative integer literals not supported yet"
tLiteral (Floatc _) = error "Float literals not supported yet"
tLiteral (Charc _)  = error "Char literals not supported yet"

-}
tyVarsOfTyExpr :: FCAT.TypeExpr -> [FCAT.TVarIndex]
tyVarsOfTyExpr (FCAT.TVar i) = [i]
tyVarsOfTyExpr (FCAT.FuncType dom ran) = tyVarsOfTyExpr dom ++ tyVarsOfTyExpr ran
tyVarsOfTyExpr (FCAT.TCons _ tyexprs) = concatMap tyVarsOfTyExpr tyexprs


funcTyList :: FCAT.TypeExpr ->([FCAT.TypeExpr], FCAT.TypeExpr)
funcTyList ty = case ty of
                  f@(FCAT.FuncType _ _) -> funcTyList' f
                  _                -> ([], ty)

funcTyList' :: FCAT.TypeExpr -> ([FCAT.TypeExpr], FCAT.TypeExpr)
funcTyList' fty@(FCAT.FuncType dom ran) =
  case fty of
    (FCAT.FuncType f@(FCAT.FuncType _ _) _) -> ([f] ++ a, b)
    (FCAT.FuncType _   (FCAT.FuncType _ _)) -> (x ++ a,   b)
    (FCAT.FuncType _                _) -> (x,      ran)
    _                             -> error "This should be impossible..."
  where (x,_) = funcTyList' dom
        (a,b) = funcTyList' ran
funcTyList' tyv@(FCAT.TVar _)    = ([tyv], tyv)
funcTyList' tyc@(FCAT.TCons _ _) = ([tyc], tyc)

varsOfRule :: FCAT.ARule a -> [FCAT.VarIndex]
varsOfRule (FCAT.ARule _ vars _) = map fst vars
varsOfRule (FCAT.AExternal _ _)  = []
{-
--------------------------------------------------------------------------------
-- Property


isProp :: AFuncDecl a -> Bool
isProp (AFunc _ _ _ tyexpr _) = (snd $ funcTyList tyexpr) == propType

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

tTypeDecl :: FCAT.TypeDecl -> Sentence
tTypeDecl (FCAT.Type qn _ tvars cdecls) = SentenceInductive $ Inductive [indbody]
  where datatype = FCAT.TCons qn (map FCAT.TVar tvars)
        bind tv  = BinderNameType [NameIdent $ tTVarIndex tv] (TermSort Type) 
        binders  = map bind tvars
        ctors    = map (tConsDecl datatype) cdecls
        indbody  = InductiveBody (tQName qn) binders (TermSort Type) ctors
tTypeDecl (FCAT.TypeSyn qn _ tvars tyExpr) =
  SentenceDefinition $ Definition (tQName qn) binders Nothing (tTypeExpr tyExpr)
  where binders = map (BinderName . NameIdent . tTVarIndex) tvars

tConsDecl :: FCAT.TypeExpr -> FCAT.ConsDecl -> InductiveCtor
tConsDecl datatype (FCAT.Cons qn _ _ tyexprs) =
  InductiveCtor (tQName qn) [] (Just ty)
  where ty = foldr TermFunction (tTypeExpr datatype) (map tTypeExpr tyexprs)

tTypeExpr :: FCAT.TypeExpr -> Term
tTypeExpr (FCAT.TVar i)           = TermQualId $ Ident (tTVarIndex i)
tTypeExpr (FCAT.FuncType d r)     = TermFunction (tTypeExpr d) (tTypeExpr r)
tTypeExpr (FCAT.TCons qn tyexprs) = TermApp (TermQualId (Ident $ tQName qn))
                                         (map tTypeExpr tyexprs)

tTypeExprToBinder :: FCAT.TypeExpr -> Binder
tTypeExprToBinder ty = case ty of
  FCAT.TVar i -> BinderName $ NameIdent (tTVarIndex i)
  _           -> BinderNameType [] (tTypeExpr ty)

--------------------------------------------------------------------------------
-- Utility functions

-- tQName :: QName -> Identifier
tQName (_, name) = name

-- tTVarIndex :: TVarIndex -> Identifier
tTVarIndex i = [chr (i + 65)]

-- tVarIndex :: VarIndex -> Identifier
tVarIndex i = [chr (i + 97)]
