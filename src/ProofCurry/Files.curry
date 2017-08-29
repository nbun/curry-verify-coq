module ProofCurry.Files where

import ProofCurry.Types
import FlatCurry.Annotated.Types hiding (QName)
import FlatCurry.Annotated.TypeInference
import List
import Maybe
import Debug
import qualified VerifyOptions

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
      tdefs = map tFuncDecl (filter requiredFun functions)
   in CoqProg name [] (ttypedecls ++ tdefs)


requiredFun :: AFuncDecl a -> Bool
requiredFun (AFunc qn _ _ _ _) = qn `notElem`
  [("Prelude", "apply"), ("Prelude", "failed")] 
                                  
propType :: TypeExpr
propType = TCons ("Test.Prop","Prop") []

--------------------------------------------------------------------------------
-- FuncDecl


tFuncDecl :: AFuncDecl a -> PDecl a
tFuncDecl fdecl = case isProp fdecl of
                    True  -> PProperty $ tProp fdecl
                    False -> PFuncDecl $ tFunc fdecl

tFunc :: AFuncDecl a -> PFuncDecl a
tFunc f@(AFunc qn ar _ tyexpr rule) =
  PFunc qn ar functype args (tTypeExpr tyexpr) (tRule rule)
    where
      (tys, _) = funcTyList tyexpr
      vars     = varsOfRule rule
      args     = zip vars (map tTypeExpr tys)
      functype = if isRecFun f then Fixpoint else Definition
        
isRecFun :: AFuncDecl a -> Bool
isRecFun (AFunc fqn _ _ _ rule)  = isRecRule rule
  where isRecRule (ARule _ _ expr) = isRecExpr expr
        isRecRule (AExternal _ _)  = False

        isRecExpr (AVar _ _)        = False
        isRecExpr (ALit _ _)        = False
        isRecExpr (AComb _ _ (qn, _) es) = fqn == qn || or (map isRecExpr es)
        isRecExpr (ALet _ binds e)  = isRecExpr e
                                      || or (map (isRecExpr . snd) binds)
        isRecExpr (AFree _ _ e)     = isRecExpr e
        isRecExpr (AOr _ e1 e2)     = isRecExpr e1 || isRecExpr e2
        isRecExpr (ACase _ _ e brs) = isRecExpr e  || or (map isRecBranch brs)
        isRecExpr (ATyped _ e _)    = isRecExpr e

        isRecBranch (ABranch _ e) = isRecExpr e

tRule :: ARule a -> PExpr a
tRule (ARule _ _ e) = tExpr e
tRule (AExternal _ _) = error "external rule not supported"

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


tyVarsOfTyExpr :: TypeExpr -> [TVarIndex]
tyVarsOfTyExpr (TVar i) = [i]
tyVarsOfTyExpr (FuncType dom ran) = tyVarsOfTyExpr dom ++ tyVarsOfTyExpr ran
tyVarsOfTyExpr (TCons _ tyexprs) = concatMap tyVarsOfTyExpr tyexprs
                      

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

--------------------------------------------------------------------------------
-- TypeDecl

tTypeDecl :: TypeDecl -> PDecl a
tTypeDecl (Type qn _ tvars cdecls) =
    PTypeDecl $ PInductive qn tvars (map (tConsDecl datatype) cdecls)
        where datatype = TCons qn (map TVar tvars)
tTypeDecl (TypeSyn qn _ tvars tyExpr) =
    PTypeDecl $ PDefinition qn tvars (tTypeExpr tyExpr)

tConsDecl :: TypeExpr -> ConsDecl -> PConsDecl
tConsDecl datatype (Cons qn ar _ tyExprs) =
    PCons qn ar (map tTypeExpr tyExprs) (tTypeExpr datatype)

tTypeExpr :: TypeExpr -> PTypeExpr
tTypeExpr (TVar i)           = PTVar i
tTypeExpr (FuncType dom ran) = PFuncType (tTypeExpr dom) (tTypeExpr ran)
tTypeExpr (TCons qn tyexprs) = PTCons qn (map tTypeExpr tyexprs)