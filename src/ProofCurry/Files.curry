module ProofCurry.Files where

import ProofCurry.Types
import FlatCurry.Annotated.Types hiding (QName)
import List
import Maybe
import Debug
import qualified VerifyOptions
{-
flatCurryToProofCurry :: Prog -> CoqProg
flatCurryToProofCurry p = CoqProg "" [] []

--------------------------------------------------------------------------------
data Options = Options {indentWidth :: Int}

defaultOptions :: Options
defaultOptions = Options {indentWidth = 2}


indent' :: Options -> Doc -> Doc
indent' opts = indent (indentWidth opts)

hsepMap :: (a -> Doc) -> [a] -> Doc
hsepMap f = hsep . map f

vsepMap :: (a -> Doc) -> [a] -> Doc
vsepMap f = vsep . map f

vsepbMap :: (a -> Doc) -> [a] -> Doc
vsepbMap f = vsepBlank . map f 

($~$) :: Doc -> Doc -> Doc
d1 $~$ d2 = align $ d1 $$ d2

infixl 5 $~$

showProg :: Prog -> String
showProg (Prog _ _ typedecls functions _) =
  let header = vsep [text "Set Implicit Arguments."]
      typedeclStr = vsepbMap (tTypeDecl defaultOptions) typedecls
      functionStr = vsepbMap (tFuncDecl defaultOptions)
                             (filter requiredFun functions)
   in pPrint $ header $$ typedeclStr $$ functionStr

terminator :: Doc
terminator = text "."

requiredFun :: FuncDecl -> Bool
requiredFun (Func qn _ _ _ _) = qn `notElem`
  [("Prelude", "apply"), ("Prelude", "failed")] 
                                  
propType :: TypeExpr
propType = TCons ("Test.Prop","Prop") []

showQName :: QName -> Doc
showQName qn     = text $ case fst qn of
                            "Prelude" -> coqEquiv
                            _ -> snd qn
  where coqEquiv = case snd qn of
                     "Bool"  -> "bool"
                     "Int"   -> "nat"
                     "True"  -> "true"
                     "False" -> "false"
                     "=="    -> "="
                     "<"     -> "<"
                     ">"     -> ">"
                     "otherwise" -> "true"
                     "failed" -> "failed"
                     "(,)"    -> "pair"
                     "id"     -> "id"
                     s       -> error $ show s ++ "not supported yet"

isInfixOp :: QName -> Bool
isInfixOp qn = case qn of
                 ("Prelude", "==") -> True
                 _                 -> False

-}
--------------------------------------------------------------------------------
-- FuncDecl


-- tFuncDecl :: AFuncDecl TypeExpr -> PFuncDecl PTypeExpr
-- tFuncDecl o fdecl = case isProp fdecl of
--                        True  -> showProp o fdecl
--                        False -> tFun  o fdecl

tFun :: AFuncDecl a -> PFuncDecl a
tFun f@(AFunc qn ar _ tyexpr rule) =
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
{-
--------------------------------------------------------------------------------
-- Property

data Quantifier = Forall

showQuantifier :: Quantifier -> Doc
showQuantifier Forall = text "forall"

isProp :: FuncDecl -> Bool
isProp (Func _ _ _ tyexpr _) = (snd $ funcTyList tyexpr) == propType

splitProp :: Rule -> (Quantifier, Expr)
splitProp (External _)  = error "External function in prop found"
splitProp (Rule _ expr) =
  case expr of
    (Comb _ ("Prelude","apply") ((Comb FuncCall ("Test.Prop","always") []) : e))
      -> (Forall, head e)
    _ -> error $ "Not supported: " ++ show expr

showProp :: Options -> FuncDecl -> Doc
showProp o (Func qn _ _ tyexpr rule) =
  let (dtys, _) = funcTyList tyexpr
      tyvars    = nub $ tyVarsOfTyExpr tyexpr
      vars      = varsOfRule rule
      args      = zip vars dtys
      argStr    = hsepMap (tFunArg o) args
      tvarStr   = hsepMap showTVarIndex tyvars
      tvarStr'  = if null tyvars
                    then text ""
                    else text " " <> parens (tvarStr <+> text ": Type")
      (quant, expr) = splitProp rule
      funhead = hsep [text "Theorem", showQName qn, text ":", showQuantifier quant,
                      tvarStr'] <+> argStr <> text ","
      funbody = indent 2 $ tExpr o expr <> terminator
   in funhead $$ funbody

--------------------------------------------------------------------------------
-- TypeDecl
-}
tTypeDecl :: TypeDecl -> PTypeDecl
tTypeDecl (Type qn _ tvars cdecls) =
    PInductive qn tvars (map (tConsDecl datatype) cdecls)
        where datatype = TCons qn (map TVar tvars)
tTypeDecl (TypeSyn qn _ tvars tyExpr) =
    PDefinition qn tvars (tTypeExpr tyExpr)

tConsDecl :: TypeExpr -> ConsDecl -> PConsDecl
tConsDecl datatype (Cons qn ar _ tyExprs) =
    PCons qn ar (map tTypeExpr tyExprs) (tTypeExpr datatype)

tTypeExpr :: TypeExpr -> PTypeExpr
tTypeExpr (TVar i)           = PTVar i
tTypeExpr (FuncType dom ran) = PFuncType (tTypeExpr dom) (tTypeExpr ran)
tTypeExpr (TCons qn tyexprs) = PTCons qn (map tTypeExpr tyexprs)