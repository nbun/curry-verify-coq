module ProofCurry.Files where

import ProofCurry.Types
import FlatCurry.Types hiding (QName)
import FlatCurry.Show
import Pretty
import List
import Maybe
import Debug
import qualified VerifyOptions

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
      typedeclStr = vsepbMap (showTypeDecl defaultOptions) typedecls
      functionStr = vsepbMap (showFuncDecl defaultOptions)
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


--------------------------------------------------------------------------------
-- FuncDecl


showFuncDecl :: Options -> FuncDecl -> Doc
showFuncDecl o fdecl = case isProp fdecl of
                       True  -> showProp o fdecl
                       False -> showFun  o fdecl

showFun :: Options -> FuncDecl -> Doc
showFun o f@(Func qn _ _ tyexpr rule) =
  let (dtys, rty) = funcTyList tyexpr
      tyvars  = nub $ tyVarsOfTyExpr tyexpr
      vars    = varsOfRule rule
      args    = zip vars dtys
      argStr  = hsepMap (showFunArg o) args
      tvarStr  = hsepMap showTVarIndex tyvars
      tvarStr' = if null tyvars
                    then text ""
                    else braces $ tvarStr <+> text ": Type"
      funkind = text $ if isRecFun f then "Fixpoint" else "Definition"
      funhead = hsep [funkind, showQName qn, tvarStr', argStr, text ":",
                     showTypeExpr o rty, text ":="]
      funbody = indent' o $ showRule o rule
   in funhead $$ funbody

isRecFun :: FuncDecl -> Bool
isRecFun (Func fqn _ _ _ rule)  = isRecRule rule
  where isRecRule (Rule _ expr) = isRecExpr expr
        isRecRule (External _)  = False

        isRecExpr (Var _)        = False
        isRecExpr (Lit _)        = False
        isRecExpr (Comb _ qn es) = fqn == qn    || or (map isRecExpr es)
        isRecExpr (Let binds e)  = isRecExpr e  || or (map (isRecExpr . snd) binds)
        isRecExpr (Free _ e)     = isRecExpr e
        isRecExpr (Or e1 e2)     = isRecExpr e1 || isRecExpr e2
        isRecExpr (Case _ e brs) = isRecExpr e  || or (map isRecBranch brs)
        isRecExpr (Typed e _)    = isRecExpr e

        isRecBranch (Branch _ e) = isRecExpr e

showFunArg :: Options -> (VarIndex, TypeExpr) -> Doc
showFunArg o (i, tyexpr) = parens $
  hsep [showVarIndex i, text ":", showTypeExpr o tyexpr]

showRule :: Options -> Rule -> Doc
showRule o (Rule _ expr) = showExpr o expr <> terminator
showRule _ (External s)  = error$ "External function " ++ s ++ " not supported yet"

showExpr :: Options -> Expr -> Doc
showExpr _ (Var i) = showVarIndex i
showExpr _ (Lit l) = showLit l
showExpr o (Comb _ qn exprs) =
  case qn of
    ("Prelude", "apply") -> parens $ hsep (map (showExpr o) exprs)
    _ -> case null exprs of
           True  -> showQName qn
           False -> if isInfixOp qn
                    then parens $ showExpr o (exprs !! 0) <+> showQName qn
                              <+> showExpr o (exprs !! 1)
                    else parens $ showQName qn
                         <+> hsep (map (showExpr o) exprs)
showExpr o (Case _ cexpr branches) =
  hsep [text "match", showExpr o cexpr, text "with"]
  $~$ vsep (map (showBranch o) branches)
  $~$ text "end"
showExpr o l@(Let _ _) = vsep (map (showBind o e) bs)
  where (Let bs e) = flattenLet l
showExpr _ (Free _ _) = error "Free not supported yet"
showExpr _ (Or _ _)   = error "Or not supported yet"
showExpr o (Typed e ty) = parens $ hsep [showExpr o e, text ":", showTypeExpr o ty]

showBind :: Options -> Expr -> (VarIndex, Expr) -> Doc
showBind o expr (v, e) = inPosition $
  hsep [text "let", showVarIndex v, text ":=", showExpr o e]
  where inPosition doc = case expr of
                           Let _ _ -> doc <+> text "in" $~$ showExpr o expr
                           _       -> doc $~$ text " in" <+> showExpr o expr

showBranch :: Options -> BranchExpr -> Doc
showBranch o (Branch pat expr)= text "|" <+> showPat pat <+> text "=>"
                              <+> showExpr o expr

showPat :: Pattern -> Doc
showPat (Pattern name vars) = showQName name <+> hsep (map showVarIndex vars)
showPat (LPattern l)        = showLit l

showLit :: Literal -> Doc
showLit (Intc n) | n >= 0    = text $ show n
                 | otherwise = error "Negative integer literals not supported yet"
showLit (Floatc _) = error "Float literals not supported yet"
showLit (Charc _)  = error "Char literals not supported yet"
   
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

varsOfRule :: Rule -> [VarIndex]
varsOfRule (Rule vars _) = vars
varsOfRule (External _)  = []

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
      argStr    = hsepMap (showFunArg o) args
      tvarStr   = hsepMap showTVarIndex tyvars
      tvarStr'  = if null tyvars
                    then text ""
                    else text " " <> parens (tvarStr <+> text ": Type")
      (quant, expr) = splitProp rule
      funhead = hsep [text "Theorem", showQName qn, text ":", showQuantifier quant,
                      tvarStr'] <+> argStr <> text ","
      funbody = indent 2 $ showExpr o expr <> terminator
   in funhead $$ funbody

--------------------------------------------------------------------------------
-- TypeDecl

showTypeDecl :: Options -> TypeDecl -> Doc
showTypeDecl o (Type qn _ tvars cdecls) =
  let tvarStr  = hsep (map showTVarIndex tvars)
      tvarStr' = if null tvars
                    then text ""
                    else parens $ (tvarStr <+> text ": Type")
      lhs       = text "Inductive" <+> showQName qn <+> tvarStr' <+> text ":="
      tvarexprs = map TVar tvars
      rhs       = indent' o $ vsepMap (showConsDecl o (TCons qn tvarexprs)) cdecls
      iArgDecls = vsep $ mapMaybe (implArgStr tvars) cdecls
   in lhs $$ rhs <> terminator <$+$> iArgDecls <> linebreak
showTypeDecl _ (TypeSyn _ _ _ _) =
  error "TypeSyn not yet supported"

showConsDecl :: Options -> TypeExpr -> ConsDecl -> Doc
showConsDecl o datatype (Cons qn _ _ typeexprs) = 
  text "|" <+> showQName qn <+> text ":"
  <+> typeListFunType o (typeexprs ++ [datatype])

implArgStr :: [TVarIndex] -> ConsDecl -> Maybe Doc
implArgStr tis cdecl@(Cons qn _ _ _) = if null missing then Nothing
                                                       else Just argStr
  where missing = missingTVars tis cdecl
        argStr  = text "Arguments" <+> showQName qn
                  <+> hsep (map (\_ -> text "{_}") tis) <> terminator

showConsArg :: TypeExpr -> Doc
showConsArg tyexpr = case tyexpr of
                       TVar _ -> text "{_}"
                       _      -> text "_"

tyVarId :: TypeExpr -> Maybe TVarIndex
tyVarId tyexpr = case tyexpr of
                   TVar i -> Just i
                   _      -> Nothing

missingTVars :: [TVarIndex] -> ConsDecl -> [TVarIndex]
missingTVars tis (Cons _ _ _ tyexprs) = tis \\ mapMaybe tyVarId tyexprs

typeListFunType :: Options -> [TypeExpr] -> Doc
typeListFunType o tys = case tys of
                          []     -> text ""
                          [t]    -> showTypeExpr o t
                          (t:ts) -> showTypeExpr o t
                                    <+> text "->" <+> typeListFunType o ts

showTypeExpr :: Options -> TypeExpr -> Doc
showTypeExpr _ (TVar i)           = showTVarIndex i
showTypeExpr o (FuncType dom ran) =
  parensIf (complexType dom) (showTypeExpr o dom)
  <+> text "->"
  <+> parensIf (complexType ran) (showTypeExpr o ran)
showTypeExpr o (TCons qn tyexprs) = showQName qn <+> tyvarstr
  where tyvarstr = if null tyexprs then text ""
                   else hsepMap showT tyexprs
        showT ty = parensIf (complexType ty) (showTypeExpr o ty)

complexType :: TypeExpr -> Bool
complexType ty = case ty of
                   TVar _ -> False
                   _      -> True

showTVarIndex :: TVarIndex -> Doc
showTVarIndex i = text [chr (i + 65)]

showVarIndex :: VarIndex -> Doc
showVarIndex i = text [chr (i + 97)]

--------------------------------------------------------------------------------
-- FlatCurry program transformations

flattenLet :: Expr -> Expr
flattenLet = flattenNestedLet . flattenMultiLet

flattenNestedLet :: Expr -> Expr
flattenNestedLet e =
  case e of
    Let [(v,e')] expr ->
      case e' of
        Let [b] expr' -> Let [b] (Let [(v, flattenNestedLet expr')]
                                      (flattenNestedLet expr))
        _             -> e
    _  -> e -- TODO add mapping over exprs

flattenMultiLet :: Expr -> Expr
flattenMultiLet expr =
  case expr of
    Let bs e -> case bs of
                  []      -> Let [] e
                  [b]     -> Let [b] e
                  (b:bs') -> Let [b] (flattenMultiLet $ Let bs' e)
    _ -> expr -- TODO add mapping over expr