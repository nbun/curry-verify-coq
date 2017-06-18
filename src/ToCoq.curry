-------------------------------------------------------------------------
--- A transformation of Curry programs into Agda programs.
---
--- @author Michael Hanus
--- @version August 2016
-------------------------------------------------------------------------
module ToCoq (theoremToCoq) where

import FlatCurry.Types
import FlatCurry.Show
import Pretty

import List
import Maybe
import Debug

import qualified VerifyOptions
-- import VerifyPackageConfig ( packagePath )

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

--------------------------------------------------------------------------------
-- TODO:
-- * Fix indentation a little more
-- * Renaming of functions names that contain symbols
-- * let flattening
-- * Handling of $
-- * Nondeterminism
-- * Free variables
-- * Much more 

t1 :: IO ()
t1 = do
  let p = showProg (Prog [] [] [(Type ("Test","Tree") Public [0] [(Cons ("Test","Leaf") 1 Public [(TVar 0)]),(Cons ("Test","Node") 2 Public [(TCons ("Test","Tree") [(TVar 0)]),(TCons ("Test","Tree") [(TVar 0)])]),(Cons ("Test","Nil") 0 Public [])])] [(Func ("Test","&") 2 Public (FuncType (TCons ("Test","Tree") [(TVar 0)]) (FuncType (TCons ("Test","Tree") [(TVar 0)]) (TCons ("Test","Tree") [(TVar 0)]))) (Rule [1,2] (Case Rigid (Comb ConsCall ("Prelude","(,)") [(Var 1),(Var 2)]) [(Branch (Pattern ("Prelude","(,)") [3,4]) (Let [(5,(Let [(6,(Comb ConsCall ("Test","Node") [(Var 3),(Var 4)]))] (Case Rigid (Var 3) [(Branch (Pattern ("Test","Nil") []) (Var 4)),(Branch (Pattern ("Test","Leaf") [7]) (Var 6)),(Branch (Pattern ("Test","Node") [8,9]) (Var 6))])))] (Case Rigid (Var 4) [(Branch (Pattern ("Test","Nil") []) (Var 3)),(Branch (Pattern ("Test","Leaf") [10]) (Var 5)),(Branch (Pattern ("Test","Node") [11,12]) (Var 5))])))]))),(Func ("Prelude","id") 1 Public (FuncType (TVar 0) (TVar 0)) (Rule [1] (Var 1))),(Func ("Test","mapTree") 2 Public (FuncType (FuncType (TVar 0) (TVar 1)) (FuncType (TCons ("Test","Tree") [(TVar 0)]) (TCons ("Test","Tree") [(TVar 1)]))) (Rule [1,2] (Case Flex (Var 2) [(Branch (Pattern ("Test","Nil") []) (Comb ConsCall ("Test","Nil") [])),(Branch (Pattern ("Test","Leaf") [3]) (Comb ConsCall ("Test","Leaf") [(Comb FuncCall ("Prelude","apply") [(Var 1),(Var 3)])])),(Branch (Pattern ("Test","Node") [4,5]) (Comb FuncCall ("Test","&") [(Comb FuncCall ("Test","mapTree") [(Var 1),(Var 4)]),(Comb FuncCall ("Test","mapTree") [(Var 1),(Var 5)])]))]))),(Func ("Prelude","apply") 2 Public (FuncType (FuncType (TVar 0) (TVar 1)) (FuncType (TVar 0) (TVar 1))) (External "Prelude.apply")),(Func ("Test","map") 1 Public (FuncType (TCons ("Test","Tree") [(TVar 0)]) (TCons ("Test.Prop","Prop") [])) (Rule [1] (Comb FuncCall ("Prelude","apply") [(Comb FuncCall ("Test.Prop","always") []),(Comb FuncCall ("Prelude","==") [(Comb FuncCall ("Test","mapTree") [(Comb (FuncPartCall 1) ("Prelude","id") []),(Var 1)]),(Var 1)])])))] [])
  writeFile "aligntest" p
  putStrLn p
-------------------------------------------------------------------------

theoremToCoq :: VerifyOptions.Options -> QName -> [FuncDecl] -> [TypeDecl] -> IO ()
theoremToCoq _ (_,theoname) allfuncs alltypes = do
  writeFile "prog" $ show (Prog "" [] alltypes allfuncs [])
  writeFile (theoname ++ ".v") (showProg (Prog "" [] alltypes allfuncs []))

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
showExpr o (Let bs e) = vsep (map (showBind o) bs) <+> showExpr o e
showExpr _ (Free _ _) = error "Free not supported yet"
showExpr _ (Or _ _) = error "Or not supported yet"
showExpr o (Typed e ty) = parens $ hsep [showExpr o e, text ":", showTypeExpr o ty]

showBind :: Options -> (VarIndex, Expr) -> Doc
showBind o (i, e) =
  hsep [text "let", showVarIndex i, text ":=", showExpr o e]
  $~$ text " in"

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
