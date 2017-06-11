-------------------------------------------------------------------------
--- A transformation of Curry programs into Agda programs.
---
--- @author Michael Hanus
--- @version August 2016
-------------------------------------------------------------------------
module ToCoq (theoremToCoq) where

import FlatCurry.Types
import FlatCurry.Show

import List
import Maybe
import Debug

import VerifyOptions
import VerifyPackageConfig ( packagePath )

--------------------------------------------------------------------------------
-- TODO:
-- * Fix indentation
-- * Handling of $
-- * Nondeterminism
-- * Free variables
-- * Much more 

t1 :: IO ()
t1 = putStrLn $ showProg (Prog [] [] [(Type ("Test","Tree") Public [0] [(Cons ("Test","Leaf") 1 Public [(TVar 0)]),(Cons ("Test","Node") 2 Public [(TCons ("Test","Tree") [(TVar 0)]),(TCons ("Test","Tree") [(TVar 0)])]),(Cons ("Test","Nil") 0 Public [])])] [(Func ("Test","&") 2 Public (FuncType (TCons ("Test","Tree") [(TVar 0)]) (FuncType (TCons ("Test","Tree") [(TVar 0)]) (TCons ("Test","Tree") [(TVar 0)]))) (Rule [1,2] (Case Rigid (Comb ConsCall ("Prelude","(,)") [(Var 1),(Var 2)]) [(Branch (Pattern ("Prelude","(,)") [3,4]) (Let [(5,(Let [(6,(Comb ConsCall ("Test","Node") [(Var 3),(Var 4)]))] (Case Rigid (Var 3) [(Branch (Pattern ("Test","Nil") []) (Var 4)),(Branch (Pattern ("Test","Leaf") [7]) (Var 6)),(Branch (Pattern ("Test","Node") [8,9]) (Var 6))])))] (Case Rigid (Var 4) [(Branch (Pattern ("Test","Nil") []) (Var 3)),(Branch (Pattern ("Test","Leaf") [10]) (Var 5)),(Branch (Pattern ("Test","Node") [11,12]) (Var 5))])))]))),(Func ("Prelude","id") 1 Public (FuncType (TVar 0) (TVar 0)) (Rule [1] (Var 1))),(Func ("Test","mapTree") 2 Public (FuncType (FuncType (TVar 0) (TVar 1)) (FuncType (TCons ("Test","Tree") [(TVar 0)]) (TCons ("Test","Tree") [(TVar 1)]))) (Rule [1,2] (Case Flex (Var 2) [(Branch (Pattern ("Test","Nil") []) (Comb ConsCall ("Test","Nil") [])),(Branch (Pattern ("Test","Leaf") [3]) (Comb ConsCall ("Test","Leaf") [(Comb FuncCall ("Prelude","apply") [(Var 1),(Var 3)])])),(Branch (Pattern ("Test","Node") [4,5]) (Comb FuncCall ("Test","&") [(Comb FuncCall ("Test","mapTree") [(Var 1),(Var 4)]),(Comb FuncCall ("Test","mapTree") [(Var 1),(Var 5)])]))]))),(Func ("Prelude","apply") 2 Public (FuncType (FuncType (TVar 0) (TVar 1)) (FuncType (TVar 0) (TVar 1))) (External "Prelude.apply")),(Func ("Test","map") 1 Public (FuncType (TCons ("Test","Tree") [(TVar 0)]) (TCons ("Test.Prop","Prop") [])) (Rule [1] (Comb FuncCall ("Prelude","apply") [(Comb FuncCall ("Test.Prop","always") []),(Comb FuncCall ("Prelude","==") [(Comb FuncCall ("Test","mapTree") [(Comb (FuncPartCall 1) ("Prelude","id") []),(Var 1)]),(Var 1)])])))] [])
-------------------------------------------------------------------------

theoremToCoq :: Options -> QName -> [FuncDecl] -> [TypeDecl] -> IO ()
theoremToCoq _ (_,theoname) allfuncs alltypes = do
  writeFile "alltypes" $ show alltypes
  writeFile "allfuncs" $ show allfuncs
  writeFile "prog" $ show (Prog "" [] alltypes allfuncs [])
  writeFile (theoname ++ ".v") (showProg (Prog "" [] alltypes allfuncs []))

showProg :: Prog -> String
showProg (Prog _ _ typedecls functions _) =
  let header = unlines $ ["Set Implicit Arguments."]
      typedeclStr = unlines $ map (showTypeDecl False) typedecls
      functionStr = unlines $ map (showFuncDecl) (filter requiredFun functions)
   in header +||+ typedeclStr +|+ functionStr

combineWith :: Bool -> Char -> String -> String -> String
combineWith check c s t = case (s,t, check) of
                            ("", _, _)   -> t
                            (_, "", _)   -> s
                            (_, _, True) -> if last s == c then (s ++ t)
                                                           else s ++ [c] ++ t
                            _            -> s ++ [c] ++ t

(+-+) :: String -> String -> String
s +-+ t = combineWith True ' ' s t

(+|+) :: String -> String -> String
s +|+ t = combineWith True '\n' s t

(+||+) :: String -> String -> String
s +||+ t = combineWith False '\n' s t

terminator :: String
terminator = ".\n"

requiredFun :: FuncDecl -> Bool
requiredFun (Func qn _ _ _ _) = qn `notElem`
  [("Prelude", "apply"), ("Prelude", "failed")] 
                                  

indent :: Int -> String -> String
indent n str = replicate n ' ' ++ str

propType :: TypeExpr
propType = TCons ("Test.Prop","Prop") []

showQName :: QName -> String
showQName qn     = case fst qn of
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

showFuncDecl :: FuncDecl -> String
showFuncDecl fdecl = case isProp fdecl of
                       True  -> showProp fdecl
                       False -> showFun  fdecl

showFun :: FuncDecl -> String
showFun f@(Func qn _ _ tyexpr rule) =
  let (dtys, rty) = funcTyList tyexpr
      tyvars  = nub $ tyVarsOfTyExpr tyexpr
      vars    = varsOfRule rule
      args    = zip vars dtys
      argStr  = unwords $ map showFunArg args
      tvarStr  = intersperse ' ' (concatMap showTVarIndex tyvars)
      tvarStr' = if null tyvars
                    then ""
                    else " " ++ implicit True (tvarStr +-+ ": Type")
      funkind = if isRecFun f then "Fixpoint" else "Definition"
      funhead = funkind +-+ showQName qn +-+ tvarStr' +-+ argStr +-+ ":" 
                +-+ showTypeExpr rty +-+ ":="
      funbody = showRule rule
   in funhead +|+ funbody

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

showFunArg :: (VarIndex, TypeExpr) -> String
showFunArg (i, tyexpr) = "(" ++ showVarIndex i +-+
                         ":" +-+ showTypeExpr tyexpr ++ ")"

addDot :: [String] -> [String]
addDot strs = init strs ++ [last strs ++ terminator]

showRule :: Rule -> String
showRule (Rule _ expr) = unlines $ map (indent 2) (addDot $ showExpr expr)
showRule (External s)  = error  $ "External function" +-+ s +-+ "not supported yet"

showExprL :: Expr -> String
showExprL = init . unlines . showExpr

showExpr :: Expr -> [String]
showExpr (Var i) = [showVarIndex i]
showExpr (Lit l) = [showLit l]
showExpr (Comb _ qn exprs) =
  case qn of
    ("Prelude", "apply") -> ["(" ++ unwords (map showExprL exprs) ++ ")"]
    _ -> case null exprs of
           True  -> [showQName qn]
           False -> if isInfixOp qn
                    then ["(" ++ showExprL (exprs !! 0) +-+ showQName qn
                              +-+ showExprL (exprs !! 1) ++ ")"]
                    else ["(" ++ showQName qn
                         +-+ unwords (map showExprL exprs) +-+ ")"]
showExpr (Case _ cexpr branches) =
  ["match" +-+ (showExprL cexpr) +-+ "with"] ++ map showBranch branches ++ ["end"]
showExpr (Let bs e) = [(unlines $ map showBind bs) ++ showExprL e
                      ++ replicate (length bs) ')']
showExpr (Free _ _) = error "Free not supported yet"
showExpr (Or _ _) = error "Or not supported yet"
showExpr (Typed e ty) = ["(" ++ showExprL e +-+ ":" +-+ showTypeExpr ty ++ ")"]

showBind :: (VarIndex, Expr) -> String
showBind (i, e) = "(let" +-+ showVarIndex i +-+ ":=" +-+ showExprL e +-+ "in"

showBranch :: BranchExpr -> String
showBranch (Branch pat expr)="|" +-+ showPat pat +-+ "=>" +-+ showExprL expr

showPat :: Pattern -> String
showPat (Pattern name vars) = showQName name +-+ unwords (map showVarIndex vars)
showPat (LPattern l)        = showLit l

showLit :: Literal -> String
showLit (Intc n) | n >= 0    = show n
                 | otherwise = "Negative integer literals not supported yet"
showLit (Floatc _) = "Float literals not supported yet"
showLit (Charc _)  = "Char literals not supported yet"
   
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

showQuantifier :: Quantifier -> String
showQuantifier Forall = "forall"

isProp :: FuncDecl -> Bool
isProp (Func _ _ _ tyexpr _) = (snd $ funcTyList tyexpr) == propType

splitProp :: Rule -> (Quantifier, Expr)
splitProp (External _)  = error "External function in prop found"
splitProp (Rule _ expr) =
  case expr of
    (Comb _ ("Prelude","apply") ((Comb FuncCall ("Test.Prop","always") []) : e))
      -> (Forall, head e)
    _ -> error $ "Not supported: " ++ showExprL expr

showProp :: FuncDecl -> String
showProp (Func qn _ _ tyexpr rule) =
  let (dtys, _) = funcTyList tyexpr
      tyvars    = nub $ tyVarsOfTyExpr tyexpr
      vars      = varsOfRule rule
      args      = zip vars dtys
      argStr    = unwords $ map showFunArg args
      tvarStr   = intersperse ' ' (concatMap showTVarIndex tyvars)
      tvarStr'  = if null tyvars
                    then ""
                    else " " ++ implicit False (tvarStr +-+ ": Type")
      (quant, expr) = splitProp rule
      funhead = "Theorem" +-+ showQName qn +-+ ":"
                 +-+ showQuantifier quant +-+ tvarStr' +-+ argStr ++ ","
      funbody = indent 2 $ showExprL expr ++ terminator
   in funhead +|+ funbody
--------------------------------------------------------------------------------
-- TypeDecl

showTypeDecl :: Bool -> TypeDecl -> String
showTypeDecl imp (Type qn _ tvars cdecls) =
  let tvarStr  = intersperse ' ' (concatMap showTVarIndex tvars)
      tvarStr' = if null tvars
                    then ""
                    else " " ++ implicit imp (tvarStr +-+ ": Type")
      lhs       = "Inductive" +-+ showQName qn ++ tvarStr' +-+ ":="
      tvarexprs = map TVar tvars
      rhs       = unlines $ map (showConsDecl (TCons qn tvarexprs)) cdecls
      iArgDecls = concat $ mapMaybe (implArgStr tvars) cdecls
   in lhs +|+ init rhs ++ terminator +||+ iArgDecls
showTypeDecl _ (TypeSyn _ _ _ _) =
  error "TypeSyn not yet supported"

showConsDecl :: TypeExpr -> ConsDecl -> String
showConsDecl datatype (Cons qn _ _ typeexprs) =
  "|" +-+ showQName qn +-+ ":" +-+ typeListFunType (typeexprs ++ [datatype])

implArgStr :: [TVarIndex] -> ConsDecl -> Maybe String
implArgStr tis cdecl@(Cons qn _ _ _) = if null missing then Nothing
                                                       else Just argStr
  where missing = missingTVars tis cdecl
        argStr  = "Arguments" +-+ showQName qn
                  +-+ unwords (map (\_ -> "{_}") tis) ++ terminator

showConsArg :: TypeExpr -> String
showConsArg tyexpr = case tyexpr of
                       TVar _ -> "{_}"
                       _      -> "_"

tyVarId :: TypeExpr -> Maybe TVarIndex
tyVarId tyexpr = case tyexpr of
                   TVar i -> Just i
                   _      -> Nothing

missingTVars :: [TVarIndex] -> ConsDecl -> [TVarIndex]
missingTVars tis (Cons _ _ _ tyexprs) = tis \\ mapMaybe tyVarId tyexprs

typeListFunType :: [TypeExpr] -> String
typeListFunType tys = case tys of
                        []     -> ""
                        [t]    -> showTypeExpr t
                        (t:ts) -> showTypeExpr t
                                    ++ " -> " ++ typeListFunType ts

showTypeExpr :: TypeExpr -> String
showTypeExpr (TVar i)           = showTVarIndex i
showTypeExpr (FuncType dom ran) = showTypeExpr dom +-+ "->" +-+ showTypeExpr ran
showTypeExpr (TCons qn tyexprs) = showQName qn ++ tyvarstr
  where tyvarstr = if null tyexprs then ""
                   else " " ++ concat (intersperse " " (map showTypeExpr tyexprs))

showTVarIndex :: TVarIndex -> String
showTVarIndex i = [chr (i + 65)]

showVarIndex :: VarIndex -> String
showVarIndex i = [chr (i + 97)] 

implicit :: Bool -> String -> String
implicit True s  = '{' : s ++ "}"
implicit False s = '(' : s ++ ")"