-------------------------------------------------------------------------
--- A transformation of Curry programs into Agda programs.
---
--- @author Michael Hanus
--- @version August 2016
-------------------------------------------------------------------------
module ToCoq where -- (theoremToCoq) where

import FlatCurry.Types
import FlatCurry.Show

import List
import Debug

import VerifyOptions
import VerifyPackageConfig ( packagePath )


e1 :: IO ()
e1 = putStrLn $ showProg (Prog "" [] [(Type ("Test","Colour") Public [] [(Cons ("Test","Red") 0 Public []),(Cons ("Test","Blue") 0 Public []),(Cons ("Test","Green") 0 Public [])])] [(Func ("Test","isRed") 1 Public (FuncType (TCons ("Test","Colour") []) (TCons ("Prelude","Bool") [])) (Rule [1] (Case Flex (Var 1) [(Branch (Pattern ("Test","Red") []) (Comb ConsCall ("Prelude","True") [])),(Branch (Pattern ("Test","Blue") []) (Comb ConsCall ("Prelude","False") []))]))),(Func ("Test","check") 3 Public (FuncType (FuncType (TCons ("Test","Colour") []) (TCons ("Prelude","Bool") [])) (FuncType (TCons ("Test","Colour") []) (FuncType (TCons ("Test","Colour") []) (TCons ("Prelude","Bool") [])))) (Rule [1,2,3] (Comb FuncCall ("Prelude","apply") [(Var 1),(Var 2)]))),(Func ("Prelude","apply") 2 Public (FuncType (FuncType (TVar 0) (TVar 1)) (FuncType (TVar 0) (TVar 1))) (External "Prelude.apply")),(Func ("Test","dummy") 1 Public (FuncType (TCons ("Test","Colour") []) (TCons ("Test.Prop","Prop") [])) (Rule [1] (Comb FuncCall ("Prelude","apply") [(Comb FuncCall ("Test.Prop","always") []),(Comb FuncCall ("Test","check") [(Comb (FuncPartCall 1) ("Test","isRed") []),(Var 1),(Var 1)])])))] [])

e2 :: IO ()
e2 = putStrLn $ showProg (Prog "" [] [(Type ("Test2","MyList") Public [0] [(Cons ("Test2","Cons") 2 Public [(TVar 0),(TCons ("Test2","MyList") [(TVar 0)])]),(Cons ("Test2","Nil") 0 Public [])])] [(Func ("Test2","myMap") 2 Public (FuncType (FuncType (TVar 0) (TVar 1)) (FuncType (TCons ("Test2","MyList") [(TVar 0)]) (TCons ("Test2","MyList") [(TVar 1)]))) (Rule [1,2] (Case Flex (Var 2) [(Branch (Pattern ("Test2","Nil") []) (Comb ConsCall ("Test2","Nil") [])),(Branch (Pattern ("Test2","Cons") [3,4]) (Comb ConsCall ("Test2","Cons") [(Comb FuncCall ("Prelude","apply") [(Var 1),(Var 3)]),(Comb FuncCall ("Test2","myMap") [(Var 1),(Var 4)])]))]))),(Func ("Prelude","apply") 2 Public (FuncType (FuncType (TVar 0) (TVar 1)) (FuncType (TVar 0) (TVar 1))) (External "Prelude.apply")),(Func ("Test2","prop") 1 Public (FuncType (FuncType (TVar 0) (TVar 1)) (TCons ("Test.Prop","Prop") [])) (Rule [1] (Comb FuncCall ("Prelude","apply") [(Comb FuncCall ("Test.Prop","always") []),(Comb FuncCall ("Prelude","==") [(Comb FuncCall ("Test2","myMap") [(Var 1),(Comb ConsCall ("Test2","Nil") [])]),(Comb ConsCall ("Test2","Nil") [])])])))] [])


-------------------------------------------------------------------------

theoremToCoq :: Options -> QName -> [FuncDecl] -> [TypeDecl] -> IO ()
--theoremToCoq opts qtheo@(_,theoname) allfuncs alltypes = do
theoremToCoq _ (_,theoname) allfuncs alltypes = do
  writeFile "alltypes" $ show alltypes
  writeFile "allfuncs" $ show allfuncs
  writeFile (theoname ++ ".v") (showProg (Prog "" [] alltypes allfuncs []))

showProg :: Prog -> String
showProg (Prog _ _ typedecls functions _) =
  let typedeclStr = unlines $ map (showTypeDecl True) typedecls
      functionStr = unlines $ map (showFuncDecl) functions
   in typedeclStr ++ "\n" ++  functionStr

(+-+) :: String -> String -> String
s +-+ t = case (s,t) of
            ("",_) -> t
            (_,"") -> s
            _      -> case last s of
                        ' ' -> s ++ t
                        _   -> s ++ " " ++ t

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
                     "apply" -> "TODO: filter this out"
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
showFun (Func qn _ _ tyexpr rule) =
  let (dtys, rty) = funcTyList tyexpr
      tyvars  = nub $ tyVarsOfTyExpr tyexpr
      vars    = varsOfRule rule
      args    = zip vars dtys
      argStr  = unwords $ map showFunArg args
      tvarStr  = intersperse ' ' (concatMap showTVarIndex tyvars)
      tvarStr' = if null tyvars
                    then ""
                    else " " ++ implicit False (tvarStr ++ " : Type")
      funhead = "Definition" +-+ showQName qn +-+ tvarStr' +-+ argStr +-+ ":" 
                +-+ showTypeExpr rty +-+ ":=\n"
      funbody = showRule rule
   in funhead ++ funbody

isRecFun :: FuncDecl -> Bool
isRecFun (Func _ _ _ _ rule) = isRecRule rule
  where isRecRule (Rule _ expr) = isRecExpr expr
        isRecRule _             = False

        isRecExpr _ = False -- TODO fix this

showFunArg :: (VarIndex, TypeExpr) -> String
showFunArg (i, tyexpr) = "(" ++ showVarIndex i +-+
                         ":" +-+ showTypeExpr tyexpr ++ ")"

addDot :: [String] -> [String]
addDot strs = init strs ++ [last strs ++ "."]

showRule :: Rule -> String
showRule (Rule _ expr)    = unlines $ map (indent 2) (addDot $ showExpr expr)
showRule (External name)  = case name of
                              "Prelude.apply" -> "TODO remove this"
                              _ -> error "External rules not supported yet"

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

splitProp :: Rule -> Maybe (Quantifier, Expr)
splitProp (External _)  = error "External function in prop found"
splitProp (Rule _ expr) =
  case expr of
    (Comb _ ("Prelude","apply") ((Comb FuncCall ("Test.Prop","always") []) : e))
      -> Just (Forall, head e)
    _ -> Nothing

showProp :: FuncDecl -> String
showProp (Func qn _ _ tyexpr rule) =
  let (dtys, rty) = funcTyList tyexpr
      tyvars   = nub $ tyVarsOfTyExpr tyexpr
      vars     = varsOfRule rule
      args     = zip vars dtys
      argStr   = unwords $ map showFunArg args
      tvarStr  = intersperse ' ' (concatMap showTVarIndex tyvars)
      tvarStr' = if null tyvars
                    then ""
                    else " " ++ implicit False (tvarStr ++ " : Type")
      Just (quant, expr) = splitProp rule
      funhead = "Theorem" +-+ showQName qn +-+ ":"
                 +-+ showQuantifier quant +-+ tvarStr' +-+ argStr ++ ",\n"
      funbody = indent 2 $ showExprL expr ++ "."
   in funhead ++ funbody
--------------------------------------------------------------------------------
-- TypeDecl

showTypeDecl :: Bool -> TypeDecl -> String
showTypeDecl imp (Type qn _ tvars cdecls) =
  let tvarStr  = intersperse ' ' (concatMap showTVarIndex tvars)
      tvarStr' = if null tvars
                    then ""
                    else " " ++ implicit imp (tvarStr ++ " : Type")
      lhs       = "Inductive " ++ showQName qn ++ tvarStr' ++ " :=\n"
      tvarexprs = map TVar tvars
      rhs       = unlines $ map (showConsDecl (TCons qn tvarexprs)) cdecls
   in lhs ++ init rhs ++ "."
showTypeDecl _ (TypeSyn _ _ _ _) =
  error "TypeSyn not yet supported"

showConsDecl :: TypeExpr -> ConsDecl -> String
showConsDecl datatype (Cons qn _ _ typeexprs) =
  "| " ++ showQName qn ++ " : " ++ typeListFunType (typeexprs ++ [datatype])

typeListFunType :: [TypeExpr] -> String
typeListFunType tys = case tys of
                        []     -> ""
                        [t]    -> showTypeExpr t
                        (t:ts) -> showTypeExpr t
                                    ++ " -> " ++ typeListFunType ts

showTypeExpr :: TypeExpr -> String
showTypeExpr (TVar i)           = showTVarIndex i
showTypeExpr (FuncType dom ran) = showTypeExpr dom ++ " -> " ++ showTypeExpr ran
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