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


e1 = putStrLn $ showProg (Prog "" [] [(Type ("Test","List") Public [0] [(Cons ("Test","Nil") 0 Public []),(Cons ("Test","Cons") 2 Public [(TVar 0),(TCons ("Test","List") [(TVar 0)])])])] [] [])

e2 = putStrLn $ showProg (Prog "" [] [(Type ("Test","Colour") Public [] [(Cons ("Test","Red") 0 Public []),(Cons ("Test","Blue") 0 Public []),(Cons ("Test","Green") 0 Public [])])] [] [])

-------------------------------------------------------------------------

theoremToCoq :: Options -> QName -> [FuncDecl] -> [TypeDecl] -> IO ()
theoremToCoq opts qtheo@(_,theoname) allfuncs alltypes = do
  writeFile "alltypes" $ show alltypes
  writeFile "allfuncs" $ show allfuncs
  writeFile (theoname ++ ".v") (showProg (Prog "" [] alltypes allfuncs []))

showProg :: Prog -> String
showProg (Prog modname imports typedecls functions opdecls) =
  let typedeclStr = concatMap (showTypeDecl True) typedecls
      functionStr = concatMap (showFuncDecl) functions
   in typedeclStr ++ functionStr

(+-+) :: String -> String -> String
s +-+ t = case (s,t) of
            ("",_) -> t
            (_,"") -> s
            _      -> case last s of
                        ' ' -> s ++ t
                        _   -> s ++ " " ++ t

--------------------------------------------------------------------------------
-- FuncDecl

showFuncDecl :: FuncDecl -> String
showFuncDecl (Func qn ar vis tyexpr rule) =
  let tyexprs = tyExprToList tyexpr
      tyvars  = tyVarsOfTyExpr tyexpr
      vars    = varsOfRule rule
      args    = zip vars tyexprs
      argStr  = unwords $ map showFunArg args
      tvarStr  = intersperse ' ' (concatMap showTVarIndex tyvars)
      tvarStr' = if null tyvars
                    then ""
                    else " " ++ implicit False (tvarStr ++ " : Type")
      funhead = "Definition" +-+ showQName qn +-+ tvarStr' +-+ argStr +-+ ":=\n"
      funbody = showRule rule
   in funhead ++ funbody

showFunArg :: (VarIndex, TypeExpr) -> String
showFunArg (i, tyexpr) = "(" ++ showVarIndex i ++
                         " : " ++ showTypeExpr tyexpr ++ ")"

showRule :: Rule -> String
showRule (Rule vars expr) = showExpr expr
showRule (External name)  = case name of
                              "Prelude.apply" -> ""
                              _ -> error "External rules not supported yet"

showExpr :: Expr -> String
showExpr (Var i) = showVarIndex i
showExpr (Lit l) = showLit l
showExpr (Comb _ qn exprs) =
  case qn of
    ("Prelude", "apply") -> "(" ++ unwords (map showExpr exprs) ++ ")"
    _ ->  "(" ++ showQName qn +-+ unwords (map showExpr exprs) +-+ ")"
showExpr (Case _ cexpr branches) =
  "match" +-+ showExpr cexpr +-+ "with\n" ++ unlines (map showBranch branches)
  ++ "end."

showBranch :: BranchExpr -> String
showBranch (Branch pat expr)="|" +-+ showPat pat +-+ "=>" +-+ showExpr expr ++ "\n"

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
                      

tyExprToList :: TypeExpr -> [TypeExpr]
tyExprToList ty = case ty of
                    (FuncType dom ran) -> dom : tyExprToList ran
                    _                  -> [ty]

varsOfRule :: Rule -> [VarIndex]
varsOfRule (Rule vars _) = vars
varsOfRule (External _)  = []
--------------------------------------------------------------------------------
-- TypeDecl

showTypeDecl :: Bool -> TypeDecl -> String
showTypeDecl imp (Type qn vis tvars cdecls) =
  let tvarStr  = intersperse ' ' (concatMap showTVarIndex tvars)
      tvarStr' = if null tvars
                    then ""
                    else " " ++ implicit imp (tvarStr ++ " : Type")
      lhs       = "Inductive " ++ showQName qn ++ tvarStr' ++ " :=\n"
      tvarexprs = map TVar tvars
      rhs       = unlines $ map (showConsDecl (TCons qn tvarexprs)) cdecls
   in lhs ++ init rhs ++ "."
showTypeDecl imp (TypeSyn qn vis tvars typeexpr) =
  error "TypeSyn not yet supported"

showQName :: QName -> String
showQName = snd

showConsDecl :: TypeExpr -> ConsDecl -> String
showConsDecl datatype (Cons qn _ _ typeexprs) =
  "| " ++ showQName qn ++ " : " ++ typeListFunType (typeexprs ++ [datatype])

typeListFunType :: [TypeExpr] -> String
typeListFunType tys = case tys of
                        []     -> ""
                        [t]    -> showTypeExpr t
                        (t:ts) -> showTypeExpr t ++ " -> " ++ typeListFunType ts

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
implicit False s = '(' : s ++ "}"