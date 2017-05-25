-------------------------------------------------------------------------
--- A transformation of Curry programs into Agda programs.
---
--- @author Michael Hanus
--- @version August 2016
-------------------------------------------------------------------------

module ToCoq(theoremToCoq, e1, e2) where

import FlatCurry.Types
import FlatCurry.Show

import List
import Debug

import VerifyOptions
import VerifyPackageConfig ( packagePath )


e1 = putStrLn $ showProg (Prog "" [] [(Type ("Test","List") Public [0] [(Cons ("Test","Nil") 0 Public []),(Cons ("Test","Cons") 2 Public [(TVar 0),(TCons ("Test","List") [(TVar 0)])])])] [] [])

e2 = putStrLn $ showProg (Prog "" [] [(Type ("Test","Colour") Public [] [(Cons ("Test","Red") 0 Public []),(Cons ("Test","Blue") 0 Public []),(Cons ("Test","Green") 0 Public [])])] [] [])

e3 = (Func ("Test","check") 3 Public (FuncType (FuncType (TCons ("Test","Colour") []) (TCons ("Prelude","Bool") [])) (FuncType (TCons ("Test","Colour") []) (FuncType (TCons ("Test","Colour") []) (TCons ("Prelude","Bool") [])))) (Rule [1,2,3] (Comb FuncCall ("Prelude","apply") [(Var 1),(Var 2)])))


-------------------------------------------------------------------------

theoremToCoq :: Options -> QName -> [FuncDecl] -> [TypeDecl] -> IO ()
theoremToCoq opts qtheo@(_,theoname) allfuncs alltypes = do
  writeFile "alltypes" $ show alltypes
  writeFile "allfuncs" $ show allfuncs
  writeFile (theoname ++ ".v") (showProg (Prog "" [] alltypes [] []))

showProg :: Prog -> String
showProg (Prog modname imports typedecls functions opdecls) =
  let typedeclStr = concatMap (showTypeDecl True) typedecls
   in typedeclStr

--------------------------------------------------------------------------------
-- FuncDecl

-- showFuncDecl :: FuncDecl -> String
-- showFuncDecl (Func qn ar vis tyexpr rule) =
--   let 

tyExprToList :: TypeExpr -> [TypeExpr]
tyExprToList (FuncType dom ran) = dom : tyExprToList ran 

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

implicit :: Bool -> String -> String
implicit True s  = '{' : s ++ "}"
implicit False s = '(' : s ++ "}"