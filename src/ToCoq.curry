module ToCoq (theoremToCoq) where

import FlatCurry.Types
import Language.Coq.Files
import Language.Coq.Prettify
import Pretty

import qualified VerifyOptions

theoremToCoq :: VerifyOptions.Options -> QName -> [FuncDecl] -> [TypeDecl]
             -> [QName] -> IO ()
theoremToCoq _ (_,theoname) allfuncs alltypes alltypenames = do
  let prog = Prog "" (modules alltypenames) alltypes allfuncs []
  writeFile "prog" $ show prog
  coqProg <- flatCurryToCoq prog
  writeFile (theoname ++ ".v") (pPrint $ pRoot coqProg)


modules :: [QName] -> [String]
modules = map fst

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
    _ -> expr -- TODO add mapping over exprs