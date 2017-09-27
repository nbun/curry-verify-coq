module ToCoq (theoremToCoq) where

import FlatCurry.Types
import Language.Coq.Files
import Language.Coq.Prettify
import Pretty

import qualified VerifyOptions

theoremToCoq :: VerifyOptions.Options -> QName -> [FuncDecl] -> [TypeDecl]
             -> [QName] -> IO ()
theoremToCoq _ (_,theoname) allfuncs alltypes alltypenames = do
  let prog  = Prog "" imps alltypes funcs []
      funcs = map flattenLet allfuncs
      imps  = map fst alltypenames
              ++ concatMap modulesOfFunc allfuncs
  writeFile "prog" $ show prog
  coqProg <- flatCurryToCoq prog
  writeFile (theoname ++ ".v") (pPrint $ pRoot coqProg)


modulesOfFunc :: FuncDecl -> [String]
modulesOfFunc (Func _ _ _ _ r) = modulesOfRule r
  where modulesOfRule (External _) = []
        modulesOfRule (Rule _ e)   = modulesOfExpr e

        modulesOfExpr expr = case expr of
          Comb _ qn es -> fst qn : concatMap modulesOfExpr es
          Let bs exp   -> concatMap (\(_,e) -> modulesOfExpr e) bs
                          ++ modulesOfExpr exp
          Free _ e     -> modulesOfExpr e
          Or e1 e2     -> modulesOfExpr e1 ++ modulesOfExpr e2
          Case _ e bes -> modulesOfExpr e
                          ++ concatMap (\(Branch _ exp) -> modulesOfExpr exp) bes
          Typed e _    -> modulesOfExpr e
          _            -> []

--------------------------------------------------------------------------------
-- FlatCurry program transformations

flattenLet :: FuncDecl -> FuncDecl
flattenLet (Func qn ar vis ty r) = Func qn ar vis ty (flattenLetRule r)
  where flattenLetRule (External _) = r
        flattenLetRule (Rule is e)  = Rule is (flattenLetExpr e) 

flattenLetExpr :: Expr -> Expr
flattenLetExpr = flattenNestedLet . flattenMultiLet

flattenNestedLet :: Expr -> Expr
flattenNestedLet e =
  case e of
    Let [(v,e')] expr ->
      case e' of
        Let [b] expr' -> Let [b] (Let [(v, flattenNestedLet expr')]
                                      (flattenNestedLet expr))
        _             -> e
    _  -> modExpr flattenLetExpr e

flattenMultiLet :: Expr -> Expr
flattenMultiLet expr =
  case expr of
    Let bs e -> case bs of
                  []      -> Let [] e
                  [b]     -> Let [b] e
                  (b:bs') -> Let [b] (flattenMultiLet $ Let bs' e)
    _ -> modExpr flattenLetExpr expr

modExpr :: (Expr -> Expr) -> Expr -> Expr
modExpr f expr = case expr of
  Comb ct qn es -> Comb ct qn (map f es)
  Let bs e      -> Let (map (\(i,exp) -> (i, f exp)) bs) (f e)
  Free is e     -> Free is (f e)
  Or e1 e2      -> Or (f e1) (f e2)
  Case ct e bes -> Case ct (f e) (map (\(Branch p exp) -> Branch p (f exp))
                                            bes)
  Typed e ty    -> Typed (f e) ty
  _             -> expr