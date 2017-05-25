-------------------------------------------------------------------------
--- A transformation of Curry programs into verification tools.
---
--- @author Michael Hanus
--- @version Augsut 2016
-------------------------------------------------------------------------

module ToVerifier where

import FlatCurry.Types
import FlatCurry.Files
import FlatCurry.Select (functions, tconsOfType, types)
import AbstractCurry.Types(pre)
import FlatCurry.Transform
import FlatCurry.Goodies
import Distribution      (stripCurrySuffix)
import GetOpt
import List
import Maybe             (fromJust)
import SCC               (scc)
import System            (exitWith, getArgs)

import Rewriting.Files   (showQName)
import PropertyUsage
import ToAgda
import ToCoq
import VerifyOptions

-- to use the determinism analysis:
import Analysis.ProgInfo
import Analysis.Deterministic  (Deterministic(..), nondetAnalysis)
import Analysis.TotallyDefined (Completeness(..), patCompAnalysis)
import CASS.Server             (analyzeGeneric)

import VerifyPackageConfig     (packageVersion)

-- Banner of this tool:
cvBanner :: String
cvBanner = unlines [bannerLine,bannerText,bannerLine]
 where
   bannerText = "curry-verify: Curry programs -> Verifiers (Version " ++
                packageVersion ++ " of 16/08/2016)"
   bannerLine = take (length bannerText) (repeat '-')

-- Help text
usageText :: String
usageText = usageInfo ("Usage: curry verify [options] <module names>\n") options
  
main :: IO ()
main = do
  argv <- getArgs
  let (funopts, args, opterrors) = getOpt Permute options argv
      opts = foldl (flip id) defaultOptions funopts
  unless (null opterrors)
         (putStr (unlines opterrors) >> putStrLn usageText >> exitWith 1)
  when (optVerb opts > 0) $ putStr cvBanner 
  when (null args || optHelp opts) (putStrLn usageText >> exitWith 1)
  mapIO_ (generateTheoremsForModule opts) (map stripCurrySuffix args)

-------------------------------------------------------------------------

-- Generate a file for each theorem found in a module.
generateTheoremsForModule :: Options -> String -> IO ()
generateTheoremsForModule opts mname = do
  prog <- readFlatCurry mname
  let propNames = map funcName (filter isProperty (functions prog))
      optNames  = nub (filter (\ (mn,_) -> null mn || mn == progName prog)
                              (optTheorems opts))
  if null optNames
   then if null propNames
        then putStrLn $ "No properties found in module `"++mname++"'!"
        else generateTheorems opts { optTheorems = propNames}
   else let qnames = map (\ (mn,pn) ->
                            (if null mn then progName prog else mn, pn))
                         optNames
         in if all (`elem` propNames) qnames
             then generateTheorems (opts { optTheorems = qnames })
             else error $ unwords ("Properties not found:" :
                                   map (\ (mn,pn) -> '`':mn++"."++pn++"'")
                                       (filter (`notElem` propNames) qnames))

-- Generate a proof file for each theorem in option `optTheorems`.
generateTheorems :: Options -> IO ()
generateTheorems opts = mapIO_ (generateTheorem opts) (optTheorems opts)

-- Generate a proof file for a given property name.
generateTheorem :: Options -> QName -> IO ()
generateTheorem opts qpropname = do
  (newopts, allprogs, allfuncs) <- getAllFunctions opts [] [] [qpropname]
  let alltypenames = foldr union []
                           (map (\fd -> tconsOfType (funcType fd)) allfuncs)
  alltypes <- getAllTypeDecls opts allprogs alltypenames []
  when (optVerb opts > 2) $ do
    putStrLn $ "Theorem `" ++ snd qpropname ++ "':\nInvolved operations:"
    putStrLn $ unwords (map (showQName . funcName) allfuncs)
    putStrLn $ "Involved types:"
    putStrLn $ unwords (map (showQName . typeName) alltypes)

  writeFile "alltypenames" $ show alltypenames
  writeFile "newopts" $ show newopts
  writeFile "qpropname" $ show qpropname
  writeFile "allfuncs" $ show allfuncs
  writeFile "alltypes" $ show alltypes
  case optTarget opts of
    --"agda" -> theoremToAgda newopts qpropname allfuncs alltypes
    "coq"  -> theoremToCoq  newopts qpropname allfuncs alltypes
    t      -> error $ "Unknown translation target: " ++ t

-------------------------------------------------------------------------
--- Extract all type declarations that are refererred in the types
--- of the given functions.
getAllTypeDecls :: Options -> [Prog] -> [QName] -> [TypeDecl]
               -> IO [TypeDecl]
getAllTypeDecls _ _ [] currtypes = return (sortTypeDecls currtypes)
getAllTypeDecls opts currmods (tc:tcs) currtypes
  | tc `elem` primTypes opts ++ map typeName currtypes
  = getAllTypeDecls opts currmods tcs currtypes
  | fst tc `elem` map progName currmods
  = maybe
      (-- if we don't find the qname, it must be a primitive type:
        getAllTypeDecls opts currmods tcs currtypes)
      (\tdecl -> getAllTypeDecls opts currmods
                                 (tcs ++ nub (typesOfCTypeDecl tdecl))
                                 (tdecl : currtypes))
      (find (\td -> typeName td == tc)
            (types (fromJust (find (\m -> progName m == fst tc) currmods))))
  | otherwise -- we must load a new module
  = do let mname = fst tc
       when (optVerb opts > 0) $
         putStrLn $ "Loading module '" ++ mname ++ "'..."
       newmod <- readFlatCurry mname
       getAllTypeDecls opts (newmod:currmods) (tc:tcs) currtypes

-- Sort the type declarations according to their dependencies.
sortTypeDecls :: [TypeDecl] -> [TypeDecl]
sortTypeDecls tdecls = concat (scc definedBy usedIn tdecls)
 where
  definedBy tdecl = [typeName tdecl]
  usedIn (Type    _ _ _ cdecls) = nub (concatMap typesOfConsDecl cdecls)
  usedIn (TypeSyn _ _ _ texp)   = nub (typesOfTypeExpr texp)

-------------------------------------------------------------------------

--- Extract all functions that might be called by a given function.
getAllFunctions :: Options -> [FuncDecl] -> [Prog] -> [QName]
                -> IO (Options, [Prog], [FuncDecl])
getAllFunctions opts currfuncs currmods [] = return (opts, currmods, currfuncs)
getAllFunctions opts currfuncs currmods (newfun:newfuncs)
  | newfun `elem` standardConstructors ++ map funcName currfuncs
    || isPrimFunc opts newfun
  = getAllFunctions opts currfuncs currmods newfuncs
  | null (fst newfun) -- local declarations have empty module qualifier
  = getAllFunctions opts currfuncs currmods newfuncs
  | fst newfun `elem` map progName currmods
  = maybe
       (-- if we don't find the qname, it must be a constructor:
        getAllFunctions opts currfuncs currmods newfuncs)
      (\fdecl -> getAllFunctions opts
                      (fdecl : currfuncs)
                    currmods (newfuncs ++ nub (funcsOfCFuncDecl fdecl)))
      (find (\fd -> funcName fd == newfun)
            (functions
               (fromJust (find (\m -> progName m == fst newfun) currmods))))
  | otherwise -- we must load a new module
  = do let mname = fst newfun
       when (optVerb opts > 0) $
         putStrLn $ "Loading module '" ++ mname ++ "'..."
       newmod <- readFlatCurry mname
       when (optVerb opts > 0) $
         putStrLn $ "Analyzing module '" ++ mname ++ "'..."
       pdetinfo <- analyzeGeneric nondetAnalysis mname
                                                >>= return . either id error
       pcmpinfo <- analyzeGeneric patCompAnalysis mname
                                                >>= return . either id error
       getAllFunctions
         opts { detInfos = combineProgInfo (detInfos opts) pdetinfo
              , patInfos = combineProgInfo (patInfos opts) pcmpinfo }
         currfuncs (newmod:currmods) (newfun:newfuncs)

-- Some standard constructors from the prelude.
standardConstructors :: [QName]
standardConstructors = [pre "[]", pre ":", pre "()"]

-------------------------------------------------------------------------
