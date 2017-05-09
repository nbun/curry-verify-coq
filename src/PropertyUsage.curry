------------------------------------------------------------------------
--- This module contains some operations to handle properties in
--- a Curry program.
---
--- @author Michael Hanus
--- @version Augsut 2016
------------------------------------------------------------------------

module PropertyUsage
  ( isProperty, isPropType, isPropIOType
  , propModule, easyCheckModule, easyCheckExecModule
  )  where

import FlatCurry.Types
import Select (funcType, resultType)

------------------------------------------------------------------------
-- Check whether a function definition is a property,
-- i.e., if the result type is `Prop` or `PropIO`.
isProperty :: FuncDecl -> Bool
isProperty = isPropertyType . funcType
 where
  isPropertyType ct = isPropIOType ct || isPropType (resultType ct)

-- Is the type expression the type Test.EasyCheck.Prop?
isPropType :: TypeExpr -> Bool
isPropType texp = case texp of
  TCons (mn,tc) [] -> tc == "Prop" && isCheckModule mn
  _                -> False

-- Is the type expression the type Test.EasyCheck.PropIO?
isPropIOType :: TypeExpr -> Bool
isPropIOType texp = case texp of
  TCons (mn,tc) [] -> tc == "PropIO" && isCheckModule mn
  _                -> False

-- Is the module name Test.Prop or Test.EasyCheck?
isCheckModule :: String -> Bool
isCheckModule mn = mn == propModule || mn == easyCheckModule

--- Name of the Test.Prop module (the clone of the EasyCheck module).
propModule :: String
propModule = "Test.Prop" 

--- Name of the EasyCheck module.
easyCheckModule :: String
easyCheckModule = "Test.EasyCheck" 

--- Name of the EasyCheckExec module.
easyCheckExecModule :: String
easyCheckExecModule = "Test.EasyCheckExec" 

