------------------------------------------------------------------------------
---
--- @author
--- @version 
--- @category 
------------------------------------------------------------------------------

module ProofCurry.Types where

data CoqProg = CoqProg String [String] [PDecl]

data PDecl = PTypeDecl PTypeDecl
           | PFuncDecl PFuncDecl
           | PNotation PNotation
           | POption POption

data PNotation = PNota String PExpr (Maybe String)

type POption = String

type QName = (String, String)

type PTVarIndex = Int

data PTypeDecl
    = PInductive  QName [PTVarIndex] [PConsDecl]
    | PDefinition QName [PTVarIndex] PTypeExpr

data PConsDecl = PCons QName Int [PTypeExpr] PTypeExpr

data PTypeExpr
    = PTVar PTVarIndex            
    | PFuncType PTypeExpr PTypeExpr
    | PTCons QName [PTypeExpr]    

type PVarIndex = Int

type PArity = Int

data PFuncType = Definition | Fixpoint
               
data PFuncDecl
    = PFunc QName PArity PFuncType [(PVarIndex, PTypeExpr)] PTypeExpr PExpr

data PCombType
    = PFuncCall | PConsCall | PFuncPartCall PArity | PConsPartCall PArity

data PExpr
    = PVar PVarIndex
    | PLit PLiteral
    | PComb PCombType QName [PExpr]
    | PLet PVarIndex PExpr PExpr
    | PMatch PExpr [PBranchExpr]
    | PTyped PExpr PTypeExpr

data PBranchExpr = PBranch PPattern PExpr

data PPattern
    = PPattern QName [PVarIndex]
    | PLPattern PLiteral

data PLiteral
    = PIntc    Int
    | PStringc String