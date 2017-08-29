------------------------------------------------------------------------------
---
--- @author
--- @version 
--- @category 
------------------------------------------------------------------------------

module ProofCurry.Types where

data CoqProg = CoqProg String [String] [PDecl]

data PDecl a = PTypeDecl PTypeDecl
             | PFuncDecl (PFuncDecl a)
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
               
data PFuncDecl a
    = PFunc QName PArity PFuncType [(PVarIndex, PTypeExpr)] PTypeExpr (PExpr a)


data PCombType
    = PFuncCall | PConsCall | PFuncPartCall PArity | PConsPartCall PArity

data PExpr a
    = PVar   a PVarIndex
    | PLit   a PLiteral
    | PComb  a PCombType QName [PExpr]
    | PLet   a PVarIndex PExpr PExpr
    | PMatch a PExpr [PBranchExpr]
    | PTyped a PExpr PTypeExpr

data PBranchExpr = PBranch PPattern PExpr

data PPattern
    = PPattern QName [PVarIndex]
    | PLPattern PLiteral

data PLiteral
    = PIntc    Int
    | PStringc String