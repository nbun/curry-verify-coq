------------------------------------------------------------------------------
---
--- @author
--- @version 
--- @category 
------------------------------------------------------------------------------

module ProofCurry.Types where

data CoqProg a = CoqProg String [String] [PDecl a]

data PDecl a = PTypeDecl PTypeDecl
             | PFuncDecl (PFuncDecl a)
             | PNotation (PNotation a)
             | POption POption

data PNotation a = PNota String (PExpr a) (Maybe String)

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
    = PFunc QName PArity PFuncType [(PVarIndex, a)] PTypeExpr (PExpr a)

data PCombType
    = PFuncCall | PConsCall | PFuncPartCall PArity | PConsPartCall PArity

data PExpr a
    = PVar   a PVarIndex
    | PLit   a PLiteral
    | PComb  a PCombType (QName, a) [PExpr a]
    | PLet   a (PVarIndex, a) (PExpr a) (PExpr a)
    | PMatch a (PExpr a) [PBranchExpr a]
    | PTyped a (PExpr a) PTypeExpr

data PBranchExpr a = PBranch (PPattern a) (PExpr a)

data PPattern a
    = PPattern  a (QName, a) [(PVarIndex, a)]
    | PLPattern a PLiteral

data PLiteral
    = PIntc    Int
    | PStringc String