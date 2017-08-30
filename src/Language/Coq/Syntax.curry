module Language.Coq.Syntax where

type Identifier = String

-- Annotation --------------------------------------------------
data Annotation = Struct Identifier

-- Assertion ---------------------------------------------------
data Assertion = Assertion AssertionKeyword Identifier [Binder] Term

-- AssertionKeyword --------------------------------------------
data AssertionKeyword = AssTheorem
                      | AssLemma
                      | AssRemark
                      | AssFact
                      | AssCorollary
                      | AssProposition
                      | AssDefinition
                      | AssExample

-- Binder ------------------------------------------------------
data Binder = BinderName Name
            | BinderNameType [Name] Term

-- Definition --------------------------------------------------
data Definition = Definition Identifier [Binder] (Maybe Term) Term

-- Equation ----------------------------------------------------
data Equation = Equation Pattern Term

-- Fixpoint ----------------------------------------------------
data Fixpoint = Fixpoint [FixpointBody]

-- FixpointBody ------------------------------------------------
data FixpointBody = FixpointBody Identifier [Binder] (Maybe Annotation) Term Term

-- Inductive ---------------------------------------------------
data Inductive = Inductive [InductiveBody]

-- InductiveBody -----------------------------------------------
data InductiveBody = InductiveBody Identifier [Binder] Term [InductiveCtor]

-- InductiveCtor -----------------------------------------------
data InductiveCtor = InductiveCtor Identifier [Binder] (Maybe Term)

-- MatchItem ---------------------------------------------------
data MatchItem = MatchItem Term (Maybe Name) (Maybe Term)

-- Name --------------------------------------------------------
data Name = NameIdent Identifier
          | NameUnderscore

-- Pattern -----------------------------------------------------
data Pattern = PatCtor QualId [Identifier]

-- Proof -------------------------------------------------------
data Proof = ProofWith [ProofStep] [ProofStep]
           | ProofDefined [ProofStep]
           | ProofQed [ProofStep]

-- ProofStep ---------------------------------------------------
data ProofStep = PrHintResolve Identifier
               | PrInduction Identifier
               | PrCrushInd
               | PrApply Term
               | PrSeq [ProofStep]
               | PrIntros [Identifier]
               | PrTry ProofStep
               | PrConstructor
               | PrAuto
               | PrFail
               | PrInversion Identifier
               | PrSubst
               | PrSimpl
               | PrRepeat ProofStep
               | PrRewrite Term
               | PrRewriter
               | PrEasy
               | PrTactic Identifier [Term]
               | PrPoseProof Term
               | PrPoseProofAs Term Identifier
               | PrBullet Int [ProofStep]
               | PrDestruct Term

-- QualId ------------------------------------------------------
data QualId = Ident Identifier

-- Root --------------------------------------------------------
data Root = Root [Sentence]

-- Scheme ------------------------------------------------------
data Scheme = Scheme [SchemeBody]

-- SchemeBody --------------------------------------------------
data SchemeBody = SchemeInduction Identifier Identifier

-- Sentence ----------------------------------------------------
data Sentence = SentenceDefinition Definition
              | SentenceInductive Inductive
              | SentenceFixpoint Fixpoint
              | SentenceAssertionProof Assertion Proof
              | SentenceSection Identifier [Sentence]
              | SentenceOpaque Identifier
              | SentenceHintResolve Identifier
              | SentenceHintRewrite Term
              | SentenceScheme Scheme
              | SentenceCombinedScheme Identifier [Identifier]

-- Sort --------------------------------------------------------
data Sort = Prop
          | Set
          | Type

-- Term --------------------------------------------------------
data Term = TermApp Term [Term]
          | TermNum Int
          | TermQualId QualId
          | TermSort Sort
          | TermFunction Term Term
          | TermForall [Binder] Term
          | TermAnd [Term]
          | TermEq Term Term
          | TermMatch MatchItem (Maybe Term) [Equation]
