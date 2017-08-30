module Language.Coq.Prettify where

import Language.Coq.Syntax
import Pretty

pIdentifier :: Identifier -> Doc
pIdentifier = text

pRoot :: Root -> Doc
pRoot (Root ss) = vsep (map pSentence ss) $$ empty

pSentence :: Sentence -> Doc
pSentence s = case s of
  SentenceDefinition def -> pDefinition def
  SentenceInductive ind  -> pInductive ind
  SentenceFixpoint fix   -> pFixpoint fix
  SentenceAssertionProof ass prf -> pAssertion ass $$ pProof prf
  SentenceSection id phrs ->
    vsep
      [ text "Section" <+> pIdentifier id <> char '.',
        indent 2 (vsep $ map pSentence phrs),
        text "End"  <+> pIdentifier id <> char '.'
      ]
  SentenceOpaque id ->
    text "Opaque" <+> pIdentifier id <> char '.'
  SentenceHintResolve id ->
    text "Hint Resolve" <+> pIdentifier id <> char '.'
  SentenceHintRewrite tm ->
    text "Hint Rewrite" <+> pTerm tm <> char '.'
  SentenceScheme scheme  -> pScheme scheme
  SentenceCombinedScheme id ids ->
    hsep
      ([ text "Combined Scheme",
        pIdentifier id,
        text "from"
       ] ++ punctuate comma (map pIdentifier ids))
     <> char '.'

pType :: Maybe Term -> [Doc]
pType Nothing   = []
pType (Just tm) = [colon, pTerm tm]

pReturnType :: Maybe Term -> [Doc]
pReturnType Nothing   = []
pReturnType (Just tm) = [text "return", pTerm tm]

pMbAnnotation :: Maybe Annotation -> [Doc]
pMbAnnotation Nothing   = []
pMbAnnotation (Just tm) = [pAnnotation tm]

pAnnotation :: Annotation -> Doc
pAnnotation (Struct id) = braces (text "struct" <+> pIdentifier id)

pDefinition :: Definition -> Doc
pDefinition (Definition id bds ty tm) =
    hsep
      ([ text "Definition", pIdentifier id] ++
       map pBinder bds ++ pType ty ++
       [ text ":=", pTerm tm]) <> char '.'


pScheme :: Scheme -> Doc
pScheme (Scheme bodies) =
    vsep
      (zipWith (<+>)
         (text "Scheme" : repeat (text "with"))
         (map pSchemeBody bodies))
    <> char '.'

pSchemeBody :: SchemeBody -> Doc
pSchemeBody (SchemeInduction id ty) =
    hsep
    [ pIdentifier id,
      text ":= Induction for",
      pIdentifier ty,
      text "Sort",
      text "Prop"
    ]

pInductive :: Inductive -> Doc
pInductive (Inductive bodies) =
    vsep
      (zipWith (<+>)
         (text "Inductive" : repeat (text "with"))
         (map pInductiveBody bodies))
    <> char '.'

pInductiveBody :: InductiveBody -> Doc
pInductiveBody (InductiveBody id bds ty ctors) =
    hsep
      ([ pIdentifier id ] ++
       map pBinder bds ++
       [ char ':'
       , pTerm ty
       , text ":="
       ]) $$
    indent 2 (vsep $ map pInductiveCtor ctors)

pInductiveCtor :: InductiveCtor -> Doc
pInductiveCtor (InductiveCtor id bds ty) =
    case ty of
      Just ty' ->
        vsep [char '|' <+> pIdentifier id,
              indent 4 (hsep (map pBinder bds) <+> colon),
              indent 4 (pTerm ty')
             ]
      Nothing ->
        hang 2 (char '|' <+> pIdentifier id <+> hsep (map pBinder bds))

pFixpoint :: Fixpoint -> Doc
pFixpoint (Fixpoint bodies) =
    vsep
      (zipWith (<+>)
         (text "Fixpoint" : repeat (text "with"))
         (map pFixpointBody bodies))
    <> char '.'

pFixpointBody :: FixpointBody -> Doc
pFixpointBody (FixpointBody id bds mbAnno ty tm) =
    hsep
      ([ pIdentifier id ] ++
       map pBinder bds ++
       pMbAnnotation mbAnno ++
       [ char ':'
       , pTerm ty
       , text ":="
       ]) $$
    indent 2 (pTerm tm)

pBinder :: Binder -> Doc
pBinder (BinderName nm) = pName nm
pBinder (BinderNameType nms tm) =
  parens . hsep $ [hsep $ map pName nms, colon, pTerm tm]

pName :: Name -> Doc
pName (NameIdent id)   = pIdentifier id
pName (NameUnderscore) = char '_'

pQualId :: QualId -> Doc
pQualId (Ident id) = pIdentifier id

pTerm :: Term -> Doc
pTerm t = case t of
  TermApp fun args ->
    parens $ foldl (<+>) (pTerm fun) (map pTerm args)
  TermNum num   -> text (show num)
  TermQualId id -> pQualId id
  TermSort srt  -> pSort srt
  TermMatch item mbTy eqns ->
    vsep
      [ hsep
          ([ text "match"
           , pMatchItem item ] ++
           pReturnType mbTy ++
           [ text "with" ])
      , indent 2 (vsep $ map pEquation eqns)
      , text "end"
      ]
  TermFunction source target ->
    pTerm source <+> text "->" <+> pTerm target
  TermForall bds tm -> parens $
    hsep ([ text "forall" ] ++ map pBinder bds ++ [ char ',' ]) $$
    indent 2 (pTerm tm)
  TermAnd tms -> vsep (punctuate (text " /\\ ") (map pTerm tms))
  TermEq l r -> pTerm l <+> char '=' $$ pTerm r

pMatchItem :: MatchItem -> Doc
pMatchItem (MatchItem tm mbName mbIn) =
     hsep [ pTerm tm ] -- TODO

pEquation :: Equation -> Doc
pEquation (Equation pat body) =
    hsep [text "|", pPattern pat, text "=>", pTerm body]

pPattern :: Pattern -> Doc
pPattern (PatCtor id fields) =
    hsep (pQualId id : map pIdentifier fields)

pSort :: Sort -> Doc
pSort Prop = text "Prop"
pSort Set  = text "Set"
pSort Type = text "Type"

pAssertion :: Assertion -> Doc
pAssertion (Assertion kw id bds ty) =
    vsep
      [ hsep
          [ pAssertionKeyword kw,
            pIdentifier id,
            hsep $ map pBinder bds,
            colon
          ],
        indent 2 (pTerm ty) <> char '.'
      ]

pAssertionKeyword :: AssertionKeyword -> Doc
pAssertionKeyword akw = case akw of
  AssTheorem     -> text "Theorem"
  AssLemma       -> text "Lemma"
  AssRemark      -> text "Remark"
  AssFact        -> text "Fact"
  AssCorollary   -> text "Corollary"
  AssProposition -> text "Proposition"
  AssDefinition  -> text "Definition"
  AssExample     -> text "Example"


pProof :: Proof -> Doc
pProof (ProofWith with steps) =
    vsep
      [ text "Proof with" <+> hsep (punctuate (text "; ") (map pProofStep with))
        <+> char '.',
        indent 2 . vsep $ map (<> char '.') (map pProofStep steps),
        text "Defined."
      ]
pProof (ProofDefined steps) =
    vsep
      [ text "Proof.",
        indent 2 . vsep $ map (<> char '.') (map pProofStep steps),
        text "Defined."
      ]
pProof (ProofQed steps) =
    vsep
      [ text "Proof.",
        indent 2 . vsep $ map (<> char '.') (map pProofStep steps),
        text "Qed."
      ]


pProofStep :: ProofStep -> Doc
pProofStep ps = case ps of
  PrHintResolve id    -> text "Hint Resolve" <+> pIdentifier id
  PrInduction id      -> text "induction" <+> pIdentifier id
  PrCrushInd          -> text "crush_ind"
  PrApply tm          -> text "apply" <+> parens (pTerm tm)
  PrSeq steps         -> hsep (punctuate (char ';') (map pProofStep steps))
  PrIntros ids        -> hsep (text "intros" : map pIdentifier ids)
  PrTry step          -> text "try" <+> parens (pProofStep step)
  PrConstructor       -> text "constructor"
  PrAuto              -> text "auto"
  PrFail              -> text "fail"
  PrInversion id      -> text "inversion" <+> pIdentifier id
  PrSubst             -> text "subst"
  PrSimpl             -> text "simpl"
  PrRepeat step       -> text "repeat" <+> parens (pProofStep step)
  PrRewrite tm        -> text "rewrite" <+> parens (pTerm tm)
  PrRewriter          -> text "rewriter"
  PrEasy              -> text "easy"
  PrTactic s ts       -> text s <+> hsep (map (parens . pTerm) ts)
  PrPoseProof tm      -> text "pose proof" <+> parens (pTerm tm)
  PrPoseProofAs tm id -> hsep
                                      [ text "pose proof",
                                        parens (pTerm tm),
                                        text "as",
                                        pIdentifier id
                                      ]
  PrBullet lvl steps  -> char c <+>
                                    vsep (punctuate (char '.')
                                            (map pProofStep steps))
    where c                   = case lvl of
                0 -> '-'
                1 -> '+'
                2 -> '*'
                _ -> '?'
  PrDestruct tm -> text "destruct" <+> parens (pTerm tm)
