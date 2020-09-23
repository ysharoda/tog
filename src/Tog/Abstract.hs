{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -w -fwarn-incomplete-patterns #-}
{-| Abstract syntax produced by scope checker, input for the type checker.
 -}
module Tog.Abstract where

import           Tog.Prelude
import           Tog.PrettyPrint as TPP
import           Tog.Names
import           Text.PrettyPrint.Leijen as PP

-- * Abstract syntax.
------------------------------------------------------------------------

data Module = Module QName Params [QName] [Decl]

type Params = [(Name, Expr)]

data Decl
  = TypeSig TypeSig
  | Postulate TypeSig
  | Data TypeSig
  | Record TypeSig
  | FunDef QName [Clause]
  | DataDef QName [Name] [TypeSig]
  | RecDef  QName [Name] QName [TypeSig]
  | Module_ Module
  | Import QName [Expr]
  | Open QName

data TypeSig = Sig
  { typeSigName :: QName
  , typeSigType :: Expr
  }

data Clause = Clause [Pattern] ClauseBody

data ClauseBody
  = ClauseBody Expr [Decl]
  | ClauseNoBody

data Expr
  = Lam Name Expr
  | Pi Name Expr Expr
  | Fun Expr Expr
  | Equal Expr Expr Expr
  | App Head [Elim]
  | Set SrcLoc
  | Meta SrcLoc
  | Refl SrcLoc
  | Con QName [Expr]

data Head
  = Var Name
  | Def QName
  | J SrcLoc

data Elim
  = Apply Expr
  | Proj QName
  deriving Eq

data Pattern
  = VarP Name
  | WildP SrcLoc
  | ConP QName [Pattern]
  | EmptyP SrcLoc

-- | Number of variables bound by a list of pattern.
patternsBindings :: [Pattern] -> Int
patternsBindings = sum . map patternBindings

-- | Number of variables bound by a pattern.
patternBindings :: Pattern -> Int
patternBindings (VarP _)      = 1
patternBindings (WildP _)     = 1
patternBindings (ConP _ pats) = patternsBindings pats
patternBindings EmptyP{}      = 0

-- * Instances
------------------------------------------------------------------------

instance HasSrcLoc SrcLoc where
  srcLoc = id

instance HasSrcLoc Name where
  srcLoc (Name p _) = p

instance HasSrcLoc Module where
  srcLoc (Module x _ _ _) = srcLoc x

instance HasSrcLoc Decl where
  srcLoc d = case d of
    TypeSig sig    -> srcLoc sig
    Postulate sig  -> srcLoc sig
    Data sig       -> srcLoc sig
    Record sig     -> srcLoc sig
    FunDef x _     -> srcLoc x
    DataDef x _ _  -> srcLoc x
    RecDef x _ _ _ -> srcLoc x
    Module_ x      -> srcLoc x
    Open x         -> srcLoc x
    Import x _     -> srcLoc x

instance HasSrcLoc TypeSig where
  srcLoc (Sig x _) = srcLoc x

instance HasSrcLoc Expr where
  srcLoc e = case e of
    Lam x _     -> srcLoc x
    Pi x _ _    -> srcLoc x
    Fun a _     -> srcLoc a
    Equal _ a _ -> srcLoc a
    App h _     -> srcLoc h
    Set p       -> p
    Meta p      -> p
    Con c _     -> srcLoc c
    Refl p      -> p

instance HasSrcLoc Head where
  srcLoc h = case h of
    Var x       -> srcLoc x
    Def x       -> srcLoc x
    J loc       -> loc

instance HasSrcLoc QName where
  srcLoc (QName n _) = srcLoc n

instance HasSrcLoc Pattern where
  srcLoc p = case p of
    WildP p  -> p
    VarP x   -> srcLoc x
    ConP c _ -> srcLoc c
    EmptyP x -> x

instance HasSrcLoc Elim where
  srcLoc e = case e of
    Apply e -> srcLoc e
    Proj x  -> srcLoc x

-- | Syntactic equality (ignoring source locations).

instance Eq Expr where
  Lam x e     == Lam x' e'      = x == x' && e == e'
  Pi x a b    == Pi x' a' b'    = x == x' && a == a' && b == b'
  Fun a b     == Fun a' b'      = a == a' && b == b'
  Equal a x y == Equal a' x' y' = a == a' && x == x' && y == y'
  App h es    == App h' es'     = h == h' && es == es'
  Set _       == Set _          = True
  Meta _      == Meta _         = True
  _           == _              = False

instance Eq Head where
  Var x  == Var x' = x == x'
  Def f  == Def f' = f == f'
  J _    == J _    = True
  _      == _      = False

-- Pretty printing
------------------------------------------------------------------------

instance Show Decl    where showsPrec = defaultShow
instance Show TypeSig where showsPrec = defaultShow
instance Show Elim    where showsPrec = defaultShow
instance Show Expr    where showsPrec = defaultShow
instance Show Head    where showsPrec = defaultShow
instance Show Pattern where showsPrec = defaultShow
instance Show Module  where showsPrec = defaultShow

instance TPP.Pretty Module where
  pretty (Module name pars exports decls) =
    let parsDoc =
          let ds = [PP.parens (TPP.pretty n <+> colon <+> TPP.pretty ty) | (n, ty) <- pars]
          in if null ds then empty else foldr (<+>) empty ds 
    in (text "module" <+> TPP.pretty name <+> parsDoc <+> text "where") <$$>
       (vcat (map TPP.pretty decls))

instance TPP.Pretty TypeSig where
  pretty (Sig x e) =
    TPP.pretty x <+> colon <+> TPP.pretty e

instance TPP.Pretty Decl where
  pretty d = case d of
    TypeSig sig ->
      TPP.pretty sig
    Postulate sig ->
      text "postulate" $$> TPP.pretty sig
    Data sig ->
      text "data" <+> TPP.pretty sig
    Record sig ->
      text "record" <+> TPP.pretty sig
    FunDef f clauses ->
      vcat $ map (prettyClause f) clauses
    DataDef d xs cs ->
      (text "data" <+> TPP.pretty d <+> (foldr (<+>) empty $ map TPP.pretty xs) <+> text "where") <$$>
      (vcat (map TPP.pretty cs))
    RecDef r xs con fs ->
      (text "record" <+> TPP.pretty r <+> (foldr (<+>) empty $ map TPP.pretty xs) <+> text "where") <$$>
      text "constructor" <+> TPP.pretty con <$$>
      text "field" <$$>
      vcat (map TPP.pretty fs)
    Module_ m ->
      TPP.pretty m
    Open m ->
      text "open" <+> TPP.pretty m
    Import m args ->
      text "import" <+> TPP.pretty m <+> (foldr (<+>) empty $ map (prettyPrec 4) args)
    where
      prettyClause f (Clause ps (ClauseBody e [])) =
        group (hsep (TPP.pretty f : map TPP.pretty ps ++ ["="]) <+> TPP.pretty e)
      prettyClause f (Clause ps (ClauseBody e wheres)) =
        group (hsep (TPP.pretty f : map TPP.pretty ps ++ ["="]) <+> TPP.pretty e) $$
        PP.indent 2 ("where" $$ PP.indent 2 (vcat (map TPP.pretty wheres)))
      prettyClause f (Clause ps ClauseNoBody) =
        group (hsep (TPP.pretty f : map TPP.pretty ps))

instance TPP.Pretty ClauseBody where
  pretty cb = case cb of
    ClauseNoBody -> "<no body>"
    ClauseBody t wheres -> TPP.pretty t $$ PP.indent 2 ("where" $$ PP.indent 2 (vcat (map TPP.pretty wheres)))

instance TPP.Pretty Head where
  pretty h = case h of
    Var x       -> TPP.pretty x
    Def f       -> TPP.pretty f
    J _         -> text "J"

instance TPP.Pretty Pattern where
  pretty e = case e of
    WildP _   -> text "_"
    VarP x    -> TPP.pretty x
    ConP c es -> PP.parens $ foldr (<+>) empty $ TPP.pretty c : map TPP.pretty es
    EmptyP _  -> text "()"

-- Pretty printing terms
------------------------------------------------------------------------

instance TPP.Pretty Elim where
  prettyPrec p (Apply e) = condParens (p > 0) $ "$" <+> prettyPrec p e
  prettyPrec _ (Proj x)  = "." <+> TPP.pretty x

instance TPP.Pretty Expr where
  prettyPrec p e = case e of
    Set _       -> text "Set"
    Meta _      -> text "_"
    Equal (Meta _) x y ->
      condParens (p > 2) $
        prettyPrec 3 x <+> text "==" <+> prettyPrec 2 y
    Equal a x y -> prettyApp p (text "_==_") [a, x, y]
    Fun a b ->
      condParens (p > 0) $ 
        prettyPrec 1 a <+> text "->" <+> TPP.pretty b
    Pi{} ->
      condParens (p > 0) $ align $
        prettyTel tel <+> text "->" <+> TPP.pretty b
      where
        (tel, b) = piView e
        piView (Pi x a b) = ((x, a) :) *** id $ piView b
        piView a          = ([], a)
    Lam{} ->
      condParens (p > 0) $
      text "\\ " <+> hsep (map TPP.pretty xs) <+> text "->" <+> TPP.pretty b
      where
        (xs, b) = lamView e
        lamView (Lam x b) = (x :) *** id $ lamView b
        lamView e         = ([], e)
    App{} -> prettyApp p (TPP.pretty h) es
      where
        (h, es) = appView e
        appView (App h es) = buildApp h [] es
        appView e = error $ "impossible: pretty application"

        buildApp :: Head -> [Expr] -> [Elim] -> (Head, [Expr])
        buildApp h es0 (Apply e : es1) = buildApp h (es0 ++ [e]) es1
        buildApp h es0 (Proj f  : es1) = buildApp (Def f) [App h $ map Apply es0] es1
        buildApp h es []               = (h, es)
    Refl{} -> text "refl"
    Con c args -> prettyApp p (TPP.pretty c) args

{-
instance Pretty Expr where
  prettyPrec p e = case e of
    Set _       -> text "Set"
    Meta _      -> text "_"
    Equal (Meta _) x y ->
      condParens (p > 2) $
        prettyPrec 3 x <+> text "==" //> prettyPrec 2 y
    Equal a x y -> prettyApp p (text "_==_") [a, x, y]
    Fun a b ->
      condParens (p > 0) $ align $
        prettyPrec 1 a <+> text "->" // pretty b
    Pi{} ->
      condParens (p > 0) $ align $
        prettyTel tel <+> text "->" // pretty b
      where
        (tel, b) = piView e
        piView (Pi x a b) = ((x, a) :) *** id $ piView b
        piView a          = ([], a)
    Lam{} ->
      condParens (p > 0) $
      text "\\ " <> hsep (map pretty xs) <+> text "->" <+> pretty b
      where
        (xs, b) = lamView e
        lamView (Lam x b) = (x :) *** id $ lamView b
        lamView e         = ([], e)
    App{} -> prettyApp p (pretty h) es
      where
        (h, es) = appView e
        appView (App h es) = buildApp h [] es
        appView e = error $ "impossible: pretty application"

        buildApp :: Head -> [Expr] -> [Elim] -> (Head, [Expr])
        buildApp h es0 (Apply e : es1) = buildApp h (es0 ++ [e]) es1
        buildApp h es0 (Proj f  : es1) = buildApp (Def f) [App h $ map Apply es0] es1
        buildApp h es []               = (h, es)
    Refl{} -> text "refl"
    Con c args -> prettyApp p (pretty c) args
-} 

prettyTel :: [(Name, Expr)] -> Doc
prettyTel = group . prs . reverse
  where
    prs []       = empty
    prs [b]      = pr b
    prs (b : bs) = (prs bs) <+> pr b
--    pr (x, e@(Pi )) = braces (pretty x <+> text ":" <+> pretty e)
    pr (x, e) = PP.parens (TPP.pretty x <+> colon <+> TPP.pretty e)

-- Printing declarations as it would be written by the user 
------------------------------------------------------------------------

class TPP.Pretty a => MorePretty a where
  morePretty :: a -> Doc

instance MorePretty Module where
  morePretty (Module name pars exports decls) =
    let parsDoc =
          let ds = [PP.parens (morePretty n <+> colon <+> morePretty ty) | (n, ty) <- pars]
          in if null ds then empty else foldr (<+>) empty ds 
    in (text "module" <+> morePretty name <+> parsDoc <+> text "where") PP.<$$>
       (PP.indent 2 (vcat (map morePretty decls))) 

instance MorePretty TypeSig where
  morePretty (Sig n e) =
   morePretty n <+> text ":" <+> TPP.pretty e

instance MorePretty Name where
  morePretty (Name _ str) = text str  
  
instance MorePretty QName where
  morePretty (QName n qn) = morePretty n 

instance MorePretty Head where
  morePretty (Var n) = morePretty n
  morePretty (Def qn) = morePretty qn
  morePretty (J srcloc) = text "J" 


instance MorePretty Expr where
--  morePretty (App head elim) = morePretty head <> morePretty elim 
  morePretty = TPP.pretty

instance MorePretty Elim where
  morePretty (Proj x) = morePretty x
  morePretty elim = TPP.pretty elim 
  
instance MorePretty Decl where  
  morePretty d = case d of
    Record ts -> text "record" <+> headerTypeSig ts <+> text "where"
    RecDef r xs con fs ->
      PP.indent 2 $ 
      (align (vsep [text "constructor" <+> morePretty con, text "field"])) PP.<$$>
      (PP.indent 2 $ PP.vsep (map morePretty fs))
    Data ts -> text "data" <+> headerTypeSig ts <+> text "where"
    DataDef qn ns tys ->
      PP.indent 2 $
      vcat (map morePretty tys) 
    Module_ m -> morePretty m
    Import _ _ -> empty  
    _ -> TPP.pretty d
   where
    headerTypeExpr e = case e of
     Pi{} -> 
       prettyTel tel <+> colon <+> TPP.pretty b
      where
        (tel, b) = piView e
        piView (Pi x a b) = ((x, a) :) *** id $ piView b
        piView a          = ([], a)
     _ -> colon <+> TPP.pretty e 
    headerTypeSig (Sig n e) =
      morePretty n <+> headerTypeExpr e

