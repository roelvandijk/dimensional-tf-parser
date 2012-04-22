{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE PackageImports      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE UnicodeSyntax       #-}

module Numeric.Units.Dimensional.TF.Parser where

--------------------------------------------------------------------------------
-- Imports
--------------------------------------------------------------------------------

import "base" Control.Applicative ( Applicative, pure, liftA2
                                  , (<*>), (<*), (*>), (<|>)
                                  )
import qualified "base" Control.Arrow as Arr ( second )
import "base" Control.Monad ( return, (=<<), sequence )
import "base" Data.Bool     ( Bool(False, True), not )
import "base" Data.Char     ( Char, isSpace )
import "base" Data.Either   ( Either(Left, Right), either )
import "base" Data.Eq       ( Eq )
import "base" Data.Function ( ($), id )
import "base" Data.Functor  ( Functor, fmap, (<$>), (<$) )
import "base" Data.Int      ( Int )
import "base" Data.List     ( (++), map, foldl', foldr, null, concat, concatMap
                            , filter, find, intercalate, dropWhile, break
                            , genericReplicate
                            )
import "base" Data.Maybe    ( Maybe(Nothing, Just), maybe )
import "base" Data.Ord      ( Ord )
import "base" Data.String   ( String )
import "base" Data.Tuple    ( fst, snd, uncurry )
import "base" Prelude
    ( Num, Fractional, Floating, Double
    , (+), (-), (*), (/), (^^)
    , error, abs, signum, negate, fromInteger, fromIntegral
    , asTypeOf
    )
import "base" Text.Read     ( Read, reads, lex )
import "base" Text.Show     ( Show, show )
import "base-unicode-symbols" Data.Bool.Unicode     ( (∧) )
import "base-unicode-symbols" Data.Eq.Unicode       ( (≡), (≢) )
import "base-unicode-symbols" Data.Function.Unicode ( (∘) )
import "base-unicode-symbols" Prelude.Unicode       ( ℤ, ℚ, (⊥), (⋅) )
import "containers" Data.Map ( Map )
import qualified "containers" Data.Map as Map
    ( empty, assocs, findWithDefault, map, insert, insertWith, unionWith )
import qualified "dimensional-tf" Numeric.Units.Dimensional.TF as Dim -- ( (*) )
import "dimensional-tf" Numeric.Units.Dimensional.TF
    ( (*~), Quantity, Unit, Dim, prefix
    , DOne, one, DLength, DMass, DTime, DElectricCurrent
    , DThermodynamicTemperature, DAmountOfSubstance, DLuminousIntensity
    )
import "dimensional-tf" Numeric.Units.Dimensional.TF.SIUnits
import "dimensional-tf" Numeric.Units.Dimensional.TF.NonSI
import "mtl" Control.Monad.Error.Class ( MonadError, throwError )
import "numtype-tf" Numeric.NumType.TF
    ( NumType, Zero, toNum, pos1, pos2, pos3, pos4, neg1, neg2, neg3
    , Abs, Add, Mul, Z(Z), S(S), N(N), Succ
    )
import "parsec" Text.Parsec.Char       ( char, letter, oneOf, string )
import "parsec" Text.Parsec.Combinator ( many1, eof, choice )
import "parsec" Text.Parsec.Error
    ( ParseError, Message(Message), newErrorMessage )
import "parsec" Text.Parsec.Expr
    ( Assoc(AssocLeft, AssocRight), Operator(Infix), OperatorTable
    , buildExpressionParser
    )
import "parsec" Text.Parsec.Language ( emptyDef )
import "parsec" Text.Parsec.Pos      ( initialPos )
import "parsec" Text.Parsec.Prim
    ( Parsec, parse, (<?>), try )
import qualified "parsec" Text.Parsec.Token as P
import "transformers" Data.Functor.Identity ( Identity )


-- DEBUG
-- import Prelude
-- import System.IO ( IO )
-- import Text.Printf ( printf )


--------------------------------------------------------------------------------
-- Products of powers of dimensions.
--------------------------------------------------------------------------------

-- | A 7-tuple containing the powers of the 7 base SI dimensions.
data DimPows α = DimPows
                 { dpLength                   ∷ α
                 , dpMass                     ∷ α
                 , dpTime                     ∷ α
                 , dpElectricCurrent          ∷ α
                 , dpThermodynamicTemperature ∷ α
                 , dpAmountOfSubstance        ∷ α
                 , dpLuminousIntensity        ∷ α
                 }
               deriving (Eq, Ord, Show)

instance Functor DimPows where
    fmap f (DimPows l m t i th n j) =
        DimPows (f l) (f m) (f t) (f i) (f th) (f n) (f j)

instance Applicative DimPows where
    pure x = DimPows x x x x x x x
    (DimPows fl fm ft fi fth fn fj) <*> (DimPows l m t i th n j) =
        DimPows (fl l) (fm m) (ft t) (fi i) (fth th) (fn n) (fj j)

-- | A dimension is made an instance of 'Num' by applying all operations
-- elementwise to each of the 7 numerical powers.
instance (Num α) ⇒ Num (DimPows α) where
    (+)         = liftA2 (+)
    (*)         = liftA2 (*)
    (-)         = liftA2 (-)
    negate      = fmap negate
    abs         = fmap abs
    signum      = fmap signum
    fromInteger = pure ∘ fromInteger

-- | Pretty representation of a dimension.
--
-- See also: NIST Special Publication 330, 2008 Edition: The International
-- System of Units (SI), Section 1.3: Dimensions of Quantities
prettyDimPows ∷ ∀ α. (Eq α, Num α, Show α) ⇒ DimPows α → String
prettyDimPows (DimPows 0 0 0 0 0  0 0) = "dimensionless"
prettyDimPows (DimPows l m t i th n j) =
    concat $ filter (not ∘ null)
                    [ f l "L"
                    , f m "M"
                    , f t "T"
                    , f i "I"
                    , f th "Θ"
                    , f n "N"
                    , f j "J"
                    ]
  where
    f ∷ α → String → String
    f 0 _ = ""
    f e sym = sym ++ map super (show e)

    super ∷ Char → Char
    super '-' = '⁻'
    super '0' = '⁰'
    super '1' = '¹'
    super '2' = '²'
    super '3' = '³'
    super '4' = '⁴'
    super '5' = '⁵'
    super '6' = '⁶'
    super '7' = '⁷'
    super '8' = '⁸'
    super '9' = '⁹'
    super c = c

--------------------------------------------------------------------------------
-- Language of Physical Units
--------------------------------------------------------------------------------

data UnitExpParsed =
      UENameP String (DimPows ℤ)
    | UEPrefixP ℚ UnitExpParsed
    | UEIntP ℤ
    | UEMulP UnitExpParsed UnitExpParsed
    | UEDivP UnitExpParsed UnitExpParsed
    | UEPowP UnitExpParsed UnitExpParsed
      deriving Show

data UnitExp =
      UEName String (DimPows ℤ)
    | UEPrefix ℚ UnitExp
    | UEMul UnitExp UnitExp
    | UEDiv UnitExp UnitExp
    | UEPow UnitExp ℤ
      deriving (Eq, Show)

infixr 8 `UEPowP`, `UEPow`
infixl 7 `UEMulP`, `UEMul`
infixl 7 `UEDivP`, `UEDiv`

unitExpDimPows ∷ UnitExp → (DimPows ℤ)
unitExpDimPows = go
  where
    go (UEName _ d) = d
    go (UEPrefix _ x) = go x
    go (UEMul x y) = go x + go y
    go (UEDiv x y) = go x - go y
    go (UEPow x i) = go x ⋅ fromInteger i

convertParsedExp ∷ UnitExpParsed → Maybe UnitExp
convertParsedExp = go
  where
    go (UENameP n dim)       = Just $ UEName n dim
    go (UEPrefixP pf x)      = UEPrefix pf <$> go x
    go (UEIntP _)            = Nothing
    go (UEMulP x y)          = UEMul <$> go x <*> go y
    go (UEDivP x y)          = UEDiv <$> go x <*> go y
    go (UEPowP x (UEIntP i)) = (`UEPow` i) <$> go x
    go (UEPowP _ _)          = Nothing


--------------------------------------------------------------------------------
-- Lexer
--------------------------------------------------------------------------------

unitDef ∷ P.LanguageDef st
unitDef = emptyDef
          { P.commentStart    = ""
          , P.commentEnd      = ""
          , P.commentLine     = ""
          , P.nestedComments  = False
          , P.identStart      = P.identLetter unitDef
          , P.identLetter     = letter
          , P.opStart         = P.opLetter unitDef
          , P.opLetter        = oneOf ['*', '·', '/', '^']
          , P.reservedNames   = []
          , P.reservedOpNames = []
          , P.caseSensitive   = True
          }

lexer ∷ P.GenTokenParser String u Identity
lexer = P.makeTokenParser unitDef


--------------------------------------------------------------------------------
-- Unit parser
--------------------------------------------------------------------------------

parseUnitExp ∷ String → Either ParseError UnitExp
parseUnitExp str =
    case parse (unitExp <* eof) "" str of
      Left err → Left err
      Right uer →
        case convertParsedExp uer of
          Just ue → Right ue
          Nothing → Left $ newErrorMessage (Message "Illegal expression")
                                           (initialPos "")

unitExp ∷ Parsec String () UnitExpParsed
unitExp = buildExpressionParser table term
  where
    table ∷ OperatorTable String () Identity UnitExpParsed
    table = [ [ binOp "^" UEPowP AssocRight ]
            , [ binOp "*" UEMulP AssocLeft
              , binOp "·" UEMulP AssocLeft
              , binOp "/" UEDivP AssocLeft
              ]
            ]

    term ∷ Parsec String () UnitExpParsed
    term = (P.parens lexer unitExp)
         <|> try (UEPowP <$> unitTerm <*> unitSuperExp)
         <|> P.lexeme lexer unitTerm
         <|> UEIntP <$> P.integer lexer

-- [prefix_name] unit_name | [prefix_symbol] unit_symbol
unitTerm ∷ Parsec String () UnitExpParsed
unitTerm = try onlyNames <|> onlySymbols
  where
    onlyNames   =   try (unit siPrefixNames (filterUnits UName True))
                <|> try (unit siPrefixNames (filterDerivedUnits UName))
                <|> unitName (filterUnits UName False)

    onlySymbols =   try (unit siPrefixSymbols (filterUnits USymbol True))
                <|> try (unit siPrefixSymbols (filterDerivedUnits USymbol))
                <|> unitName (filterUnits USymbol False)

    unit prefixTable unitTable =
        try (prefixedUnit prefixTable unitTable)
        <|> unitName unitTable

    prefixedUnit prefixTable unitTable = UEPrefixP <$> prefixTerm prefixTable <*> unitName unitTable
    prefixTerm tab = choice $ map (try ∘ (\(s, x) → string s *> pure x)) tab
    unitName tab = uncurry UENameP <$> choice (map (\t → try (string (fst t) *> pure t)) tab)

unitSuperExp ∷ Parsec String () UnitExpParsed
unitSuperExp = UEIntP <$> (P.lexeme lexer superDecimal <?> "superscript decimal")

binOp ∷ String → (α → α → α) → Assoc → Operator String () Identity α
binOp name fun assoc = Infix (P.reservedOp lexer name *> pure fun) assoc

superDecimal ∷ (Num α) ⇒ Parsec String () α
superDecimal =
  superSign <*> (foldl' (\x d → 10⋅x + d) 0 <$> many1 superDigit)

superDigit ∷ (Num α) ⇒ Parsec String () α
superDigit = choice
             [ 0 <$ char '⁰'
             , 1 <$ char '¹'
             , 2 <$ char '²'
             , 3 <$ char '³'
             , 4 <$ char '⁴'
             , 5 <$ char '⁵'
             , 6 <$ char '⁶'
             , 7 <$ char '⁷'
             , 8 <$ char '⁸'
             , 9 <$ char '⁹'
             ]

superSign ∷ (Num α) ⇒ Parsec String () (α → α)
superSign =   (char '⁻' *> pure negate)
          <|> (char '⁺' *> pure id)
          <|> pure id


--------------------------------------------------------------------------------
-- SI prefixes
--------------------------------------------------------------------------------

dec ∷ (Fractional α) ⇒ ℤ → α
dec = (10 ^^)

siPrefixNames ∷ (Fractional α) ⇒ [(String, α)]
siPrefixNames =
  [ ("yotta", dec   24)
  , ("zetta", dec   21)
  , ("exa",   dec   18)
  , ("peta",  dec   15)
  , ("tera",  dec   12)
  , ("giga",  dec    9)
  , ("mega",  dec    6)
  , ("kilo",  dec    3)
  , ("hecto", dec    2)
  , ("deca",  dec    1)
  , ("deka",  dec    1)
  , ("deci",  dec (- 1))
  , ("centi", dec (- 2))
  , ("milli", dec (- 3))
  , ("micro", dec (- 6))
  , ("nano",  dec (- 9))
  , ("pico",  dec (-12))
  , ("femto", dec (-15))
  , ("atto",  dec (-18))
  , ("zepto", dec (-21))
  , ("yocto", dec (-24))
  ]

siPrefixSymbols ∷ (Fractional α) ⇒ [(String, α)]
siPrefixSymbols =
  [ ("Y",  dec   24)
  , ("Z",  dec   21)
  , ("E",  dec   18)
  , ("P",  dec   15)
  , ("T",  dec   12)
  , ("G",  dec    9)
  , ("M",  dec    6)
  , ("k",  dec    3)
  , ("h",  dec    2)
  , ("da", dec    1)
  , ("d",  dec (- 1))
  , ("c",  dec (- 2))
  , ("m",  dec (- 3))
  , ("μ",  dec (- 6))
  , ("n",  dec (- 9))
  , ("p",  dec (-12))
  , ("f",  dec (-15))
  , ("a",  dec (-18))
  , ("z",  dec (-21))
  , ("y",  dec (-24))
  ]


--------------------------------------------------------------------------------
-- Unit definitions (SI & other)
--------------------------------------------------------------------------------

data UnitKind = UName | USymbol deriving (Eq, Show)
data UnitEntry dim α =
    UE { ueUnit          ∷ Unit dim α
       , ueKind          ∷ UnitKind
       , ueName          ∷ String
       , ueAllowSIPrefix ∷ Bool
       }
data DerivedUnitEntry =
    DUE { dueKind       ∷ UnitKind
        , dueName       ∷ String
        , dueDerivation ∷ UnitExp
        }

dimensionlessUnits ∷ (Floating α) ⇒ [UnitEntry DOne α]
dimensionlessUnits =
  [ UE one         UName   "revolution"  False
  , UE one         UName   "solid"       False
  , UE degree      UName   "degree"      False
  , UE degree      USymbol "°"           False
  , UE arcminute   UName   "arcminute"   False
  , UE arcminute   USymbol "'"           False
  , UE arcsecond   UName   "arcsecond"   False
  , UE arcsecond   USymbol "\""          False
  , UE degreeOfArc UName   "degreeOfArc" False
  , UE secondOfArc UName   "secondOfArc" False
  , UE minuteOfArc UName   "minuteOfArc" False
  ]

lengthUnits ∷ (Floating α) ⇒ [UnitEntry DLength α]
lengthUnits =
  [ UE metre        UName   "metre"         True
  , UE metre        USymbol "m"             True
  , UE metre        UName   "meter"         True
  , UE foot         UName   "foot"          False
  , UE inch         UName   "inch"          False
  , UE yard         UName   "yard"          False
  , UE mile         UName   "mile"          False
  , UE nauticalMile UName   "nauticalMile"  False
  , UE metre        UName   "ångström"      True
  , UE (prefix (dec (-10)) metre) USymbol "Å" True
  ]

massUnits ∷ (Floating α) ⇒ [UnitEntry DMass α]
massUnits =
  [ UE gram      UName   "gram"       True
  , UE gram      USymbol "g"          True
  , UE poundMass UName   "poundMass"  False
  , UE tonne     UName   "tonne"      False
  , UE tonne     USymbol "T"          False
  , UE metricTon UName   "metric ton" False
  ]

timeUnits ∷ (Floating α) ⇒ [UnitEntry DTime α]
timeUnits =
  [ UE second  UName   "second"  True
  , UE second  USymbol "s"       True
  , UE minute  UName   "minute"  False
  , UE minute  USymbol "min"     False
  , UE hour    UName   "hour"    False
  , UE hour    USymbol "h"       False
  , UE day     UName   "day"     False
  , UE day     USymbol "d"       False
  , UE year    UName   "year"    False
  , UE century UName   "century" False
  ]

electricCurrentUnits ∷ (Floating α) ⇒ [UnitEntry DElectricCurrent α]
electricCurrentUnits =
  [ UE ampere UName   "ampere" True
  , UE ampere USymbol "A"      True
  ]

thermodynamicTemperatureUnits ∷ (Floating α) ⇒ [UnitEntry DThermodynamicTemperature α]
thermodynamicTemperatureUnits =
  [ UE kelvin UName   "kelvin" True
  , UE kelvin USymbol "K"      True
  ]

amountOfSubstanceUnits ∷ (Floating α) ⇒ [UnitEntry DAmountOfSubstance α]
amountOfSubstanceUnits =
  [ UE mole UName   "mole" True
  , UE mole USymbol "mol"  True
  ]

luminousIntensityUnits ∷ (Floating α) ⇒ [UnitEntry DLuminousIntensity α]
luminousIntensityUnits =
  [ UE candela UName   "candela" True
  , UE candela USymbol "cd"      True
  ]

filterUnits ∷ UnitKind → Bool → [(String, DimPows ℤ)]
filterUnits unitKind allowPrefix =
    concat [ map extract $ filter pred dimensionlessUnits
           , map extract $ filter pred amountOfSubstanceUnits
           , map extract $ filter pred timeUnits
           , map extract $ filter pred lengthUnits
           , map extract $ filter pred massUnits
           , map extract $ filter pred electricCurrentUnits
           , map extract $ filter pred thermodynamicTemperatureUnits
           , map extract $ filter pred luminousIntensityUnits
           ]
  where
    pred ∷ UnitEntry dim α → Bool
    pred ue = ueKind          ue ≡ unitKind
             ∧ ueAllowSIPrefix ue ≡ allowPrefix
    extract ue = (ueName ue, uDimPows $ ueUnit ue)

filterDerivedUnits ∷ UnitKind → [(String, DimPows ℤ)]
filterDerivedUnits unitKind =
    map (\due → (dueName due, unitExpDimPows $ dueDerivation due))
    $ filter ((unitKind ≡) ∘ dueKind) derivedUnits

baseUnitNames = filterUnits UName True ++ filterUnits UName False
baseUnitSymbols = filterUnits USymbol True ++ filterUnits USymbol False

unsafePUE ∷ String → UnitExp
unsafePUE = either (error ∘ show) id ∘ parseUnitExp

derivedUnits ∷ [DerivedUnitEntry]
derivedUnits =
  [ DUE UName "radian"    $ unsafePUE "metre / metre"
  , DUE UName "steradian" $ unsafePUE "metre² / metre²"
  , DUE UName "hertz"     $ unsafePUE "second⁻¹"
  , DUE UName "newton"    $ unsafePUE "metre · kilogram · second⁻²"
  , DUE UName "pascal"    $ unsafePUE "metre⁻¹ · kilogram · second⁻²"
  , DUE UName "joule"     $ unsafePUE "metre² · kilogram · second⁻²"
  , DUE UName "watt"      $ unsafePUE "metre² · kilogram · second⁻³"
  , DUE UName "coulomb"   $ unsafePUE "second · ampere"
  , DUE UName "volt"      $ unsafePUE "metre² · kilogram · second⁻³ · ampere⁻¹"
  , DUE UName "farad"     $ unsafePUE "metre⁻² · kilogram⁻¹ · second⁴ · ampere²"
  , DUE UName "ohm"       $ unsafePUE "metre² · kilogram · second⁻³ · ampere⁻²"
  , DUE UName "siemens"   $ unsafePUE "metre⁻² · kilogram⁻¹ · second³ · ampere²"
  , DUE UName "weber"     $ unsafePUE "metre² · kilogram · second⁻² · ampere⁻¹"
  , DUE UName "tesla"     $ unsafePUE "kilogram · second⁻² · ampere⁻¹"
  , DUE UName "henry"     $ unsafePUE "metre² · kilogram · second⁻² · ampere⁻²"
  , DUE UName "degree Celsius" $ unsafePUE "kelvin"
  , DUE UName "lumen"     $ unsafePUE "candela"
  , DUE UName "lux"       $ unsafePUE "metre² · candela"
  , DUE UName "becquerel" $ unsafePUE "second⁻¹"
  , DUE UName "gray"      $ unsafePUE "metre² · second⁻²"
  , DUE UName "sievert"   $ unsafePUE "metre² · second⁻²"
  , DUE UName "katal"     $ unsafePUE "second⁻¹ · mole"
  , DUE USymbol "rad"     $ unsafePUE "m / m"
  , DUE USymbol "sr"      $ unsafePUE "m² / m²"
  , DUE USymbol "Hz"      $ unsafePUE "s⁻¹"
  , DUE USymbol "N"       $ unsafePUE "m · kg · s⁻²"
  , DUE USymbol "Pa"      $ unsafePUE "m⁻¹ · kg · s⁻²"
  , DUE USymbol "J"       $ unsafePUE "m² · kg · s⁻²"
  , DUE USymbol "W"       $ unsafePUE "m² · kg · s⁻³"
  , DUE USymbol "C"       $ unsafePUE "s · A"
  , DUE USymbol "V"       $ unsafePUE "m² · kg · s⁻³ · A⁻¹"
  , DUE USymbol "F"       $ unsafePUE "m⁻² · kg⁻¹ · s⁴ · A²"
  , DUE USymbol "Ω"       $ unsafePUE "m² · kg · s⁻³ · A⁻²"
  , DUE USymbol "S"       $ unsafePUE "m⁻² · kg⁻¹ · s³ · A²"
  , DUE USymbol "Wb"      $ unsafePUE "m² · kg · s⁻² · A⁻¹"
  , DUE USymbol "T"       $ unsafePUE "kg · s⁻² · A⁻¹"
  , DUE USymbol "H"       $ unsafePUE "m² · kg · s⁻² · A⁻²"
  , DUE USymbol "℃"       $ unsafePUE "K"
  , DUE USymbol "°C"      $ unsafePUE "K"
  , DUE USymbol "lm"      $ unsafePUE "cd"
  , DUE USymbol "lx"      $ unsafePUE "m⁻² · cd"
  , DUE USymbol "Bq"      $ unsafePUE "s⁻¹"
  , DUE USymbol "Gy"      $ unsafePUE "m² · s⁻²"
  , DUE USymbol "Sv"      $ unsafePUE "m² · s⁻²"
  , DUE USymbol "kat"     $ unsafePUE "s⁻¹ · mol"
  ]

-- | Removes all subprefixes and calculates the combined prefix value of the
-- expression.
normalisePrefix ∷ UnitExp → (ℚ, UnitExp)
normalisePrefix n@(UEName _ _) = (1, n)
normalisePrefix (UEPrefix px x) =
    let (p, x') = normalisePrefix x
    in (p ⋅ px, x')
normalisePrefix (UEMul x y) =
    let (px, x') = normalisePrefix x
        (py, y') = normalisePrefix y
    in (px ⋅ py, UEMul x' y')
normalisePrefix (UEDiv x y) =
    let (px, x') = normalisePrefix x
        (py, y') = normalisePrefix y
    in (px / py, UEDiv x' y')
normalisePrefix (UEPow x i) =
    let (px, x') = normalisePrefix x
    in (px ^^ i, UEPow x' i)

-- | Replaces derived units with equivalent expressions using only base SI
-- units.
toBase ∷ UnitExp → UnitExp
toBase ueName@(UEName n _) = maybe ueName id derivation
 where
   derivation ∷ Maybe UnitExp
   derivation = dueDerivation <$> find ((n ≡) ∘ dueName) derivedUnits
toBase (UEPrefix p x) = UEPrefix p (toBase x)
toBase (UEMul x y) = UEMul (toBase x) (toBase y)
toBase (UEDiv x y) = UEDiv (toBase x) (toBase y)
toBase (UEPow x i) = UEPow (toBase x) i

-- | Replaces all divisions with combinations of multiplications and
-- powers. (m/s = m·s⁻¹)
toMulForm ∷ UnitExp → UnitExp
toMulForm n@(UEName _ _) = n
toMulForm (UEPrefix p x) = UEPrefix p (toMulForm x)
toMulForm (UEMul x y) = UEMul (toMulForm x) (toMulForm y)
toMulForm (UEDiv x y) = UEMul (toMulForm x) (UEPow (toMulForm y) (negate 1))
toMulForm (UEPow x i) = UEPow (toMulForm x) i

-- | Extract a list of units and their exponents
-- (m·s⁻¹)² = [m², s⁻²]
extractUnits ∷ UnitExp → Either String [((String, DimPows ℤ), ℤ)]
extractUnits ue = filter ((0 ≢) ∘ snd) <$> Map.assocs <$> go ue
  where
    go ∷ UnitExp → Either String (Map (String, DimPows ℤ) ℤ)
    go (UEName n d)   = pure $ Map.insert (n, d) 1 Map.empty
    go (UEMul x y)    = Map.unionWith (+) <$> go x <*> go y
    go (UEPow x n)    = Map.map (⋅ n) <$> go x
    go (UEPrefix _ _) = throwError "extractUnits: can't deal with prefixes"
    go (UEDiv _ _)    = throwError "extractUnits: can't deal with division"

-- Copied from safe-0.3.3 by Neil Mitchell.
readMay ∷ (Read α) ⇒ String → Maybe α
readMay s = case [x | (x,t) ← reads s, ("", "") ← lex t] of
                [x] → Just x
                _   → Nothing

lookupUnit ∷ String → [UnitEntry dim α] → Maybe (Unit dim α)
lookupUnit n = fmap ueUnit ∘ find ((n ≡) ∘ ueName)

-- | Group units by dimension.
groupUnits ∷ [((String, DimPows ℤ), ℤ)] → Map (DimPows ℤ) [(String, ℤ)]
groupUnits = foldr (\((n, d), p) m → Map.insertWith (++) d [(n, p)] m) Map.empty

mulUnitsV ∷ (Num α)
          ⇒ V x (Unit (Dim l m t i th n j) α)
          → Unit (Dim (Mul x l)
                       (Mul x m)
                       (Mul x t)
                       (Mul x i)
                       (Mul x th)
                       (Mul x n)
                       (Mul x j)
                  )
                  α
mulUnitsV Nil = error "empty vector"
mulUnitsV (Cons u Nil) = u
mulUnitsV (Cons u us)  = u Dim.* mulUnitsV us

mulUnits ∷ ∀ α x l m t i th n j
         . (Num α, Nat x)
         ⇒ x
         → [Unit (Dim l m t i th n j) α]
         → Maybe (Unit (Dim (Mul x l)
                             (Mul x m)
                             (Mul x t)
                             (Mul x i)
                             (Mul x th)
                             (Mul x n)
                             (Mul x j)
                        )
                        α
                  )
mulUnits _ xs = mulUnitsV
                <$> (vecFromList xs ∷ Maybe (V x (Unit (Dim l m t i th n j) α)))

{-
parseUnit ∷ ∀ l m t i th n j α
          . ( NumType l,  NumType m, NumType t, NumType i
            , NumType th, NumType n, NumType j
            , Num α
            )
          ⇒ String
          → Either String (Unit (Dim l m t i th n j) α)
parseUnit unitStr = do
    unitExp ← either (Left ∘ show) Right $ parseUnitExp unitStr

    let (p, e) = normalisePrefix $ toMulForm $ toBase unitExp

    unitDimMap ← groupUnits <$> extractUnits e

    let os  = Map.findWithDefault [] (DimPows 0 0 0 0 0 0 0) unitDimMap
        ls  = Map.findWithDefault [] (DimPows 1 0 0 0 0 0 0) unitDimMap
        ms  = Map.findWithDefault [] (DimPows 0 1 0 0 0 0 0) unitDimMap
        ts  = Map.findWithDefault [] (DimPows 0 0 1 0 0 0 0) unitDimMap
        is  = Map.findWithDefault [] (DimPows 0 0 0 1 0 0 0) unitDimMap
        ths = Map.findWithDefault [] (DimPows 0 0 0 0 1 0 0) unitDimMap
        ns  = Map.findWithDefault [] (DimPows 0 0 0 0 0 1 0) unitDimMap
        js  = Map.findWithDefault [] (DimPows 0 0 0 0 0 0 1) unitDimMap

    let os'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n dimensionlessUnits)            os
        ls' ∷ (Floating α) ⇒ Maybe [(Unit DLength α, ℤ)]
        ls'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n lengthUnits)                   ls
        ms'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n massUnits)                     ms
        ts'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n timeUnits)                     ts
        is'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n electricCurrentUnits)          is
        ths' = sequence $ map (\(n, x) → (,x) <$> lookupUnit n thermodynamicTemperatureUnits) ths
        ns'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n amountOfSubstanceUnits)        ns

    let foo_ls ∷ Maybe (Unit (Dim l Zero Zero Zero Zero Zero Zero) α)
        foo_ls = mulUnits ((⊥) ∷ Abs l) =<< ls'

    let oneUnit                      ∷ Unit (Dim Zero Zero Zero Zero Zero Zero Zero) α
        lengthUnit                   ∷ Unit (Dim l    Zero Zero Zero Zero Zero Zero) α
        massUnit                     ∷ Unit (Dim Zero m    Zero Zero Zero Zero Zero) α
        timeUnit                     ∷ Unit (Dim Zero Zero t    Zero Zero Zero Zero) α
        electricCurrentUnit          ∷ Unit (Dim Zero Zero Zero i    Zero Zero Zero) α
        thermodynamicTemperatureUnit ∷ Unit (Dim Zero Zero Zero Zero th   Zero Zero) α
        amountOfSubstanceUnit        ∷ Unit (Dim Zero Zero Zero Zero Zero n    Zero) α
        luminousIntensityUnit        ∷ Unit (Dim Zero Zero Zero Zero Zero Zero j   ) α
        oneUnit                      = (⊥)
        lengthUnit                   = (⊥)
        massUnit                     = (⊥)
        timeUnit                     = (⊥)
        electricCurrentUnit          = (⊥)
        thermodynamicTemperatureUnit = (⊥)
        amountOfSubstanceUnit        = (⊥)
        luminousIntensityUnit        = (⊥)

    return $ (     oneUnit
             Dim.* lengthUnit
             Dim.* massUnit
             Dim.* timeUnit
             Dim.* electricCurrentUnit
             Dim.* thermodynamicTemperatureUnit
             Dim.* amountOfSubstanceUnit
             Dim.* luminousIntensityUnit
             )

parseQuantity ∷ ∀ l m t i th n j α
              . ( NumType l,  NumType m, NumType t, NumType i
                , NumType th, NumType n, NumType j
                , Read α, Num α
                )
              ⇒ String
              → Either String (Quantity (Dim l m t i th n j) α)
parseQuantity str = do
    val ← maybe (throwError "Can't parse value") pure $ readMay valStr
    case parseUnit unitStr of
      Left err → Left err
      Right unit → Right $ val *~ unit
  where
    (valStr, unitStr) = Arr.second (dropWhile isSpace) $ break isSpace str
-}

--------------------------------------------------------------------------------
-- Vector with length encoded in its type
--------------------------------------------------------------------------------

data V n α where
  Nil ∷ V Zero α
  Cons ∷ α → V n α → V (S n) α

infixr 2 `Cons`

newtype FromList a n = FromList {unFromList ∷ [a] → Maybe (V n a)}
vecFromList ∷ ∀ a n. Nat n ⇒ [a] → Maybe (V n a)
vecFromList = unFromList
            $ induction (witnessNat ∷ n)
                        (FromList fl0)
                        (FromList ∘ flS ∘ unFromList)
  where
    fl0 [] = Just Nil
    fl0 _  = Nothing

    flS k [] = Nothing
    flS k (x:xs) = Cons x <$> k xs

newtype ToList a n = ToList { unToList ∷ V n a → [a] }
vecToList ∷ ∀ n a. Nat n ⇒ V n a → [a]
vecToList = unToList
          $ induction (witnessNat ∷ n)
                      (ToList tl0)
                      (ToList ∘ tlS ∘ unToList)
  where
    tl0 ∷ V Z a → [a]
    tl0 Nil = []
    tlS ∷ ∀ x. Nat x ⇒ (V x a → [a]) → V (S x) a → [a]
    tlS f (Cons x xs) = x : f xs


--------------------------------------------------------------------------------
-- Induction on natural numbers
--------------------------------------------------------------------------------

class Nat n where
   caseNat ∷ ∀ r. n → (n ~ Z ⇒ r) → (∀ p. (n ~ S p, Nat p) ⇒ p → r) → r
instance Nat Z where
   caseNat _ z _ = z
instance Nat n => Nat (S n) where
   caseNat (S n) _ s = s n

induction ∷ ∀ p n. Nat n ⇒ n → p Z → (∀ x. Nat x ⇒ p x → p (S x)) → p n
induction n z s = caseNat n isZ isS where
   isZ ∷ n ~ Z ⇒ p n
   isZ = z

   isS ∷ ∀ x. (n ~ S x, Nat x) ⇒ x → p n
   isS x = s (induction x z s)

newtype Witness x = Witness {unWitness ∷ x}
witnessNat ∷ ∀ n. Nat n ⇒ n
witnessNat = theWitness
  where
    theWitness = unWitness
               $ induction ((⊥) `asTypeOf` theWitness)
                           (Witness Z)
                           (Witness ∘ S ∘ unWitness)


--------------------------------------------------------------------------------
-- Utils
--------------------------------------------------------------------------------

uDimPows ∷ ∀ l m t i th n j α β
         . ( NumType l,  NumType m, NumType t, NumType i
           , NumType th, NumType n, NumType j
           , Num β
           )
         ⇒ Unit (Dim l m t i th n j) α → DimPows β
uDimPows _ =
    DimPows (toNum ((⊥) ∷ l))
            (toNum ((⊥) ∷ m))
            (toNum ((⊥) ∷ t))
            (toNum ((⊥) ∷ i))
            (toNum ((⊥) ∷ th))
            (toNum ((⊥) ∷ n))
            (toNum ((⊥) ∷ j))

decodeRLE ∷ [(α, ℤ)] → [α]
decodeRLE = concatMap (\(x, n) → genericReplicate n x)


--------------------------------------------------------------------------------
-- Debug
--------------------------------------------------------------------------------

-- test ∷ String → IO ()
-- test str = printf "%s\nPrefix: %s\n  %s\n"
--                   (show d)
--                   (show p)
--                   (intercalate "\n  " $ map show us)
--   where
--     us = either error id $ extractUnits e
--     d = unitExpDimPows e
--     (p, e) = normalisePrefix $ toMulForm $ toBase $ unsafePUE str
