{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ViewPatterns               #-}

module BoundedN
  ( -- don't export the constructor, so clients can't create out-of-range values
    BoundedN, 𝕎, pattern 𝕎, pattern 𝕎', pattern W, pattern W'
  , checkBoundedN, checkBoundedN', 𝕨
  , add, (⨹), subtract, sub, (⨺), multiply, mult, (⨻), product, (⨴), (⨵)
  , divide, (⫽) , divModulo, divModuloProxy, divModuloP, divM, divMP
  , modulo, moduloN, moduloProxy, moduloP, moduloProxyN, moduloPN
  , rounded, (⦼)

  , tests
  )
where

import Prelude  ( Bounded, Enum( pred, succ ), Integer, Integral( toInteger )
                , Num
                , (+), (-), (*)
                , div, divMod, enumFrom, enumFromThen, enumFromThenTo
                , enumFromTo, error, fromEnum, fromInteger, fromIntegral
                , maxBound, minBound, toEnum, toInteger
                )

-- base --------------------------------

import Control.Exception  ( Exception )
import Control.Monad      ( return )
import Data.Bifunctor     ( bimap )
import Data.Bool          ( not, otherwise )
import Data.Either        ( Either( Right ), either )
import Data.Eq            ( Eq )
import Data.Function      ( ($), const, flip, id )
import Data.Maybe         ( Maybe( Just, Nothing ) )
import Data.Ord           ( Ord, (<) )
import Data.Proxy         ( Proxy( Proxy ) )
import Data.String        ( String )
import Data.Typeable      ( Typeable )
import GHC.Generics       ( Generic )
import GHC.TypeNats       ( KnownNat, Nat, type(+), type(*), natVal )
import System.Exit        ( ExitCode )
import System.IO          ( IO )
import Text.Read          ( Read )
import Text.Show          ( Show( show ) )

-- base-unicode-symbols ----------------

import Data.Bool.Unicode        ( (∧) )
import Data.Eq.Unicode          ( (≡) )
import Data.Function.Unicode    ( (∘) )
import Data.Monoid.Unicode      ( (⊕) )
import Data.Ord.Unicode         ( (≤), (≥) )
import Numeric.Natural.Unicode  ( ℕ )

-- deepseq -----------------------------

import Control.DeepSeq  ( NFData )

-- finite-typelits ---------------------

import qualified  Data.Finite
import Data.Finite  ( Finite, finite, getFinite, packFinite )

-- genvalidity -------------------------

import Data.GenValidity  ( GenValid( genValid, shrinkValid ) )

-- ghc-typelits-extra ------------------

import GHC.TypeLits.Extra  ( DivRU )

-- lens --------------------------------

import Control.Lens.Prism   ( Prism' )
import Control.Lens.Review  ( (#) )

-- mtl ---------------------------------

import Control.Monad.Except  ( MonadError, throwError )

-- more-unicode ------------------------

import Data.MoreUnicode.Functor  ( (⊳), (⩺) )
import Data.MoreUnicode.Tasty    ( (≟) )

-- number ------------------------------

import Number  ( FromI( fromI, fromI', __fromI, __fromI' )
               , ToNum( toNum ) )

-- QuickCheck --------------------------

import Test.QuickCheck        ( Gen, Property, property )
import Test.QuickCheck.Arbitrary
                              ( Arbitrary( arbitrary ), arbitraryBoundedEnum )

-- tasty -------------------------------

import Test.Tasty  ( TestTree, testGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( assertBool, testCase )

-- tasty-plus --------------------------

import TastyPlus  ( assertAnyException, runTestsP, runTestsReplay, runTestTree )

-- tasty-quickcheck --------------------

import Test.Tasty.QuickCheck  ( testProperty )

-- template-haskell --------------------

import Language.Haskell.TH         ( Exp( AppE, ConE, LitE ), ExpQ
                                   , Lit( IntegerL ) )
import Language.Haskell.TH.Syntax  ( Lift( lift ) )

-- tfmt --------------------------------

import Text.Fmt  ( fmt )

-- validity ----------------------------

import Data.Validity  ( Validation, Validity( validate ), check )

--------------------------------------------------------------------------------

__bang__ ∷ Show ε ⇒ Either ε α → α
__bang__ = either (error ∘ show) id

maxOf ∷ Bounded α ⇒ α → α
maxOf = const maxBound

newtype BoundedN (ν ∷ Nat) = BoundedN { unBoundedN ∷ Finite ν }
  deriving (Bounded,Enum,Eq,Generic,NFData,Ord,Read,Show)

type 𝕎 = BoundedN

finiteℕ ∷ KnownNat ν ⇒ ℕ → Finite ν
finiteℕ = finite ∘ fromIntegral

getFiniteℕ ∷ Finite ν → ℕ
getFiniteℕ = fromInteger ∘ getFinite

boundedℕ ∷ KnownNat ν ⇒ ℕ → BoundedN ν
boundedℕ = BoundedN ∘ finiteℕ

----------------------------------------

instance KnownNat ν ⇒ Validity (BoundedN ν) where
  validate ∷ BoundedN ν → Validation
  validate b = let m = toNum @_ @Integer $ maxOf b
                   i = toNum b
                   checkMsg = [fmt|value %d does not exceed upper bound %d|] i m
                in check (i ≤ m) checkMsg
                 ⊕ check (i ≥ 0) ([fmt|value %d is non-negative|] i)

instance KnownNat ν ⇒ GenValid (BoundedN ν) where
  genValid ∷ Gen (BoundedN ν)
  genValid = arbitrary
  shrinkValid ∷ BoundedN ν → [BoundedN ν]
  -- try all the lower-numbered values
  shrinkValid (𝕎 0) = []
  shrinkValid (𝕎 n) = enumFromTo (𝕎 0) (𝕎 (n-1))
  shrinkValid  _     = error "shrinkValid failed to pattern-match on 𝕎"

instance KnownNat ν ⇒ Lift (BoundedN ν) where
  lift ∷ BoundedN ν → ExpQ
  -- λ> runQ [|  W 7 |]
  -- AppE (ConE MInfo.BoundedN.W) (LitE (IntegerL 7))
  lift (BoundedN n) = return $ AppE (ConE 'W) (LitE $ IntegerL (getFinite n))

----------------------------------------

data BoundsError α = InputTooLow  α | InputTooHigh ℕ α
  deriving (Eq,Show)

instance (Typeable α, Show α) ⇒ Exception (BoundsError α)

-- see ProcLib.Process2 / ExecError for another example of a
-- multi-param error class
class AsBoundsError α ε where
  _BoundsError ∷ Prism' ε (BoundsError α)

instance AsBoundsError α (BoundsError α) where
  _BoundsError = id

inputTooLow ∷ (AsBoundsError α ε, MonadError ε η) ⇒ α → η χ
inputTooLow i = throwError $ _BoundsError # InputTooLow i

inputTooHigh ∷ (AsBoundsError α ε, MonadError ε η) ⇒ ℕ → α → η χ
inputTooHigh max i = throwError $ _BoundsError # InputTooHigh max i

-- | Like `inputTooHigh`, but infers the max value from the type of the result.
inputTooHigh' ∷ (KnownNat ν,AsBoundsError α ε,MonadError ε η) ⇒ α → η (proxy ν)
inputTooHigh' i = let result = inputTooHigh max i
                      max    = natVal $ fromME result
                   in result


fromME ∷ MonadError σ μ ⇒ μ β → β
fromME = error $ "fromME should never be called (for type inference only)"

checkBoundedN ∷ (KnownNat ν, Integral α, AsBoundsError α ε, MonadError ε η) ⇒
                α → η (𝕎 ν)
checkBoundedN i | i < 0 = inputTooLow i
                | otherwise = -- we 'let' the result, to bind a name to the
                              -- return type, so that inputTooHigh' can use it
                              -- to infer the upper bound
                              let result = case fromI i of
                                             Just n  → return n
                                             Nothing → inputTooHigh' i
                               in result

checkBoundedN' ∷ (KnownNat ν, Integral α, MonadError (BoundsError α) η) ⇒
                 α → η (𝕎 ν)
checkBoundedN' = checkBoundedN

{- | Convert an Integral to a 𝕎, hopefully. -}
toBoundedN ∷ (KnownNat ν, Integral α) ⇒ α → Maybe (𝕎 ν)
-- we can't use the maybe-funnel on here checkBoundedN here, because
-- checkBoundedN uses toBoundedN…
toBoundedN = BoundedN ⩺ packFinite ∘ toInteger

instance KnownNat ν ⇒ FromI (BoundedN ν) where
  fromI = toBoundedN

{- | Alias for `toBoundedN`, with Integer to avoid type ambiguity -}
toBoundedN' ∷ KnownNat ν ⇒ Integer → Maybe (𝕎 ν)
toBoundedN' = fromI'

--------------------

{- | Alias for @toBoundedN@, specifying Integer input for ease of literal
     use. -}
𝕨 ∷ KnownNat ν ⇒ Integer → Maybe (𝕎 ν)
𝕨 = fromI

--------------------

toBoundedNTests ∷ TestTree
toBoundedNTests =
  testGroup "toBoundedN"
            [ testCase "toBoundedN 5" $ Just (𝕎 @6 5) ≟ toBoundedN' 5
            , testCase "toBoundedN 7" $ (Nothing ∷ Maybe (𝕎 6)) ≟ 𝕨 7
            , testCase "toBoundedN @6 7" $ Nothing      ≟ toBoundedN' @6 7
            , testCase "toBoundedN @8 7" $ Just (𝕎 7) ≟ toBoundedN' @8 7
            ]

----------------------------------------

{- | *PARTIAL* Convert an Integral to a 𝕎' (or bust). -}
__toBoundedN ∷ (KnownNat ν, Integral α, Show α) ⇒ α → 𝕎 ν
__toBoundedN = __bang__ ∘ checkBoundedN'

{- | Alias for `__toBoundedN`, with Integer to avoid type ambiguity.
    *PARTIAL* Convert an Integral to a 𝕎' (or bust). -}
__toBoundedN' ∷ KnownNat ν ⇒ Integer → 𝕎 ν
__toBoundedN' = __toBoundedN

__toBoundedNTests ∷ TestTree
__toBoundedNTests =
  testGroup "__toBoundedN"
            [ testCase "__toBoundedN 5" $ (𝕎 @6 5 ∷ 𝕎 6) ≟ __toBoundedN' @6 5
            , testCase "__toBoundedN 7" $
                assertAnyException "__toBoundedN 7" $ __toBoundedN' @6 7
            ]

----------------------------------------

{- | Pattern to (de)construct a BoundedN (A.K.A., 𝕎') from any integral value.
     *BEWARE* that the constructor is *PARTIAL* - you can, for example, write
     𝕎' @3 (-1), and it will compile (but will diverge under evaluation).
 -}
pattern 𝕎 ∷ KnownNat ν ⇒ Integer → 𝕎 ν
pattern 𝕎 i ← ((getFinite ∘ unBoundedN) → i)
              where 𝕎 i = __fromI' i

{- | Non-unicode alias for 𝕎 -}
pattern W ∷ KnownNat ν ⇒ Integer → 𝕎 ν
pattern W i ← ((getFinite ∘ unBoundedN) → i)
              where W i = __fromI' i

{- | Alias for 𝕎, for any @Integral@. -}
pattern 𝕎' ∷ (KnownNat ν, Integral α, Show α) ⇒ α → 𝕎 ν
pattern 𝕎' i ← ((fromInteger ∘ getFinite ∘ unBoundedN) → i)
              where 𝕎' i = __fromI i

{- | Non-unicode alias for 𝕎' -}
pattern W' ∷ (KnownNat ν, Integral α, Show α) ⇒ α → 𝕎 ν
pattern W' i ← ((fromInteger ∘ getFinite ∘ unBoundedN) → i)
              where W' i = __fromI i

instance KnownNat ν ⇒ ToNum (BoundedN ν) where
  toNum ∷ Num α ⇒ 𝕎 ν → α
  toNum (𝕎 i) = fromInteger $ toInteger i
  toNum _      = error "failed to convert BoundedN to num"

--------------------

𝕨Tests ∷ TestTree
𝕨Tests =
  let five  = 𝕎 @7 5
      seven = 𝕎 @7 7
   in testGroup "𝕎'"
                [ testCase "five"  $ 5 ≟ (\ case (𝕎 x) → x; _ → -1) five
                , testCase "seven" $
                  assertAnyException "seven" $ (\ case (𝕎 x) → x; _ → 1) seven
                , testCase "five" $ five ≟ 𝕎 5
                , testCase "seven" $ assertAnyException "seven" $ 𝕎 @7 7
                , testCase "-1" $ assertAnyException "-1" $ 𝕎 @3 (-1)
                ]

instance KnownNat ν ⇒ Arbitrary (BoundedN ν) where
  arbitrary ∷ Gen (BoundedN ν)
  arbitrary = BoundedN ⊳ arbitraryBoundedEnum

arbitraryTests ∷ TestTree
arbitraryTests =
  let propBounded ∷ KnownNat ν ⇒ BoundedN ν → Property
      propBounded n = property $ n ≥ 𝕎 0 ∧ n ≤ maxBound
   in testGroup "Arbitrary"
                [ testProperty "properlyBounded" (propBounded @137) ]

-- testing ---------------------------------------------------------------------

boundedTests ∷ TestTree
boundedTests =
  testGroup "Bounded"
    [ testCase "minBound" $ 𝕎 0 ≟ minBound @(𝕎 7)
    , testCase "maxBound" $ 𝕎 6 ≟ maxBound @(𝕎 7)
    ]

----------------------------------------

enumTests ∷ TestTree
enumTests =
  let assertFail ∷ String → 𝕎 7 → TestTree
      assertFail n v = testCase n $ assertAnyException n v
   in testGroup "Enum"
        [ testCase   "succ 5"   $ 𝕎 6 ≟ succ (𝕎 @7 5)
        , testCase   "pred 5"   $ 𝕎 4 ≟ pred (𝕎 @7 5)
        , assertFail "pred 0"   (pred $ 𝕎 0)
        , assertFail "succ 6"   (succ $ 𝕎 6)
        , testCase   "toEnum 4" $ (𝕎 @7 4) ≟ toEnum 4
        , assertFail "toEnum 7" (toEnum $ 7)
        , testCase   "fromEnum 4" $ 4 ≟ (fromEnum (𝕎 @7 4))
        , testCase   "enumFrom 4" $
            [𝕎 4, 𝕎 5, 𝕎 6] ≟ enumFrom (𝕎 @7 4)
        , testCase   "enumFromThen 1 3" $
            [𝕎 1, 𝕎 3, 𝕎 5] ≟ enumFromThen (𝕎 @7 1) (𝕎 3)
        , testCase   "enumFromTo 1 4" $
            [𝕎 1, 𝕎 2, 𝕎 3, 𝕎 4] ≟ enumFromTo (𝕎 @7 1) (𝕎 4)

        , testCase   "enumFromThenTo 8 5 0" $
              [𝕎 8, 𝕎 5, 𝕎 2]
            ≟ enumFromThenTo (𝕎 @9 8) (𝕎 5) (𝕎 0)
        ]

----------------------------------------

eqTests ∷ TestTree
eqTests =
  testGroup "Eq" [ testCase "2==2" $ 𝕎 2 ≟ (𝕎 @9 2)
                 , testCase "2/=3" $ assertBool "2/=3" (not $ 𝕎 2 ≡ 𝕎 @7 3)
                 ]

----------------------------------------

{- | `Prelude.mod`, returning a BoundedN (and type implied by). -}
modulo ∷ (KnownNat ν, Integral α) ⇒ α → 𝕎 ν
modulo i = BoundedN $ Data.Finite.modulo (toInteger i)

{- | `modulo` using `ToNum` rather that `Integral`. -}
moduloN ∷ (KnownNat ν, ToNum α) ⇒ α → 𝕎 ν
moduloN i = BoundedN $ Data.Finite.modulo (toNum i)

{- | `Prelude.mod`, returning a BoundedN, with a proxy to help with type
     signatures. -}
moduloProxy ∷ (KnownNat ν, Integral α) ⇒ proxy ν → α → 𝕎 ν
moduloProxy p i = BoundedN $ Data.Finite.moduloProxy p (toInteger i)

{- | Alias for `moduloProxy`. -}
moduloP ∷ (KnownNat ν, Integral α) ⇒ proxy ν → α → 𝕎 ν
moduloP = moduloProxy

{- | `moduloProxy` using `ToNum` rather that `Integral`. -}
moduloProxyN ∷ (KnownNat ν, ToNum α) ⇒ proxy ν → α → 𝕎 ν
moduloProxyN p i = BoundedN $ Data.Finite.moduloProxy p (toNum i)

{- | Alias for `moduloPN`. -}
moduloPN ∷ (KnownNat ν, ToNum α) ⇒ proxy ν → α → 𝕎 ν
moduloPN = moduloProxyN

------------------------------------------------------------

{- | `Prelude.divMod`, returning a BoundedN (and type implied by). -}
divModulo ∷ (KnownNat ν, Integral α) ⇒ α → (α, 𝕎 ν)
divModulo i = let m = BoundedN $ Data.Finite.modulo (toInteger i)
                  n = fromInteger $ toInteger $ natVal m
               in (i `div` n, m)

{- | Alias for `divModulo`. -}
divM ∷ (KnownNat ν, Integral α) ⇒ α → (α, 𝕎 ν)
divM = divModulo

{- | `Prelude.divMod`, returning a BoundedN, with a proxy to help with type
     signatures. -}
divModuloProxy ∷ (KnownNat ν, Integral α) ⇒ proxy ν → α → (α, 𝕎 ν)
divModuloProxy p i = let m = BoundedN $ Data.Finite.moduloProxy p (toInteger i)
                         n = fromInteger $ toInteger $ natVal m
                      in (i `div` n, m)

{- | Alias for `divModuloProxy`. -}
divModuloP ∷ (KnownNat ν, Integral α) ⇒ proxy ν → α → (α, 𝕎 ν)
divModuloP = divModuloProxy

{- | Alias for `divModuloProxy`. -}
divMP ∷ (KnownNat ν, Integral α) ⇒ proxy ν → α → (α, 𝕎 ν)
divMP = divModuloProxy

{- | Alias for `divModuloProxy`, with the arguments flipped. -}
infixl 7 ⨸
(⨸) ∷ (KnownNat ν, Integral α) ⇒ α → proxy ν → (α, 𝕎 ν)
(⨸) = flip divModuloProxy

divModuloTests ∷ TestTree
divModuloTests =
  testGroup "divModulo"
            [ testCase "6 ≑ 3" $ (2, 𝕎 0) ≟ divModulo @3 (6 ∷ Integer)
            , testCase "7 ≑ 3" $ (2, 𝕎 1) ≟ divModulo @3 (7 ∷ Integer)
            , testCase "8 ≑ 3" $ (2, 𝕎 2) ≟ divModulo @3 (8 ∷ Integer)
            , testCase "9 ≑ 3" $ (3, 𝕎 0) ≟ divModulo @3 (9 ∷ Integer)
            , testCase "8 ⨸ 3" $ (2, 𝕎 2) ≟ (8 ∷ Integer) ⨸ (Proxy ∷ Proxy 3)
            ]

----------------------------------------

add ∷ BoundedN ν → BoundedN ν' → BoundedN (ν + ν')
add (BoundedN m) (BoundedN n) = BoundedN $ Data.Finite.add m n

infixl 6 ⨹
(⨹) ∷ BoundedN ν → BoundedN ν' → BoundedN (ν + ν')
(⨹) = add

----------

addTests ∷ TestTree
addTests =
  testGroup "add" [ testCase "6 + 3" $ 𝕎 @12 9 ≟ 𝕎 @8 6 ⨹ 𝕎 @4 3 ]

----------------------------------------

subtract ∷ BoundedN ν → BoundedN ν' → Either (BoundedN ν') (BoundedN ν)
subtract (BoundedN m) (BoundedN n) =
  bimap BoundedN BoundedN $ Data.Finite.sub m n

sub ∷ BoundedN ν → BoundedN ν' → Either (BoundedN ν') (BoundedN ν)
sub = subtract

infixl 6 ⨺
(⨺) ∷ BoundedN ν → BoundedN ν' → Either (BoundedN ν') (BoundedN ν)
(⨺) = subtract

----------

subTests ∷ TestTree
subTests =
  testGroup "sub" [ testCase "6 - 3" $ Right (𝕎 2) ≟ 𝕎 @8 6 ⨺ 𝕎 @5 4 ]

----------------------------------------

multiply ∷ BoundedN ν → BoundedN ν' → BoundedN (ν * ν')
multiply (BoundedN m) (BoundedN n) = BoundedN $ Data.Finite.multiply m n

mult ∷ BoundedN ν → BoundedN ν' → BoundedN (ν * ν')
mult = multiply

infixl 7 ⨻
(⨻) ∷ BoundedN ν → BoundedN ν' → BoundedN (ν * ν')
(⨻) = multiply

----------

multTests ∷ TestTree
multTests =
  testGroup "mult" [ testCase "6 * 3" $ 𝕎 24 ≟ 𝕎 @8 6 ⨻ 𝕎 @5 4
                   , testCase "6 * 3" $ 𝕎 @35 24 ≟ 𝕎 6 ⨻ 𝕎 @5 4
                   ]

----------------------------------------

{- | Multiply a bounded value by a fixed value, which is encoded in the type. -}
product ∷ (KnownNat ν, KnownNat γ, KnownNat (ν * γ)) ⇒
          BoundedN ν → proxy γ → BoundedN (ν * γ)
product (BoundedN m) n =
  BoundedN $ finite $ (getFinite m) * fromIntegral (natVal n)

{- | Unicode operator for product; note that the half-circle is on the side of
     the proxy type (type-affixed value). -}
(⨵) ∷ (KnownNat ν, KnownNat γ, KnownNat (ν * γ)) ⇒
       BoundedN ν → proxy γ → BoundedN (ν * γ)
infixl 7 ⨵
(⨵) = product

{- | Unicode operator for product; note that the half-circle is on the side of
     the proxy type (type-affixed value). -}
(⨴) ∷ (KnownNat ν, KnownNat γ, KnownNat (ν * γ)) ⇒
       proxy γ → BoundedN ν → BoundedN (ν * γ)
infixl 7 ⨴
(⨴) = flip product

productTests ∷ TestTree
productTests =
  testGroup "product" [ testCase "3 *: 5" $ 𝕎 @20 15 ≟ 𝕎 @4 3 `product` 𝕎 @5 0
                      , testCase "3 *: 4" $ 𝕎 12 ≟ 𝕎 @4 3 ⨵ 𝕎 @4 0
                      , testCase "3 *: 6" $ 𝕎 @24 18 ≟ 𝕎 @4 3 ⨵ Proxy
                      , testCase "4 *: 6" $ 𝕎 24 ≟ (Proxy @6) ⨴ 𝕎 @5 4
                      ]

----------------------------------------

{- | Divide a bounded value by a static value, returning also the remainder. -}
divide ∷ (KnownNat (DivRU ν γ), KnownNat γ) ⇒
         BoundedN ν → proxy γ → (BoundedN (DivRU ν γ),BoundedN γ)
divide (BoundedN a) b = let (x,y) = getFiniteℕ a `divMod` natVal b
                         in (boundedℕ x,boundedℕ y)

infixl 7 ⫽
(⫽) ∷ (KnownNat (DivRU ν γ), KnownNat γ) ⇒
       BoundedN ν → proxy γ → (BoundedN (DivRU ν γ),BoundedN γ)
(⫽) = divide

divideTests ∷ TestTree
divideTests =
  testGroup "divide"
            [ testCase "0 ⫽ 3" $ (𝕎 @3 0,𝕎 @3 0) ≟ 𝕎 @8 0 `divide` Proxy @3
            , testCase "1 ⫽ 3" $ (𝕎 @3 0,𝕎 @3 1) ≟ 𝕎 @8 1 `divide` Proxy @3
            , testCase "2 ⫽ 3" $ (𝕎 @3 0,𝕎 @3 2) ≟ 𝕎 @8 2 `divide` Proxy @3
            , testCase "3 ⫽ 3" $ (𝕎 @3 1,𝕎 @3 0) ≟ 𝕎 @8 3 `divide` Proxy @3
            , testCase "4 ⫽ 3" $ (𝕎 @3 1,𝕎 @3 1) ≟ 𝕎 @8 4 `divide` Proxy @3
            , testCase "5 ⫽ 3" $ (𝕎 @3 1,𝕎 @3 2) ≟ 𝕎 @8 5 `divide` Proxy @3
            -- try it without the explicit types
            , testCase "6 ⫽ 3" $ (𝕎 2,𝕎 0) ≟ 𝕎 @8 6 `divide` Proxy @3
            , testCase "7 ⫽ 3" $ (𝕎 @3 2,𝕎 @3 1) ≟ 𝕎 @8 7 `divide` Proxy

            -- different BoundedN value, to show that isn't affecting things
            -- (or rather that it is, but in the right way - the output bound
            -- only)
            , testCase "0 ⫽ 3" $ (𝕎 @4 0,𝕎 @3 0) ≟ 𝕎 @10 0 `divide` Proxy @3
            , testCase "1 ⫽ 3" $ (𝕎 @4 0,𝕎 @3 1) ≟ 𝕎 @10 1 `divide` Proxy @3
            , testCase "2 ⫽ 3" $ (𝕎 @4 0,𝕎 @3 2) ≟ 𝕎 @10 2 `divide` Proxy @3
            , testCase "3 ⫽ 3" $ (𝕎 @4 1,𝕎 @3 0) ≟ 𝕎 @10 3 `divide` Proxy @3
            , testCase "4 ⫽ 3" $ (𝕎 @4 1,𝕎 @3 1) ≟ 𝕎 @10 4 `divide` Proxy @3
            , testCase "5 ⫽ 3" $ (𝕎 @4 1,𝕎 @3 2) ≟ 𝕎 @10 5 `divide` Proxy @3
            -- try it without the explicit types
            , testCase "6 ⫽ 3" $ (𝕎 2,𝕎 0) ≟ 𝕎 @10 6 `divide` Proxy @3
            , testCase "7 ⫽ 3" $ (𝕎 @4 2,𝕎 @3 1) ≟ 𝕎 @10 7 `divide` Proxy
            , testCase "8 ⫽ 3" $ (𝕎 @4 2,𝕎 @3 2) ≟ 𝕎 @10 8 `divide` Proxy
            , testCase "9 ⫽ 3" $ (𝕎 @4 3,𝕎 @3 0) ≟ 𝕎 @10 9 `divide` Proxy

            -- and also @9, which is equally divisible by @3
            , testCase "0 ⫽ 3" $ (𝕎 @3 0,𝕎 @3 0) ≟ 𝕎 @9 0 `divide` Proxy @3
            , testCase "1 ⫽ 3" $ (𝕎 @3 0,𝕎 @3 1) ≟ 𝕎 @9 1 `divide` Proxy @3
            , testCase "2 ⫽ 3" $ (𝕎 @3 0,𝕎 @3 2) ≟ 𝕎 @9 2 `divide` Proxy @3
            , testCase "3 ⫽ 3" $ (𝕎 @3 1,𝕎 @3 0) ≟ 𝕎 @9 3 `divide` Proxy @3
            , testCase "4 ⫽ 3" $ (𝕎 @3 1,𝕎 @3 1) ≟ 𝕎 @9 4 `divide` Proxy @3
            , testCase "5 ⫽ 3" $ (𝕎 @3 1,𝕎 @3 2) ≟ 𝕎 @9 5 `divide` Proxy @3
            -- try it without the explicit types
            , testCase "6 ⫽ 3" $ (𝕎 2,𝕎 0) ≟ 𝕎 @9 6 `divide` Proxy @3
            , testCase "7 ⫽ 3" $ (𝕎 @3 2,𝕎 @3 1) ≟ 𝕎 @9 7 `divide` Proxy
            , testCase "8 ⫽ 3" $ (𝕎 @3 2,𝕎 @3 2) ≟ 𝕎 @9 8 `divide` Proxy
            ]

----------------------------------------

{- | Divide a bounded int by a static value, rounding the result.  We use
     classic rounding rules ('round half up'; in which a precise half rounds up.
 -}

-- https://en.wikipedia.org/wiki/Rounding#Round_half_up
rounded ∷ (KnownNat γ, KnownNat (DivRU (ν+1) γ)) ⇒
          BoundedN ν → proxy γ → BoundedN (DivRU (ν+1) γ)
rounded (BoundedN a) b = let x = (2*(getFiniteℕ a)) `div` (natVal b)
                             (y,z) = x `divMod` 2
                          in BoundedN ∘ finite ∘ fromIntegral $ y+z

{- | Alias for `rounded`. -}
infixl 7 ⦼
(⦼) ∷ (KnownNat γ, KnownNat (DivRU (ν+1) γ)) ⇒
       BoundedN ν → proxy γ → BoundedN (DivRU (ν+1) γ)
(⦼) = rounded

roundedTests ∷ TestTree
roundedTests =
  testGroup "rounded"
    [ testGroup "@6 rounded @3"
        [ testCase "0" $ (𝕎 @3 0) ≟ 𝕎 @6 0 `rounded` Proxy @3
        , testCase "1" $ (𝕎    0) ≟ 𝕎 @6 1 `rounded` Proxy @3
        , testCase "2" $ (𝕎    1) ≟ 𝕎 @6 2 `rounded` Proxy @3
        , testCase "3" $ (𝕎    1) ≟ 𝕎 @6 3 `rounded` Proxy @3
        , testCase "4" $ (𝕎    1) ≟ 𝕎 @6 4 `rounded` Proxy @3
        , testCase "5" $ (𝕎    2) ≟ 𝕎 @6 5 `rounded` Proxy @3
        ]
    , testGroup "@7 rounded @3"
        [ testCase "0" $ (𝕎 @3 0) ≟ 𝕎 @7 0 `rounded` Proxy @3
        , testCase "1" $ (𝕎    0) ≟ 𝕎 @7 1 `rounded` Proxy @3
        , testCase "2" $ (𝕎    1) ≟ 𝕎 @7 2 `rounded` Proxy @3
        , testCase "3" $ (𝕎    1) ≟ 𝕎 @7 3 `rounded` Proxy @3
        , testCase "4" $ (𝕎    1) ≟ 𝕎 @7 4 `rounded` Proxy @3
        , testCase "5" $ (𝕎    2) ≟ 𝕎 @7 5 `rounded` Proxy @3
        , testCase "6" $ (𝕎    2) ≟ 𝕎 @7 6 `rounded` Proxy @3
        ]
    , testGroup "@8 rounded @3"
        [ testCase "0" $ (𝕎 @3 0) ≟ 𝕎 @8 0 `rounded` Proxy @3
        , testCase "1" $ (𝕎    0) ≟ 𝕎 @8 1 `rounded` Proxy @3
        , testCase "2" $ (𝕎    1) ≟ 𝕎 @8 2 `rounded` Proxy @3
        , testCase "3" $ (𝕎    1) ≟ 𝕎 @8 3 `rounded` Proxy @3
        , testCase "4" $ (𝕎    1) ≟ 𝕎 @8 4 `rounded` Proxy @3
        , testCase "5" $ (𝕎    2) ≟ 𝕎 @8 5 `rounded` Proxy @3
        , testCase "6" $ (𝕎    2) ≟ 𝕎 @8 6 `rounded` Proxy @3
        , testCase "7" $ (𝕎 @3 2) ≟ 𝕎 @8 7 `rounded` Proxy @3
        ]
    , testGroup "@6 rounded @2"
        [ testCase "0" $ (𝕎 @4 0) ≟ 𝕎 @6 0 `rounded` Proxy @2
        , testCase "1" $ (𝕎    1) ≟ 𝕎 @6 1 `rounded` Proxy @2
        , testCase "2" $ (𝕎    1) ≟ 𝕎 @6 2 `rounded` Proxy @2
        , testCase "3" $ (𝕎    2) ≟ 𝕎 @6 3 `rounded` Proxy @2
        , testCase "4" $ (𝕎    2) ≟ 𝕎 @6 4 `rounded` Proxy @2
        , testCase "5" $ (𝕎 @4 3) ≟ 𝕎 @6 5 `rounded` Proxy @2
        ]
    , testGroup "@7 rounded @2"
        [ testCase "0" $ (𝕎 @4 0) ≟ 𝕎 @7 0 `rounded` Proxy @2
        , testCase "1" $ (𝕎    1) ≟ 𝕎 @7 1 `rounded` Proxy @2
        , testCase "2" $ (𝕎    1) ≟ 𝕎 @7 2 `rounded` Proxy @2
        , testCase "3" $ (𝕎    2) ≟ 𝕎 @7 3 `rounded` Proxy @2
        , testCase "4" $ (𝕎    2) ≟ 𝕎 @7 4 `rounded` Proxy @2
        , testCase "5" $ (𝕎    3) ≟ 𝕎 @7 5 `rounded` Proxy @2
        , testCase "6" $ (𝕎 @4 3) ≟ 𝕎 @7 6 `rounded` Proxy @2
        ]
    , testGroup "@8 rounded @2"
        [ testCase "0" $ (𝕎 @5 0) ≟ 𝕎 @8 0 `rounded` Proxy @2
        , testCase "1" $ (𝕎    1) ≟ 𝕎 @8 1 `rounded` Proxy @2
        , testCase "2" $ (𝕎    1) ≟ 𝕎 @8 2 `rounded` Proxy @2
        , testCase "3" $ (𝕎    2) ≟ 𝕎 @8 3 `rounded` Proxy @2
        , testCase "4" $ (𝕎    2) ≟ 𝕎 @8 4 `rounded` Proxy @2
        , testCase "5" $ (𝕎    3) ≟ 𝕎 @8 5 `rounded` Proxy @2
        , testCase "6" $ (𝕎    3) ≟ 𝕎 @8 6 `rounded` Proxy @2
        , testCase "7" $ (𝕎 @5 4) ≟ 𝕎 @8 7 `rounded` Proxy @2
        ]
    ]


------------------------------------------------------------

tests ∷ TestTree
tests = testGroup "BoundedN" [ boundedTests, enumTests, eqTests, arbitraryTests
                             , toBoundedNTests, __toBoundedNTests, 𝕨Tests
                             , divModuloTests, addTests, subTests, multTests
                             , productTests, divideTests, roundedTests
                             ]

----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

-- that's all, folks! ----------------------------------------------------------
