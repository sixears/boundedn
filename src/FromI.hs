{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE UnicodeSyntax     #-}

module FromI
  ( FromI( fromI, fromI', __fromI, __fromI' ) )
where

import Prelude  ( Integer, Integral, error )

-- base --------------------------------

import Data.Function  ( ($) )
import Data.Maybe     ( Maybe( Just, Nothing ) )
import Data.Typeable  ( Typeable, typeOf )

-- tfmt --------------------------------

import Text.Fmt  ( fmt )

--------------------------------------------------------------------------------

class Typeable α ⇒ FromI α where
  fromI  ∷ Integral β ⇒ β → Maybe α

  fromI' ∷ Integer → Maybe α
  fromI' = fromI

  __fromI ∷ Integral β ⇒ β → α
  __fromI i = let result = case fromI i of
                             Just x  → x
                             Nothing → error $ [fmt|value %d out of %w range|]
                                               i (typeOf result)
               in result

  __fromI' ∷ Integer → α
  __fromI' = __fromI

-- that's all, folks! ----------------------------------------------------------
