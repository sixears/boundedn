{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax     #-}

-- base --------------------------------

import Control.Monad        ( return )
import Data.Function        ( ($) )
import System.IO            ( IO )

-- base-unicode-symbols ----------------

import Data.Monoid.Unicode  ( (⊕) )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⊵) )


-- optparse-applicative ----------------

import Options.Applicative.Builder  ( failureCode, fullDesc, info, prefs
                                    , progDesc, showHelpOnError )
import Options.Applicative.Extra    ( customExecParser, helper )

import TastyPlus    ( runTests_, tastyOptParser )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import BoundedN.T.Tests    ( tests )

-------------------------------------------------------------------------------

main ∷ IO ()
main = do
  tastyOpts ← customExecParser (prefs showHelpOnError) $
                 info (helper ⊵ tastyOptParser tests)
                      (fullDesc ⊕ progDesc "minfo tests"
                                ⊕ failureCode 254)

  _ ← runTests_ tastyOpts
  return ()

-- that's all, folks! ---------------------------------------------------------
