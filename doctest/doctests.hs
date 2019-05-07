module Main (main) where

import Test.DocTest

main :: IO ()
main =
    doctest
        [ "-XBangPatterns"
        , "-XLambdaCase"
        , "-XFlexibleInstances"
        , "-XDeriveFunctor"
        , "-XMultiParamTypeClasses"
        , "-XUndecidableInstances"
        , "-isrc"
        , "src/"]
