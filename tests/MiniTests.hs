{-# LANGUAGE OverloadedStrings #-}

-- | Tiny module to hold mini-test strings. Some mini-test strings are split
-- strings which conflict with the CPP pragma. See
-- https://downloads.haskell.org/ghc/latest/docs/users_guide/phases.html#cpp-and-string-gaps

module MiniTests where

import Data.Text

trivialUserMacro :: Text
trivialUserMacro = "[let-syntax \n\
                   \  [m [lambda [_] \n\
                   \       [pure [quote [lambda [x] x]]]]] \n\
                   \  m]"

letMacro :: Text
letMacro = "[let-syntax \n\
            \  [let1 [lambda [stx] \n\
            \          (syntax-case stx \n\
            \            [[list [_ binder body]] \n\
            \             (syntax-case binder \n\
            \               [[list [x e]] \n\
            \                {- [[lambda [x] body] e] -} \n\
            \                [pure [list-syntax \n\
            \                        [[list-syntax \n\
            \                           [[ident-syntax 'lambda stx] \n\
            \                            [list-syntax [x] stx] \n\
            \                            body] \n\
            \                           stx] \n\
            \                         e] \n\
            \                        stx]]])])]] \n\
            \  [let1 [x [lambda [x] x]] \n\
            \    x]]"

unboundVarLet :: Text
unboundVarLet = "[let-syntax \
                \  [m [lambda [_] \
                \       [pure [quote [lambda [x] x]]]]] \
                \  anyRandomWord]"
