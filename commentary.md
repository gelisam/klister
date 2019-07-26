# Commentary

## Parsing

    readExpr :: FilePath -> Text -> Either Text Syntax

`Syntax` is an s-expression tree. We distinguish between square brackets, which are intended to be used whenever the arity is fixed, from parentheses, which are intended to be used whenever the arity is variable. So if you are experimenting with an unfamiliar piece of syntax, you can try to duplicate an element found between parentheses, but you probably shouldn't try to duplicate an element found between square brackets.

At this stage, the identifiers at the leaves are simply `Text`. Other leaf values include booleans, strings, and "signals". A signal is simply a number, but we call it a signal because we intend to use those numbers as labels for the `wait-signal` and `send-signal` operations, we don't intend to use them in arithmetic operations.

Each node in the syntax tree is annotated with its source location and with a "scope set" indicating which variables are in scope. At this point, we have only parsed the s-expression, we have not attributed meaning such as binding-sites vs use sites to the various identifiers, and so at this point all the scope sets are empty.

TODO: Presumably, we use those scope sets later on. Give an example which explains why we need `Syntax` values to have scope sets.
