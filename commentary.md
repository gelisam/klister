# Commentary

## Parsing

    readExpr :: FilePath -> Text -> Either Text Syntax

`Syntax` is an s-expression tree. We distinguish between square brackets, which are intended to be used whenever the arity is fixed, from parentheses, which are intended to be used whenever the arity is variable. So if you are experimenting with an unfamiliar piece of syntax, you can try to duplicate an element found between parentheses, but you probably shouldn't try to duplicate an element found between square brackets.

At this stage, the identifiers at the leaves are simply `Text`. Other leaf values include booleans, strings, and "signals". A signal is simply a number, but we call it a signal because we intend to use those numbers as labels for the `wait-signal` and `send-signal` operations, we don't intend to use them in arithmetic operations.

Each node in the syntax tree is annotated with its source location and with a "scope set" indicating which variables are in scope. At this point, we have only parsed the s-expression, we have not attributed meaning such as binding-sites vs use sites to the various identifiers, and so at this point all the scope sets are empty.

TODO: Presumably, we use those scope sets later on. Give an example which explains why we need `Syntax` values to have scope sets.

## Evaluating

    eval :: Core -> Eval Value

Eventually the `Syntax` gets simplified into a core language which we can evaluate. Most of the complexity happens between `Syntax` and `Core`, so we'll keep that part for last.

`Core` expressions consist of function applications, pattern-matching, and constructors for the language's primitive types. Those primitive types include functions, booleans, signals, reified `Syntax` objects, and "macro actions". A macro action is a monadic block performing zero or more side-effects. These side-effects do not occur during evaluation, but rather during expansion, so we'll cover macro actions in more details in the `Expanding` section.

TODO: what happened to strings? `Syntax` supports booleans, strings, and signals, but of those, `Core` only supports booleans and signals. Maybe we're instead supposed to manipulate a reified `Syntax` object holding a string?

### `Core` variables: `Var`

    newtype Var = Var Unique

In a core expression, variables don't have names, they have been translated into a form which avoids accidental capture.

TODO: how does this relate to scope sets?

### `SplitCore` and `PartialCore`

Now is the time to talk about the complexity which happens between `Syntax` and `Core`. Part of that complexity is the fact that there are two more intermediate formats in-between: `Syntax` becomes `SplitCore`, then `PartialCore`, then `Core`.

    unsplit :: SplitCore -> PartialCore
    split   :: PartialCore -> IO SplitCore

    nonPartial     :: Core -> PartialCore
    runPartialCore :: PartialCore -> Maybe Core

A `PartialCore` expression is a tree with the same shape as a `Core` expression, except that sub-trees may be missing. The reason those sub-trees are missing is that we haven't computed them from the `Syntax` yet. `SplitCore` is a more useful form of `PartialCore` in which the missing sub-trees are labelled with a `SplitCorePtr`, so that we may graft sub-trees back in once they are computed. Every node in a `SplitCore` expression is labelled by a unique `SplitCorePtr`, not just the missing sub-trees.

    newtype SplitCorePtr = SplitCorePtr Unique

TODO: explain how the sub-trees get computed.

## Expanding

    expandExpr :: Syntax -> Expand SplitCore

TODO: explain the the expansion process, and the difference between the various `Unique`s we haven't explained yet: `Binding`, `ModulePtr`, `DeclPtr`, `ModBodyPtr`, and `TaskID`.
