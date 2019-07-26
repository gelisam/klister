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

Expansion is divided into a large number of small tasks. The input `Syntax` will eventually become the output's core expression, so we first create a `SplitCorePtr` and create our first task, to fill in that `SplitCorePtr` with the beginning of a tree. In the process, more tasks are created, e.g. to fill in the remaining sub-trees. `expandExpr` keeps executing tasks until no more tasks can be completed, and which point the entire core expression will hopefully be filled in. But that is not guaranteed, because some tasks can get stuck.

TODO: explain the difference between the various `Unique`s we haven't explained yet: `Binding`, `ModulePtr`, `DeclPtr`, `ModBodyPtr`, and `TaskID`.

### Stuck tasks

TODO: explain how a task may get stuck and what gets them unstuck.

TODO: explain macro actions in more details.

## Module System

The module system is based on that described by Matthew Flatt in "Composable and Compilable Macros: You Want it _When?_" (ICFP 2002). Source modules are written in a _language_ that is intended to provide all the initial bindings available in the file. The `kernel` language is primitive and contains all the built-in operators.

There is a cache of the expanded and evaluated forms of each module in the system. At the start of expansion, this cache contains only `kernel`.

There are two parts of the process of bringing a module into scope: loading it, and visiting it. Loading refers to the process of parsing the module's source code and expanding it to the core language, while visiting is the process of evaluating the contents of a module at a particular phase and producing a collection of bindings exported from the module. Loading occurs at phase 0, while visiting a module can be shifted relative to some base phase.

Loading an uncached module consists of the following steps:

 1. Visit the module's language, unless that language is `kernel`.
 
 2. Allocate a scope to serve as the root for the module (the "outside-edge scope" described in Flatt '16), and bind all the language's exports using this scope and the current-phase scope that's appropriate for the export.
 
 3. Expand the contents of the module.
 
 4. Add the expanded module to the cache.

Visiting an uncached module relative to phase _p_ consists of the following steps:

 1. Load the module.
 
 2. Shift the expanded module _p_ phases.
 
 3. Evaluate the module's contents and insert definitions into the environment.
 
 4. Construct the set of exports, and return it. Add them to the cache.
