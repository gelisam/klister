# Commentary

## Parsing

    readExpr :: FilePath -> Text -> Either Text Syntax

`Syntax` is an s-expression tree. We distinguish between square brackets, which are intended to be used whenever the arity is fixed, from parentheses, which are intended to be used whenever the arity is variable. So if you are experimenting with an unfamiliar piece of syntax, you can try to duplicate an element found between parentheses, but you probably shouldn't try to duplicate an element found between square brackets.

At this stage, the identifiers at the leaves are simply `Text`. Other leaf values include booleans, strings, and "signals". A signal is simply a number, but we call it a signal because we intend to use those numbers as labels for the `wait-signal` and `send-signal` operations, we don't intend to use them in arithmetic operations.

Each node in the syntax tree is annotated with its source location and with a "scope set" indicating which variables are in scope. At this point, we have only parsed the s-expression, we have not attributed meaning such as binding-sites vs use sites to the various identifiers, and so at this point all the scope sets are empty.

TODO: Presumably, we use those scope sets later on. Give an example which explains why we need `Syntax` values to have scope sets.


## Module System

The module system is based on that described by Matthew Flatt in "Composable and Compilable Macros: You Want it /When?/" (ICFP 2002). Source modules are written in a /language/ that is intended to provide all the initial bindings available in the file. The `kernel` language is primitive and contains all the built-in operators.

There is a cache of the expanded and evaluated forms of each module in the system. At the start of expansion, this cache contains only `kernel`.

There are two parts of the process of bringing a module into scope: loading it, and visiting it. Loading refers to the process of parsing the module's source code and expanding it to the core language, while visiting is the process of evaluating the contents of a module at a particular phase and producing a collection of bindings exported from the module. Loading occurs at phase 0, while visiting a module can be shifted relative to some base phase.

Loading an uncached module consists of the following steps:

 1. Visit the module's language, unless that language is `kernel`.
 
 2. Allocate a scope to serve as the root for the module (the "outside-edge scope" described in Flatt '16), and bind all the language's exports using this scope and the current-phase scope that's appropriate for the export.
 
 3. Expand the contents of the module.
 
 4. Add the expanded module to the cache.

Visiting an uncached module relative to phase /p/ consists of the following steps:

 1. Load the module.
 
 2. Shift the expanded module /p/ phases.
 
 3. Evaluate the module's contents and insert definitions into the environment.
 
 4. Construct the set of exports, and return it. Add them to the cache.
