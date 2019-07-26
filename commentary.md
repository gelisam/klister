# Commentary

## Parsing

    readExpr :: FilePath -> Text -> Either Text Syntax

`Syntax` is an s-expression tree. We distinguish between square brackets, which are intended to be used whenever the arity is fixed, from parentheses, which are intended to be used whenever the arity is variable. So if you are experimenting with an unfamiliar piece of syntax, you can try to duplicate an element found between parentheses, but you probably shouldn't try to duplicate an element found between square brackets.

At this stage, the identifiers at the leaves are simply `Text`. Other leaf values include booleans, strings, and "signals". A signal is simply a number, but we call it a signal because we intend to use those numbers as labels for the `wait-signal` and `send-signal` operations, we don't intend to use them in arithmetic operations.

Each node in the syntax tree is annotated with its source location and with a "scope set" indicating which variables are in scope. At this point, we have only parsed the s-expression, we have not attributed meaning such as binding-sites vs use sites to the various identifiers, and so at this point all the scope sets are empty.

Scope sets are used during expansion to determine which binding an identifier refers to. See the section on macro expansion for a quick description of their use, or "Binding as Sets of Scopes" (Flatt, POPL '16) for a complete description.


TODO: Presumably, we use those scope sets later on. Give an example which explains why we need `Syntax` values to have scope sets.

## Expanding

Macro expansion is the process of converting user-written syntax into the core language. Unlike traditional Lisps, macro expansion does not necessarily proceed from the outside of the expression towards the inside, from left to right. Instead, macro expansion is controlled by a _task queue_ and a _split expression_. Split expressions are trees in the core language in which some subtrees are not yet known (please see the section that describes them for details). Some tasks in the queue have dependencies; these will be skipped and requeued until their dependencies are satisfied.

The entry point to expanding expressions is

    expandExpr :: Syntax -> Expand SplitCore

It initializes the expander state with an empty split expression and a single task: to expand the input.

To expand an expression, the first step is to determine which procedure can expand it (this procedure is called the _transformer_). Then, the syntax itself is passed to the transformer, which mutates the current expander state to make progress, arranging for any necessary further tasks to be enqueued.

Transformers are determined as follows:

 1. If the expression is an identifer, it is resolved (see the relevant subsection). If the identifier resolves to a variable, the current core expression is filled in with a reference to the variable. If the identifer resolves to anything else, the corresponding transformer is invoked on the syntax being expanded.

 2. If the expression is a list or vector, there are two possibilities:

   a. The expression's head is an identifier. In this case, the identifier is resolved. If it resolves to a variable, then `#%app` is inserted at the beginning of the list or vector, and it is re-expanded. If it resolves to any other transformer, then that transformer is invoked on the syntax being expanded.
   
   b. The expression's head is not an identifier. In this case, `#%app` is inserted at the beginning and the syntax is re-expanded.

 3. If the expression is a signal literal, then the current expression is replaced by the signal. This should perhaps be replaced by a `#%signal` builtin, similar to `#%app`.

 4. If the expression is anything else, then expansion fails.


TODO: explain the the expansion process, and the difference between the various `Unique`s we haven't explained yet: `Binding`, `ModulePtr`, `DeclPtr`, `ModBodyPtr`, and `TaskID`.

### Resolving identifiers

The most important operation in hygienic macro expansion is being able to reliably determine the referent of an identifier. Each identifier has a scope set, and the expander maintains a binding table that relates names as written by users to a scope set and a binding. The range of the binding table represents the bindings that could in theory be available for an identifier with the appropriate name.

To resolve an identifier _x_, the first step is to find all candidate bindings. Candidate bindings are those that are named _x_ whose scope sets are subsets of _x_'s scopes. Once the candidate bindings are found, _best_ candidate is returned. If there is no unique best candidate, then expansion fails.

The best candidate binding is the one whose scope set is the largest. This allows inner bindings to shadow outer bindings.

### Quotation

Quoted syntax expands to itself. In other words, quotation leaves intact the scope sets that prior expansion has added. This means that quotations maintain lexical scoping with respect to their original position in the program.

### About #%app

In traditional Lisp systems, function application is unnamed, and is indicated by providing an expression with a non-macro `car`. In Racket, on the other hand, function application is a named operator (`#%app`) that is implicitly inserted in positions that a traditional Lisp would unconditionally consider to be an application. Importantly, `#%app` is inserted with the same scope set as the list that contains its arguments. This allows languages to provide their own notion of application, and even to locally override it using a macro.

In this language, the built-in `#%app` is a binary operator, taking only one function and argument. It can be overridden with a macro to create Curried application.

### Expanding binding forms

When expanding a binding form such as `lambda`, a fresh scope is created to represent the fact of the binding. This scope serves two roles at once:

 1. Applied to the binding occurrence, the scope ensures that only those identifiers that have been provided with the scope can refer to the binding. This is applied at all phases, because scopes on binders serve to limit scope, so using all phases makes the binding occurrence as restrictive as possible.
 
 2. Applied to the expression within which the bound name is accessible, the scope provides access to the binding occurrence. The use-site addition of the scope is performed only at the phase in which the binding should be accessible, because scopes on potential use sites serve to provide access to previously-limited scopes.
 
Understood this way, scopes can be seen as a generalization of de Bruijn indices, in which a set is augmented with a scope instead of shifting a binding. Scope sets, however, work for _multiple dimensions_ of binding, as introduced by macro expansion.

### Scopes and Expansion

TODO (but see Flatt, POPL '16)

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

### The macro monad

TODO: explain macro actions in more details.

### Stuck tasks

Many tasks have dependencies that must be satisfied before the expander can carry them out. For instance, the scope in which a macro is bound cannot be expanded before the macro itself has been expanded and evaluated. The "job queue" approach to macro expansion means that the order of expansion is not necessarily predictable from the source code itself, so operators cannot be arranged to take care of these concerns on their own.

In addition to the natural dependencies that the primitive macro operations impose on their tasks, users can impose additional dependencies. While we eventually plan to use this to allow macro expansion to block until a type variable has been solved by unification, we presently have a simpler system that captures the essence of the problem: the signal system. The expander maintains a set of signals that have been sent, and an action in the macro monad can add a new signal to this set. A further action can cause macro monad evaluation to block until a signal has been received; in this case, a continuation is captured and added to the task queue with an indication of the signal that is being waited for. If the signal has been sent, the captured continuation will be reinvoked in the next pass through the queue.


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

