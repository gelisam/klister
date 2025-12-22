Here's a simple type-driven macro.
```
#lang "prelude.kl"
(import (shift "prelude.kl" 1))
(import "define-syntax-rule.kl")

(define-macro (convert)
  (>>= (which-problem)
    (lambda (problem)
      (case problem
        [(expression fun-type)
         (type-case fun-type
           [(-> arg-type _)
            (type-case arg-type
              [Integer
               (pure 'integer->string)]
              [String
               (pure 'string->integer)])])]))))

(example
  ((convert) 42))
-- => "42"
```

Since the macro is type-driven, we need the type-checker to calculate the type of `42` before the macro-expander can figure out that `(convert)` expands to `integer->string`. And then the type-checker needs to run again in order to verify that `(integer->string 42)` is well-typed and has type `String`. Which, in a more complicated example, could allow another type-driven macro to be expanded, and so on. 

In other words, we have to interleave macro-expansion and type-checking, we cannot run one phase and then the other.

Before we look at their interleaving, let's review each phase on its own, starting with macro-expansion (ME). 

ME1. Expand `((convert) 42)`. It's a function application, so recur on `(convert)` and `42`.
ME2. Expand `(convert)`. It's a macro, execute its body. The body calls `type-case` on the type of `42`.
ME3. Assuming that the type-checker has figured out that `42` has type `Integer` by now, the body completes its execution and outputs `integer->string`.
ME4. `integer->string` is an identifier, it expands to itself. 
ME5. `42` is an integer literal, it expands to itself. 

Taking everything together, the expansion is `(integer->string 42)`. Let's look at type-checking (TC) next. 

TC1. Type-check `((convert) 42)`. It's a function application, so recur on `integer->string` and `42`.
TC2. Assuming that the macro-expander has figured out that `(convert)` expands to `integer->string` by now, type-check `integer->string`. It's an identifier, and the environment says it has type `(-> Integer String)`.
TC3. Type-check `42`. It's an integer literal, it has type `Integer`.
TC4. Combine the `(-> Integer String)` and `Integer` results to conclude that `(integer->string 42)` is well-typed and has type `String`.

If we swapped the order of TC2 and TC3, the algorithm would still make sense. But it would not make sense to move TC4 any higher, since it depends on the output of both TC2 and TC3. Steps are partially ordered by their dependencies. And steps from one phase can depend on steps from the other phase: TC2 depends on ME3, and ME3 depends on TC3. To interleave macro-expansion and type-checking, we must divide each phase into individual steps, which we call "tasks", figure out the dependencies between them, and execute the tasks in an order which satisfies the dependency constraints. 

One difficulty is that we don't know all the tasks and dependencies in advance. For example, it is only after we have started executing the macro body in ME2 that we realize that it calls `type-case` and thus that the rest of the work needs to be done in a new task, ME3, and that this task depends on TC3. In particular, at the time when we realize that TC2 depends on figuring out what `(convert)` expands to, the ME3 task which answers this question does not yet exist.

Klister's solution is that tasks don't depend on other tasks, they are blocked until a particular problem is solved. For example, ME3 is blocked until a particular type variable is solved, that is, until we know its outermost constructor. And TC2 is blocked until the expansion of `(convert)` is known, that is, until we know its outermost constructor.

In the Klister codebase, we know that a type-checker problem has been solved if a particular `TypePtr` (a unification variable) is filled, and since the macro-expander expands an s-expression (a Syntax value) into a Core AST, we know that a macro-expander problem has been solved if a particular `CorePtr` (an "expansion variable"?) has been filled. When tracing through the inner-workings of unification, I like to use the syntax `?1` to represent type variables, so I will use `!1` to represent expansion variables.

Let's use this notation to step through the macro-expansion and type-checking of `((convert) 42)`. We start with two tasks: expand `((convert) 42)` to solve `!0`, and type-check `((convert) 42)` to solve `?0`. We put both of those in an unordered "task pool". Running a task may either solve its goal or add more tasks to the task pool which will make progress toward solving that goal. The interleaving algorithm is to keep running unlocked tasks until either all the tasks are blocked (an error case) or no tasks are left (success). If there is more than one unblocked task, they can run in any order.

```
?0 = ?

!0 = ?

Task Pool:
ME1. !0 = expand `((convert) 42)`
TC1. ?0 = type-check !0 (blocked on !0)
```
Running ME1 solves `!0`, adds `!1` and `!2`, and adds two more macro-expansion tasks.
```
?0 = ?

!0 = (!1 !2)
!1 = ?
!2 = ?

Task Pool:
TC1. ?0 = type-check !0 (unblocked)
ME2. !1 = expand `(convert)`
ME5. ?2 = expand `42`
```
Running TC1 solves `?1`, adds `?1` and `?2`, and adds two more type-checking tasks. Since we use unification, we don't need to add TC4.
```
?0 = ?
?1 = ?2 -> ?0
?2 = ?

!0 = (!1 !2)
!1 = ?
!2 = ?

Task Pool:
TC2. ?1 = type-check !1 (blocked on !1)
TC3. ?2 = type-check !2 (blocked on !2)
ME2. !1 = expand `(convert)`
ME5. ?2 = expand `42`
```
Running ME2 adds one more macro-expansion task.
```
?0 = ?
?1 = ?2 -> ?0
?2 = ?

!0 = (!1 !2)
!1 = ?
!2 = ?

Task Pool:
TC2. ?1 = type-check !1 (blocked on !1)
TC3. ?2 = type-check !2 (blocked on !2)
ME3. !1 = continue after the type-case (blocked on ?2)
ME5. ?2 = expand `42`
```
Running ME5 solves `!2`.
```
?0 = ?
?1 = ?2 -> ?0
?2 = ?

!0 = (!1 !2)
!1 = ?
!2 = 42

Task Pool:
TC2. ?1 = type-check !1 (blocked on !1)
TC3. ?2 = type-check !2 (unblocked)
ME3. !1 = continue after the type-case (blocked on ?2)
```
Running TC3 solves `?2`.
```
?0 = ?
?1 = ?2 -> ?0
?2 = Integer

!0 = (!1 !2)
!1 = ?
!2 = 42

Task Pool:
TC2. ?1 = type-check !1 (blocked on !1)
ME3. !1 = continue after the type-case (unblocked)
```
Running ME3 adds one more macro-expansion task.
```
?0 = ?
?1 = ?2 -> ?0
?2 = Integer

!0 = (!1 !2)
!1 = ?
!2 = 42

Task Pool:
TC2. ?1 = type-check !1 (blocked on !1)
ME4. !1 = expand `integer->string`
```
Running ME4 solves `!1`.
```
?0 = ?
?1 = ?2 -> ?0
?2 = Integer

!0 = (!1 !2)
!1 = integer->string
!2 = 42

Task Pool:
TC2. ?1 = type-check !1 (unblocked)
```
Running TC2 unifies `?1` with `Integer -> String`, solving `?0`.
```
?0 = String
?1 = ?2 -> ?0
?2 = Integer

!0 = (!1 !2)
!1 = integer->string
!2 = 42

Task Pool is empty
```
The interleaving algorithm succeeds with `!0 = (integer->string 42)` and `?0 = String`.
