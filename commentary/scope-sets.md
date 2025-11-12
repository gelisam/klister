A "scope" intuitively means a region of code where some variables are visible. In a language without hygienic macros, scopes are neatly nested within each other, and when multiple bindings bind the same name, the innermost binding wins:
```
-- example 1
(let [x 1]    -- call this binding "x1"
  -- scope 1 begins {
  (let [x 2]  -- call this binding "x2"
    -- scope 2 begins {
    x         -- at this reference, both x1 and x2 are visible, but x2 wins.
    -- } scopes 2 ends 
  )
  -- } scope 1 ends
)
```

In a world with macros, the situation is more complicated. 
```
-- example 2
(let [x 1]         -- call this binding "x1"
  (my-macro [x 2]  -- call this binding "x2"
    -- which bindings are visible here depends
    -- on which code my-macro produces
    x))
```

Let's say that `(my-macro [y 2] y)` expands to
```
(let [x 3]  -- call this binding "xM"
  (let [y 2]
    (+ x y)))
```

The goal of hygienic macros is to make sure that even if the caller of `my-macro` happens to pass `[x 2]` instead of `[y 2]`, it should not affect the binding structure of the result: the two arguments to `+` should still refer to two different bindings. So we want example 2 to expand to this: 
```
-- example 2, expanded
(let [x 1]      -- call this binding "x1"
  (let [x 3]    -- call this binding "xM"
    (let [x 2]  -- call this binding "x2"
      (+ x      -- xM should win here
         x))))  -- but x2 should win here
```

Obviously we cannot use the "innermost binding wins" algorithm here, or x2 would win at both use sites. We need a more complicated algorithm, the "scope sets" algorithm. 

In this algorithm, each location in the AST is tagged with a set of `Scope` values. Two `Scope` values can be compared for equality, and that's it, there are no other operations on `Scope` values. Here is how the scope set algorithm works in example 1:
```
-- example 1, scope sets
(let [x 1]    -- binding x1, tagged with scope 1
  (let [x 2]  -- binding x2, tagged with scopes 1 and 2
    x))       -- tagged with scope 1 and 2;
              -- x1 and x2 are both visible but x2 wins
```

For bindings, the tagged scopes indicate _requirements_: only the use sites which can see all those scopes can see this binding.

For use sites, tagged scopes indicate _visibility_: the use site can see all the bindings which require those scopes. 

So the reason x1 and x2 are both visible is because the use site is tagged with both scopes, which fulfills both sets of requirements. The reason x2 wins is because its scope set is strictly bigger than x1's, so it shadows x1. It is possible to construct weird situations in which no variable shadows all the other variables, in which case the code is ambiguous and Klister rejects the program.

Let's now look at example 2. The parts which are lexically within binding x1 _before_ `my-macro` is expanded will be tagged with scope 1:
```
-- example 2, scope 1
(let [x 1]  -- scope 1
  (my-macro
    [x 2]   -- scope 1
    x))     -- scope 1
```
becomes
```
-- example 2, scope 1, expanded
(let [x 1]      -- scope 1
  (let _
    (let [x 2]  -- scope 1
      (+ _
         x))))  -- scope 1
```

The parts which are lexically within the `my-macro` definition will be tagged with scope M:
```
(define-macro (my-macro binding expr)
  (pure `(let [x 3]      -- scope M
           (let ,binding
             (+ x        -- scope M
                ,expr)))))
```
becomes
```
-- example 2, scope M, expanded
(let _
  (let [x 3]  -- scope M
    (let _
      (+ x    -- scope M
         _))))
```

The last binding, `(let [x 2] _)`, only appears after `my-macro` is expanded, so this time it is the parts which are lexically within binding x2 _after_ `my-macro` is expanded which are tagged with scope 2:
```
-- example 2, scope 2, expanded
(let _
  (let _
    (let [x 2]
      (+ x      -- scope 2
         x))))  -- scope 2
```

Bringing all the scopes together, we get:
```
(let [x 1]      -- binding x1, scope 1
  (let [x 3]    -- binding xM, scope M
    (let [x 2]  -- binding x2, scopes 1 and 2
      (+ x      -- scopes M and 2;
                -- only xM is visible, xM wins
         x))))  -- scopes 1 and 2;
                -- x1 and x2 are visible, x2 wins
```

As desired.
