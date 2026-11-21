# TZ39 single-site repair after exact hosted r11

Exact run 44870370462, raw inventory
600c6e3c7840d81c1923256c7754a92152f1fc8da0572fb0092be08755bccd50,
36/39 compiled and 530 declarations audited. One direct diagnostic,
same CanonicalWrap owner, at L139. The r11 cardinality repair was
verified and remains unchanged, as do the new explicit rename steps.

The diagnostic compared a physical polynomial containing the whole
unapplied function L.actualSlope to the same polynomial with the
literal lambda j ↦ primorial(y)·L.divided(j). Simplifying a definition's
applied equations does not rewrite this function-valued argument.
State the exact typed equality of functions, prove it pointwise by
rfl in the same owner, and rewrite that named equality under the
physical polynomial/map. No other proof hunk, import graph, theorem
statement, source parameter or peer Lean byte changed. Same canonical
ordered 39. Static successor only; not a hosted run.
