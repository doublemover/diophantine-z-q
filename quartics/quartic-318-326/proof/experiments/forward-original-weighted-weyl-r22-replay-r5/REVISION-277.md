# Narrow hosted277 contact-weight repair

The exact first failures are source rows164 and217 and the scaled weight limit. Both row failures came from expanding the contact polynomial before clearing its denominator: the known factored nonvanishing hypothesis no longer matched a normalized quartic inverse produced by field_simp. This revision proves the literal identity contact(parameter)*scaledWeight=c^10*delta^2 with the denominator still intact. Each failing row is then identified by a polynomial ring identity with (contact*scaledWeight-c^10*delta^2)*delta^3 and vanishes by that identity. No nonvanishing condition is added and no source row changes.

For the limit, the target is explicitly changed to its definitionally equal lambda function before applying const_mul and composition. This avoids the opaque partially-applied scaledWeight mismatch. The same original weight, parameter, limit and hypotheses remain.

All682 other Lean modules, including every new local-image proof, are byte-identical to683r1. The exact hosted log and a symbolic/finite regression are bound. No local Lean or resource changes. Independent review and hosted replay remain required.
