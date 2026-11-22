# Lift the same literal positive period through its named closure, revision 2

Official revision 1 accepted fifty-four of fifty-five selected modules
and strictly audited 1170 declarations. Its sole new receiver failed at
two proof sites. At L85 the mapped cubic expects e.toRingHom applications,
so name both coordinate equalities in that exact coercion before simp.
At L142 the actual input is n*(1/n), so expose one_div and cancel rather
than using the forward rule for a product already written over n.

These are the only proof changes. No hypotheses, theorem statements,
imports, peer source bytes, or heartbeat limits change. Text-only
repository proof evidence, no new acceptance claim.
