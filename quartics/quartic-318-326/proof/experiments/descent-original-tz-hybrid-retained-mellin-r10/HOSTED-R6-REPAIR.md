# Exact TZ mean replay r7: two directly diagnosed proof owners

Observed predecessor r6 run 44860358428, intake
0ecb9b757c8d92d475f2e6c2453da56de5b1bce1789bddffaa5cce756f947b18:
33/39 compiled with 492 declarations strictly audited; 2 directly
diagnosed, 4 blocked. The previous inverse-index Nat projections,
width bound, coefficient at zero and exact probability proof all
pass this observed run and are unchanged.

- HybridGrid: in the left inverse invoke the already-green
  `unflat_pack` directly at each of the concrete old signed coordinates.
  The two case distinctions now reduce in the literal digit definitions
  rather than matching a Boolean coercion's Decidable with a simp lemma.
- IntegerGridMarker: the convenience theorem for totalDegree only
  accepts a common coefficient ring. Use finite support `sup_mono`
  directly across Z → ZMod p: the exponent type and sum functional
  are identical on the two supports. The exact support inclusion
  from r6 is already elaborated and is retained verbatim.

Raw-source and log hashes verified. All other 128 Lean source files
are byte identical; module ABI, import-name graph, and selected 39
names/order unchanged. No Lean or remote operation performed here.
