# Independent actual-generic-signs repair review

PASS for source/application contract only. Reviewer: arithmetic_lean. No local Lean or Lake was run. Candidate remains hosted-unverified.

Exact base: 2e4471d08710d58a1fdc2353b62a30023d88e94e. Independently compared the before source to the zero46 Git blob: byte-identical. All four supplied bindings match. A complete text reconstruction using precisely the three displayed proof substitutions equals the after source, so definitions, statements, imports, domains and resource options are unchanged.

I independently fetched hosted job 132624148956 from run 43652368511: the checked-out SHA is the exact base above; FourRootActionStabilizers318 exited 0 in 2.472 seconds and FourRootActualGenericSigns318 exited 1 in 3.574 seconds. The supplied per-module log exhibits the two sign simplification goals, underdetermined Algebra metavariables, and final affineEmbedding composition mismatch. No full packet acceptance is inferred from these prefix results.

## Three fixes against actual native definitions

1. FourBinaryCharacters318.coordinate and signPattern both test whether the additive value of the same bit is zero. The observed simplifier normalizes this to g i = 1. Splitting on that exact normal form preserves both exhaustive cases, the original four-bit group, every index and arbitrary element of any complex algebra. The plus/minus scalar factors are unchanged.
2. FourRootOrderSigns318.signEquiv is the actual fourfold tensor algebra equivalence over the polynomial base, built from the four existing sign involutions. After finite_base and toTensor_base, its commutes theorem at Polynomial.X is exactly the required symmetry. Specifying this equivalence and this polynomial eliminates underconstrained base/algebra metavariables; it does not introduce an arbitrary or replacement map.
3. FourRootActualGenericField318.affineEmbedding is definitionally embedding composed with the exact affine-to-tensor equivalence. The revised change exposes that same composition on both sides, then uses the existing tensor_equivariant and embedding_equivariant equalities. The full affine coordinate-ring element remains arbitrary. No evaluation restriction, point bijection, field/domain assumption or injective-branch premise is added.

## Nine-obligation contract

APPLICATION.md correctly records unchanged inputs and actual objects; complete sign/index/ring-element coverage; the literal tensor/base-change maps; plus/minus scalar factors; identity with the consumed polynomial and affine embedding; absence of new exceptions; future all-copy propagation rather than assumed propagation; and the boundary between source review and pending hosted elaboration/recursive axiom audit. No mathematical application blocker found.

The exact candidate must still be tested by hosted Lean. This review does not claim the new simplification or definitional reductions have elaborated, nor that downstream evaluator/geometry modules were reached. Historical packets must remain unchanged; future successors need their own native intake and exact-copy binding audit.

- `before/FourRootActualGenericSigns318.lean` SHA-256: `81a81ac7a216622c4646f922cb26720a6340ad4d7a7d1d2f706bdf1c34ba7d8d`
- `after/FourRootActualGenericSigns318.lean` SHA-256: `1beea6db801ac03ce2d6f30dba0268b48db8ff71b034962c95f3054910b9666f`
- `APPLICATION.md` SHA-256: `2e657f41cc8bbf05dcde9008eac6dafa0260633d494b937d9331057bdbd9cf15`
- Independent dependency/binding manifest SHA-256: `0246f8ee3569c0939431161ee4cb86dca0bf46822db1fd93053b50babe63c94f`
