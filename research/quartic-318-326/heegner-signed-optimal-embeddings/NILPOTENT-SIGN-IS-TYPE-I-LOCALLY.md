# The direct nilpotent sign is the Type-I local weight, up to its base sign

This is a short supplement to a432a3e5…. The full direct replay is independent of the shrinking two-coefficient calibration, but the local signed arithmetic is not a new species of theta weight.

Fix an odd ℓ|d, a split M₂(F_ℓ) frame and its area form ω. For any rank-one nilpotents U,V, write
```
Ux=c e·ω(e,x),    Vx=f b·ω(b,x)
```
for nonzero e,b and c,f∈F_ℓ×; this is possible since image and kernel are the same line. The direct sign is η(U)=(−c/ℓ), independently of the scale of e; likewise η(V)=(−f/ℓ). If the two lines are different,
```
tr(UV) = −c f·ω(e,b)²,
(−tr(UV)/ℓ) = η(U)/η(V).
```
If they are the same, U=aV and η(U)/η(V)=(a/ℓ).

Let x,z be quotient-order vectors and U=2x−tr(x), V=2z−tr(z) the corresponding trace-zero matrices. Their discriminant Δ is half the trace of the square of the trace-zero matrix. Thus its associated bilinear expression Δ(x+z)−Δ(x)−Δ(z) is tr(UV). [Sirolli–Tornaría §4.1, Type I](https://arxiv.org/html/2107.04483#S4.SS1) uses the quadratic symbol of the negative of this pairing when it is nonzero, and the scalar character when the two isotropic classes are proportional. Consequently in the exact same split frame its Type-I function at the admissible nonzero isotropic vectors is η(U)/η(V) for its chosen reference V. In particular the old script's `b=(disc_(x+z)-disc_(x)-disc_(z))/9` has this sign, since `disc_=-9Δ`.

In the direct optimal embedding formula one can take each V to be the actual base embedding and get exactly that local Type-I factor, with the norm-gauge contribution still required globally. This identifies precisely what is and is not “dual”: the direct calculation uses the one moving-auxiliary shell |(−d)·(md)|=md² with primitive mark, level and residue orientation filters; the old shorter determinant certificate uses two fixed-auxiliary shells |37·(−d)| and |(−35)·md| plus global calibration. Only the local Type-I factors have been identified here. There is no assertion that the whole directly oriented count is a particular old ST eigenform (the other places and their weighted projections differ), nor any complexity gain for moving q.
