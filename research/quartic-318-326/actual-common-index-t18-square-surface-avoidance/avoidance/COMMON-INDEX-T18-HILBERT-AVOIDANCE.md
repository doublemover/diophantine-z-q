# Unconditional avoidance, not finiteness, for native square matches

Fix the input-zero labels, the physical anchor, and the \(t=18\) first point. This note uses an unconditional number-field Hilbert irreducibility theorem; it neither selects an index nor gives a rational point or nonexistence result for the complete secant quartic.

## 1. The exact theorem applies to the fixed cyclic source

Let \(\mathcal A=\operatorname{Res}_{\mathbb Q(\sqrt2)/\mathbb Q} E\) and \(P=(R,R^\sigma)\in\mathcal A(\mathbb Q)\). In the two-arm chart the literal scalar function is
\[
 c=\lambda\left((1+x)^2(1+y)^2+\gamma/(xy)\right),\qquad\gamma>0.
\]
The previous surface calculation proves that the cyclic subgroup \(\Gamma=\mathbb ZP\) is Zariski dense, without an assumption about the rank of the full group \(\mathcal A(\mathbb Q)\).

For the two optional secant families define \(Q_\pm(c)=(2a_{\rm sec}c\pm2A)^2+B_0 c^2\), and set \(\delta(c)=1-\beta c^2\). Each of these polynomials has two distinct finite roots in \(c\), and has degree two. The earlier torus critical calculation works for *every* finite level of the function within parentheses, not only the plus-sign roots. The fibre has polynomial
\[
   xy\bigl((1+x)^2(1+y)^2-t\bigr)+\gamma ;
\]
it has nonempty torus support, no vertical or horizontal component, and is generically reduced since the torus critical locus is finite. The pullback to the two elliptic arms is therefore generically unramified at that support, leaving simple zeros. For any fixed rational squareclass representative \(e\ne0\), the normal covers obtained by adjoining \(\sqrt{Q_+(c)/e}\), \(\sqrt{Q_-(c)/e}\), or \(\sqrt{\delta(c)/e}\) are consequently finite, geometrically integral, ramified covers of degree two. They have no nontrivial étale subcover: a nontrivial intermediate cover of a degree-two extension would be the cover itself.

[Corvaja–Demeio–Javanpeykar–Lombardo–Zannier, Theorems 1.3–1.4](https://doi.org/10.1112/S0010437X22007746) apply over \(\mathbb Q\) to any finite collection of these covers on \(\Gamma\). Their Theorem 1.4 yields a finite-index coset on which all scheme-theoretic fibres are integral. In the chart with finite nonzero values this means a nonsplit quadratic fibre and hence failure of the stated rational square match. The same follows for an arbitrary prescribed progression \(h\equiv h_b\bmod M\): translate the covers by \(h_bP\), and apply the theorem to the dense subgroup \(\mathbb Z(MP)\). If the resulting coset inside this subgroup has index \(D\), the avoided indices are a progression modulo \(MD\) lying in the original one.

This is stronger than just an infinite complement, but is not a sparsity estimate on square matches. There is a positive-density avoided subprogression inside each prescribed progression. The closure of the set of matching integers has empty interior in the profinite topology. Neither property says that matching integers are finite or that their natural density is zero.

## 2. The no-match progression can retain the same key and Ready data

Fix a Gaussian key supplied by the existing simultaneous four-Ready handoff, along with one Ready index \(h_*\) from that handoff. This is an existential choice in the proof, not a new materialization. The key, the three contact parameters, the labels and the anchor are now fixed. Retain all original CRT residues. The same four Ready conditions hold on a further progression through \(h_*\) restricted to a nonempty open real neighborhood of its orbit point, as follows.

At the three detectors the exact squareclass identities have the form \(b_j=F_j S_j(h)^2\), where \(F_j\in\mathbb Q^\times\) is fixed by the original contact polynomial at the fixed parameter. Outside the finite set of primes dividing its numerator or denominator, valuations of \(b_j\) are automatically even. At the union of those supports and \(\{2,3,17\}\), retain the valuations and any required local square classes of the nonzero poles at \(h_*\). These are open conditions. The native all-prime progression lemma and actual detector coefficient regularity supply a progression for these finitely many neighborhoods. At the guarded point the detector folds are rational functions of those coefficients with the already-certified nonzero trace and contact denominators, so the neighborhoods apply to the literal stored poles, not replacements. The scalar support units are likewise retained, with the original square-denominator and small-place preparation following from the same native identities. Take the least common multiple of these periods and the original CRT period. At the real place, strict original guard and pole-domain inequalities remain true on an open neighborhood of the existing source point; the fixed key and literal nonpole and anchor identities are unchanged.

The real chart uses the connected compact pair of ovals with dense cyclic orbit (\(\texttt{ActualPairDensity318.pairOrbit\_dense}\), as used in \(\texttt{CompactDetectorRegion318.mixedCRT\_access}\)). Multiplication by every positive integer on that torus is surjective, so a translated subprogression remains dense on it. In particular the subprogression returned by Theorem 1.4 returns to the Ready neighborhood for arbitrarily large positive \(h\). These visits even have bounded gaps in that subprogression: the translates of the open neighborhood under the dense step cover the compact real torus, and a finite subcover bounds the waiting time. This yields genuine same-key Ready failures, not just failures in a progression that might never return to the real domain.

Applying the theorem simultaneously to \(Q_+(c)\), \(Q_-(c)\), and \(\delta(c)\) as above gives arbitrarily large same-key four-Ready indices at which **both explicit degree-two square matches fail and \(\delta\) is nonsquare**. The proof works as well for any given finite list of squareclasses for each of these three quantities, by using their twists, so their possible squareclasses along these genuine indices are not captured by a finite list. This is a statement about the exact optional square gates or square-complement escape. It does not exclude an unrelated rational slope on the same full secant quartic.

## 3. What does not follow from the literature

Ordinary Mordell–Lang controls intersections of the orbit with *closed subvarieties of the abelian variety*. The lift image in this problem is the image of *rational points* under a finite morphism whose geometric image is the whole abelian variety. There is no proper algebraic subvariety of the base to which that theorem can be applied. The [Ghioca–Hu–Scanlon–Zannier variant](https://arxiv.org/abs/1804.10561) does not fill this gap: its dimension-one additive-extension result does not cover a surface finite over a two-dimensional abelian variety with an arbitrary rational radical coordinate; the general variant discussed there assumes Bombieri–Lang. The [Xie–Yuan theorem](https://arxiv.org/abs/2308.08117) and [Guoquan Gao's extension](https://arxiv.org/abs/2511.17010) concern geometric Bombieri–Lang **over function fields**, not rational points over the number field \(\mathbb Q\). They do not give the needed arithmetic nondensity.

No unconditional finiteness theorem for this literal lift set was identified in this bounded check. Nondensity of rational lifts for this fixed cover (or only for the points over the native orbit) would suffice, by the predecessor argument that an infinite set of distinct native orbit points is Zariski dense. The Hilbert theorem proves dense avoidance, not nondensity of the lifts themselves. This is independent of the fact that the resolved plus-square surface is of general type.

## Bindings

The exact literal double-cover proof is list SHA-256 6540d554fa770d4caf5b3572c35fecc85a2bd5a02ae9872249fc7a01c88d444c and the original simultaneous four-Ready handoff is list SHA-256 9dc74e33f8afb1fdb40aae98ed766ab5bedb8f8cb63b828c4bc04f401e9b34f5. Native source SHA-256:
- DetectorLocalRegularity318.lean: 7c2012b8b0371c8e063dfca89b8437edad7b423f5f8be6df5429a0c7047a5620.
- AllPrimeSourceProgression318.lean: 964daba2756719f8a7f4fe70726ea9ce2a03a36bd66a36eb81fd98b184a23d50.
- ActualPairDensity318.lean: 79584ba0cbb1e329d8130ab87f477d4ccd104506648605c303c1caeb39233dd0.
- CompactDetectorRegion318.lean: 1c10c2100f36502e87a4c5b24eb5a733ce39b3458ad5abfc310d032c1cbf6cd7.
- ThreeDetectorUniformFamily318.lean: df9f80935c672c24ed8d095be490c4253951c69af224fbf8236d9d54737fe42b.
- AllScalarSupportPreparation318.lean: db7793cdd7327ad737a3312dcda0962096a803ddca61caf8ba90d1657604c677.

No ruling on positive witnesses, numerical evaluation, prime search, or native build is part of this note.
