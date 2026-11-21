# The other actual full-33 comparison: one kernel at the ramified prime 3

This supplements the construction by twelve kernels in the actual A₃[11]. Over the same overlap S=Spec Z[1/33], start with the genuine fine level-eleven family A₁₁/X₁₁ of Yuan §2.1. Here 3 is invertible in every residue field in sight although 3 ramifies in the discriminant-210 quaternion algebra. Confusing these two meanings of ramification would incorrectly replace O/3 by a matrix algebra.

## The actual geometric 3-torsion is a regular module

The local algebra D₃=B⊗Q₃ is quaternion division, and its maximal order O₃ is its valuation ring. Write v for the valuation normalized by v(3)=1, and P for its unique maximal two-sided ideal. Its value group is ½Z, P²=3O₃, and its residue field is F₉: see [Voight, Theorem 13.3.11](https://jvoight.github.io/quat-book.pdf). These are facts about the acting algebra, not smoothness of the arithmetic Shimura base.

For any geometric point of X₁₁ on this overlap, the usual 3-adic Tate module T is free of rank four over Z₃ since it is the Tate module of an abelian surface in characteristic different from 3. The action of O on every 3-power torsion group extends by continuity to O₃ and, after tensoring, defines a unital D₃-action on T⊗Q₃. This is a rank-one left module over a division algebra of Q₃ dimension four. Identify it with the regular left module D₃. The O₃-stable Z₃-lattice T is exactly O₃α for an element α∈T of least division valuation: valuations of its nonzero elements are bounded below by its finite set of Z₃ generators, and discrete. For any x∈T, v(xα⁻¹)≥0, so x=(xα⁻¹)α∈O₃α. The converse is O₃-stability; note the order of multiplication. Consequently T/3T≅O₃/3O₃ as left modules, not a semisimplification. Since the multiplication by 3 maps on the geometric torsion tower are surjective, T/3T identifies with the actual geometric A₁₁[3], also at residues 2,5,7 of this overlap.

## Produce the full level by deleting one kernel scheme

Choose any nonzero class Π in P/3O₃ and lift it to O/3O (the reduction of the actual maximal order, canonically O₃/3O₃). On the actual finite étale group scheme V=A₁₁[3], let K=ker(Π:V→V). This is an open-and-closed finite étale subscheme for the same diagonal argument as in the tame eleven proof. Fibrewise, in the regular left module, Πx=0 modulo 3 iff v(x)≥½, since any lift of Π has valuation ½. The kernel is exactly the radical P/3O₃, of size nine; its complement is the unit locus in O₃/3O₃. Therefore

    R₁₁ = A₁₁[3] minus ker Π

is a finite étale scheme of degree 81−9=72, independent of the nonzero choice of Π. A point x of this complement is exactly the value at 1 of a full 3-frame, by the same O-linear evaluation a↦ax. This criterion is valid for nonreduced test bases: every proposed frame is a morphism of finite étale schemes, and it is an isomorphism exactly when it is one on geometric fibres.

Adjoin the resulting actual full 3-mark to the retained 11-mark using the projector CRT [22]/[12]. This identifies R₁₁ with the same full principal-33 moduli scheme as the tame construction. Its actual family is R₁₁×ₓ₁₁ A₁₁, the unchanged polarized surface with the same zero; the projected full 11-mark is unchanged. Under the common representing property both new constructions have the **same** universal polarized family and actual full marks up to their unique fine-moduli isomorphism. No coarse product or relative sign quotient enters.

It follows that the one actual generic 33-mark determines both cartesian family comparisons used in the three-level gluing, without an independent chosen forgotten family or overlap isomorphism. The finite section of R₁₁ over the restriction of the integral level-eleven section has the same prescribed generic 33-mark, and extends uniquely over the same normal integer-away base by the finite algebra proof of the tame packet. These two full-33 extensions are the same on Spec O_L[1/33], by separatedness and the common generic map. There is no claim of a full 3-frame at residue 3 or 11-frame at residue 11.

The replay uses the literal skew ring F₉⊕F₉Π with Π²=0 and Πa=a³Π from the unramified local normal form. It checks all 81 elements, all products, both inverse equations on the 72 generators, and all ordered multiplication triples. It is a finite actual residue-ring check, not a computation of the selected surface or Lean formalization of PEL representability.
