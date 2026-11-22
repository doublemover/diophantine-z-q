# The exact fixed isogenous first curve has six 2-primary Sha directions

Use the complete baseline \(t_*=18\) arithmetic of the earlier literal input-zero scalar, \(h=328655617654071015360\), but in this note **only the fixed first curve** and its rational isogenous curve are evaluated. Put
\[
 F=E_n:\ y^2=x(x-n)(x+3n),\qquad
 G_0:\ y^2=x(x^2-4nx+16n^2),\qquad n=\beta(1-324\beta)(1-2916\beta)
\]
with the archived \(\beta=204618888056724185\) and full \(n\) factorization. Let \(\phi_0:F\to G_0\) be the zero-root isogeny and \(\hat\phi_0\) its dual. The fixed first-side certificate exhausts the local Kummer groups and computes full \(\operatorname{Sel}_2(F/\mathbb Q)\) of dimension three; its actual marked point is nontorsion, independently of real or root-number reasoning. With two independent rational 2-torsion roots this gives rank exactly one and equality of the Selmer group with the rational Kummer image. The Kummer sequence gives \(\Sha(F/\mathbb Q)[2]=0\), and hence \(\Sha(F/\mathbb Q)[2^\infty]=0\): a nonzero 2-power-order element would have a nonzero multiple killed by two. No rank conjecture, Sha finiteness, or condition on the moving companion is needed.

The exact dual-isogeny Selmer group \(\operatorname{Sel}^{\hat\phi_0}(G_0/\mathbb Q)\), in the \(x\)-class convention on \(F\), has dimension **nine**. Here is a replay using no new elliptic calculation. The original complete local groups of \(F\) modulo doubling in the two Kummer slots are archived. Project each to its \(x\)-slot; this gives its entire \(\hat\phi_0\)-Kummer image since \([2]=\hat\phi_0\phi_0\). Signed support is on \(-1,2,3\) and the fifteen odd primes of \(n\). Away from those places the curve has good reduction, and the full rational split \(2\)-torsion gives precisely the unramified local squareclasses in this slot. At infinity both signs occur (the identity and the class \(-3\) at the zero root). Thus the projection and row reduction of the pinned finite table give the whole isogeny Selmer group, not just a necessary screen. The eighteen signed columns give independent row masks
\[
                     2,\ 212317,\ 244450,\ 155903,\ 6418,\
                     196026,\ 203984,\ 60082,\ 21127
\]
at \(2,7,109,163,661,733,1489,1861,833212819\) in that order. The replay verifies independence and that no additional rows occur.

The exact rational \(x\)-image is spanned by \(\beta,-3,n\). Indeed the proved basis of \(F(\mathbb Q)/2F(\mathbb Q)\) may be taken to be \(P\) and the roots at 0 and \(n\); their \(x\)-classes are exactly these three, independent by the fixed prime factorizations and sign. The usual isogeny Kummer sequence therefore gives
\[
                    \Sha(G_0/\mathbb Q)[\hat\phi_0]
                         \simeq(\mathbb Z/2)^6.
\]
This already equals the whole \(2\)-primary group of \(G_0\): its image under \(\hat\phi_0\) lies in the zero \(2\)-primary group of \(F\), and its kernel is killed by \([2]=\phi_0\hat\phi_0\).

This does **not** give the relative restriction map on these six directions, nor the \(2\)-primary group of \(G=G_0^\delta\). In particular the reverse trace principle that used vanishing of the first curve's rational \(2\)-primary Sha on \(F\) cannot simply be carried across the isogeny to \(G_0\). Restriction–corestriction only says that a class killed on quadratic restriction is killed by two, and all six directions already are. The forward h328 bare bit still needs the *moving* integral trace image computed or obstructed; an isogeny, first-side rank, or fixed group order alone does not do that. No new literal support, point, rank or push is claimed.

Exact input: old full Kummer replay SHA-256 7c94388b54349fe6247aa8baace6cbba3f94db8f3c6e2f8e4717308d5cf96d0f in the unchanged sibling original-a0-h328-t18-known-nine-pure-second-r1; old first-rank paper SHA-256 57875a3c1c2d7a5c8e57fcd46b4f978e95895c9a511f830f59561a590bb2cf65. New integral trace theorem for the bare bit is the separate f7be5f6566f15b3f79563ddac9155254e154e85ccbd9c39abf85b5f97bc6ae8e packet.

~~~sh
sha256sum -c SHA256SUMS
python3 -B replay_fixed_dual_projection.py | cmp - EXACT-FIXED-FIRST-DUAL-SELMER.json
~~~
