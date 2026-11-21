# Cleared regular formula for mixed Weber translation at an odd place

This supplies exact equations for the first paragraph of §4 of the
chosen-torsion specialization note. Take a nonzero point T in the
identity chart with t in the maximal ideal, w+t w²=t³, and d=1+t w.
Then d is a unit, d²−d=t⁴, and T=(d/t²,−d/t³) on the generic
affine chart. Fix P=(x,y) integral on y²=x³−x. Define

    A=d−x t², B=d+y t³,
    C=2dy+d(3x²−1)t+(y²−2x³)t³.

A has residue 1, so T cannot have the same x as P and the ordinary
secant is l=−B/(tA). Direct expansion gives

    B²−d A²−2xt²A²−t³C = −d(d²−d−t⁴) = 0.

It follows, **exactly**, from the actual affine addition formula that

    x(P+T)=x+t C/A²,        y(P+T)=−y+B C/A³.

There is no formal inverse, analytic remainder or change of local
parameter in this clearance. These generic coordinates are integral.
They reduce to x and y because A and B reduce to 1 and C reduces to
2y. The paper-level translation argument can thus use this single
field/ring identity for both coordinates. Native source proves the
cleared identity, slope and both regular field expressions as well as
the actual integral witnesses and residues. The companion mixed-point
module connects these witnesses to the literal Mathlib affine group
sum via the pinned `Point.add_of_X_ne`, `slope_of_X_ne` and exact
point constructor. It still takes the literal origin/ordinary shape
and both points' nonsingularity as inputs. It does not construct
the whole point specialization or prove the other local branches.
