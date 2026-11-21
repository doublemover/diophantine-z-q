# One denominator saturation routes all shared contact primes in the three original rows

This is a finite exact design for choosing a common square t for
the three original detector scales. It removes accidental shared
odd primes without a factorization of the scales. It does not
supply a complete compatible t, h or PointPair.

Fix the actual four labels and hence the literal scales c_j,
j=0,1,2, written in reduced form m_j/n_j with n_j>0 and m_j!=0.
Write the five exact original roots of F as θ_i=a_i/b_i,
b_i>0, coprime; they are 0, −1/2, −1, 1/2399, −32/407.
The original F is monic and F(T)=product_i(T−θ_i).

For primitive t=(r/d)^2, define the integer cleared factors

    K_{ji} = b_i m_j² r² − a_i n_j² d².

Then literally, for the same t and all three j,

    c_j²t−θ_i = K_{ji}/(b_i n_j² d²).

The rational unscaled-root slots are s_{ji}=θ_i/c_j². The
slots with θ=0 are identical and will contribute only even orders
outside fixed coefficient primes. Partition all other slots by
equality of s_{ji} in Q, not by equality of indices or by
a guessed modular collision.

## One explicit denominator removes the entire accidental locus

Set B to the product of the following positive integers (absolute
values if necessary; omit zero entries):

- 76176!, to include every fixed below-threshold prime;
- every scale numerator and denominator |m_j|,n_j;
- every root numerator and denominator |a_i|,b_i for a_i != 0,
  and every nonzero |a_i−b_i|;
- the absolute value of every nonzero cross determinant

      a_i b_l n_j² m_k² − a_l b_i n_k² m_j²

  for all pairs of slots with *different* rational roots s_{ji},s_{kl}.

This is a finite arithmetic circuit in the actual fixed scale
data. No factoring is used to form B. Use d=B^N with N>=2 and
choose any r>0 coprime to B. One can take r=1+mB for arbitrarily
large m; choosing even greater N is compatible with these choices.

At p|B, write k=v_p(B)>0. For every j, |v_p(c_j)|<=k, and every
nonzero θ_i has |v_p(θ_i)|<=k. Since r is a unit, exactly

    v_p(c_j² t)=2v_p(c_j)−2Nk <= −2k < v_p(θ_i).

For the root zero the valuation of the linear factor is unchanged
as well. Therefore at *every* p|B and in every j, including
nonunit scales, negative contact valuations are

    v_p(F(c_j² t)) = 5 v_p(c_j² t),

always even. The actual nonzero pole has valuation of the same parity
by the exact squared trace factor and even denominator powers. Thus
nothing in this entire fixed accidental locus can be an odd
contact, regardless of the h choice. This includes universal 2399,
and 407 when one chooses the optional Pythagorean branch, without
using independent Pythagorean constraints on the other scales.

At p not dividing B, all c_j,b_i,n_j,d and nonzero a_i are
units. If p|r only root zero can occur and its depth is even.
Otherwise an odd contact comes from a unique rational root class:
two integer factors K_{ji},K_{kl} of distinct classes vanishing
would imply p divides their nonzero cross determinant. This is
impossible by construction of B. If two slots are in the same
nonzero rational class, their p-values agree exactly, not just
with the same parity, since

    c_j²t−θ_i = c_j²(t−s_{ji})

and all scales are p-units. In a single scale the five roots
are distinct, so one class has at most one slot there. No
odd-support double counting occurs within a row.

At every odd contact p the scale is a unit and the corresponding
Delta_j=c_j²t−1 is a unit (the exact θ_i−1 numerator was
put in B); also p>76176. Thus once actual support is known
the one-prime fold/CRT methods apply at every odd incidence.
For a shared rational root class they use *one* prime orientation
and index, with each of its incident folds checked at that same h.
The early-eight orientation is uniquely determined by h at p,
so shared incidence is not permission to choose separately for
each scale. The full-order sufficient CRT specialization and
exact sixteen-leaf local thresholds are those in 2046e97f/f94a6177.

## What this does and does not construct

This constructively saturates all fixed bad contacts and all
accidental collisions across the three literal rows, while retaining
one common square t and their exact original scales. If the
old real or 2/3/17 pole gates impose deeper bounds on d,
increase N before choosing the numerator and use those original
open-region proofs; the saturation statement itself makes no
such scalar or real claim.

Still needed are the actual remaining prime supports of K,
and an orientation/depth-compatible h for *all* of them.
For instance, the independently checked complete split support
of one unscaled t in 04e2554e fails a local h orientation even
after its fixed denominator saturation. No assertion that r
can be chosen with all the needed prime properties or that
a rational PointPair exists is made here. There is no Lean claim.
