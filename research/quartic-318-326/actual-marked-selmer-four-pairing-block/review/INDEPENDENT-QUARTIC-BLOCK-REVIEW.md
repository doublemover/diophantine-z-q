# Independent review: marked Selmer-four lift with a nondegenerate block

Checked exact source note 4a39d208cb35767a1ba43dcc90d91f7b2d1b62d2f2099e00417c5476c5b07b4a
and author manifest f7823f1a263c8945af34a375c271aba6ae024579c3d9f6181237eb1dd23f403f.
The author SHA checks and the entire output replay match.

The two fixed W elements differ on the actual 2-torsion lines; their cup is
the scalar bilinear cocycle (g,h) ↦ χ_a(g)χ_a(h). I checked the carry for all
16 pairs in Z/4 independently. Writing a quartic Dirichlet character as low
bit χ_a plus twice its high bit therefore makes the latter a genuine
primitive, not a cocycle wrongly placed on the elementary quotient. At any
admissible q_b each of the two local quartic summands is even, since q_b has
square residue at both p_a and q_a. Thus the restriction has Artin bit equal
to the product of the two literal quartic signs, with no cross carry or
choice of quartic orientation on the quadratic residues.

In the exact split Gaussian coordinates I independently obtained norms
1 and 9 modulo 415721. Their Euler signs are both + and their quartic signs
are opposite. The fourth powers of the two individual split components
are (16,181878) and (16,182288), so neither ray phase has a component in
mu_4. Multiplication by a Gaussian unit preserves this exclusion and the
norm. The q_a ray phase is held fixed. Both choices still induce allowed
point-order and coprimality conditions on the old governor, not a new
h index alone.

[Smith, Theorem 3.2 proof, (3.3)](https://arxiv.org/pdf/1607.07860)
applies to these two actual reference ray strata: the normalized W
elements split at both variable primes, their twist ratio is a square at
the fixed bad set, and the explicit primitive has no additional
ramification beyond p_a and q_a. The central commutators from the full
marked-row proof fix this abelian quartic field. They can therefore tune
the whole marked row on the reference with the nonzero block without
erasing that block. No generic independence of all alternating entries
is assumed.

**Pass:** rank at least two in the ordinary alternating pairing, together
with the actual full marked Selmer-four lift. This does not compute its
full radical or a global rational point. The old final conditional note
about odd parity is a sufficient route; the separate exact bridge
c717e2dca2246116e4a9f7ea3e59099b6f37462cae11ccf6c51d98f000b6e209
shows why a unique pure marked radical would already force odd corank.
No Lean or remote action.

Signed: independent reviewer, joined arithmetic lane.
