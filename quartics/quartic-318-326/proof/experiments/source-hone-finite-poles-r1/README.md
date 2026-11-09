# Original finite-chart witnesses for high infinity poles

This seven-source packet is uncompiled. Hosted strict checking, recursive axiom
audit and independent acceptance are pending. Six sources are copied exactly
from whole-principal-r2. No local Lean run occurred.

The new ContactFinitePoleReduction318 uses the actual source generators and the
original infinity coordinates u=c0/y0 and v_j=y_(j+1)/y0. The weight d of an
infinity basis monomial is the sum of its three binary exponents. For any e>=0,
u^(-(d+e)) times that monomial equals c0^(-(d+e)) times y0^e times the product of
the indicated finite root generators. The latter is explicitly constructed in
the original finite-chart ring. The theorem is an equality in the original whole
overlap ring, reflected through its already proved injective field embedding.
The full original c0 normalization is retained; no scalar is discarded.

pole_of_weight_le covers every pole k>=d by choosing e=k-d. This is the concrete
finite-chart reduction needed to remove high poles from the preceding principal
representatives. It does not itself identify a rational H1 module structure,
prove independence, or compare these classes to quotient pullbacks.

The consequence to prove next is that only positive pole orders k<d can survive.
Among three binary exponents there are three weight-2 monomials (k=1) and one
weight-3 monomial (k=1 or 2), giving five candidate terms. This counting and the
complete polynomial-coefficient expansion into those terms are not claimed by
this packet. In particular a five-dimensional H1 theorem remains open.

The source join was read directly: finiteGenerator_embedding uses the original
four-root coefficient-change map to the actual contact field; infinity_embedding
uses the original ratio monomials; inverse_u_embedding is the actual overlap
inverse, and orderToOpen/openEmbedding_on_order uses the original finite chart.
The rational algebra selection matches the original coordinate modules.
