# The exact 17 and 673 operators on the fixed helper-673 frame space

At the verified local helper $I=673$, the literal first-arm discriminant always has the fixed prime 17 and the ramified helper 673. The rigid Hecke parity criterion needs both finite operators. A deck-coordinate description realizes them with **1,008** degree-17 rows and **56** relative-Frobenius rows, rather than expanding all 344,064 rigid frames. The moving prime operators and the original mark are not evaluated.

## Field, curves, and the finite certificate

The replay uses $\mathbf F_{673}[z]/(z^{32}-c)$ with $c$ a fixed element of order 32. This binomial is irreducible: every root has order 1024 (its 32nd power has order 32), and 673 has multiplicative order 32 modulo 1024. Subfields of degrees 2 and 4 are represented by the usual powers of $z$. The exact file of monic degree-one/two factors of the Deuring Legendre polynomial is product-checked against
$$
   \sum_{j=0}^{336}\binom{336}{j}^{\!2}X^j .
$$
Its roots give the complete supersingular $j$-set via $j=256(1-\lambda+\lambda^2)^3/(\lambda^2(1-\lambda)^2)$; over $\overline{\mathbf F}_{673}$ every elliptic curve admits a Legendre presentation. There are exactly 56 distinct $j$'s, none 0 or 1728. For each take $A_j:y^2=x^3+3d x+2d$ with $d=j/(1728-j)$.

Every such $A_j$ over $\mathbf F_{673^2}$ has square Frobenius a scalar $\pm673$ (the standard supersingular scalar-square representative and its quadratic twist, since geometric automorphisms are exactly signs). Thus on $\mathbf F_{673^{32}}$ the 17-torsion can be found by projecting with $(673^{16}-1)/17$, and the full needed 96-torsion is within $\mathbf F_{673^4}$ by $96\mid673^2-1$. The deterministic point search itself only proposes candidates: the replay verifies exact torsion orders and **all distinct points** of the generated $17^2$, $32^2$, and $3^2$ tables. These force complete bases even without a point-count heuristic.

For each source $j$ enumerate the 18 projective lines in that 17-torsion basis and exactly the associated kernel points. Vélu's quotient and coordinate functions are evaluated on the two 32-basis and two 3-basis points. The computed quotient $j$ is among the 56 names. A scaling isomorphism to its chosen model is checked on both curve coefficients; its possible sign is a simultaneous sign on the residue matrices, harmless for the target frame isomorphism class. Reading the four image points in the exact torsion tables gives two $2\times2$ matrices, modulo 32 and 3, respectively. Rows are images of the two source basis vectors, so a coordinate **row vector** is multiplied on the right. The code checks every image on the exact quotient curve, confirms all matrix blocks are invertible, matches a reverse degree-17 row whose composition is $\pm[17]$, and checks all Frobenius/degree-17 commutation multisets modulo simultaneous sign.

The 673 operator at the ramified prime is instead the unique relative Frobenius. Raise the four basis-point coordinates to their 673rd powers, then read them in the exact target basis at $j^{673}$. There are 56 such directed rows, whose squares act by common sign in the frame data. No characteristic-673 étale line count is used.

## How this operates on the actual rigid state space

On a source $j$, represent a rigid frame by the coordinate rows for $(Q_{32},V_2,Z_3)$; the first is primitive in $(\mathbf Z/32)^2$, the second is independent of $[16]Q_{32}$, the third is nonzero in $\mathbf F_3^2$. Push each row by its displayed transition matrix (at $V_2$ use the induced mod-two matrix). Identify simultaneous negation of $Q_{32},Z_3$ exactly once. There are $(32^2-16^2)\cdot2\cdot8/2=6144$ frames per $j$. There is no averaging over source frames and no division within a matrix entry. Distinct lines of degree 17 are retained with multiplicity, even if they give the same pushed target frame.

This supplies a complete fixed table for the early $T_{17}$ step in the exact original first-arm Hecke product, and the actual $T_{673}$ permutation when that helper is used. It is a fixed finite receipt independent of the moving $n$ and safe to replay with only Python's standard library. The arithmetic does not certify the existence of the already nonmaterialized global source with this helper, any other moving-prime operator, the final product parity, or the marked point.
