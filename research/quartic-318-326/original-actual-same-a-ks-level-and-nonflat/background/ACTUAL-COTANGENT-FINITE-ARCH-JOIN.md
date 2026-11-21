# The identical two sections in the finite and complex computations

The previous actual fine family/unnormalized KS packet supplied the two
finite bounds on the integral tensors in an actual proper closed stalk.
The compiled-in parts of the original archimedean work name two point
coefficients in a branch frame. Their equality with the finite tensors
cannot be inferred just from the ratio of the two sections. This
packet derives the scalar and actual tensor identities.

## Common ordinary point and actual cotangent

Let t=q=32u/v be the actual finite noncontact point and P its fixed marked
point field. Let L be the auxiliary common height field, retaining the
fixed embedding P -> L. Let X_n be the actual fine model, with its
previous proper trait y and true MarkLocal B in the very same function
field, and R its closed stalk. From the earlier producer we have
t=a/d in B, ev(d) nonzero, ev(a)=q ev(d), and the true integral tensor
coefficients r0,r1. Write e for the primitive dualizing basis at R,
delta for coordinates of the fundamental differential in e, and
sigma for its actual field specialization into the ordinary cotangent
V at the selected point. The square specialization is sigma tensor
sigma, not a separately supplied map of the squared lines.

The actual ordinary differential D at the point, on B and into V,
satisfies the field-valued Leibniz rule. Its arithmetic comparison is
only on integral elements: D(image x)=ev(delta x) sigma(e). The source
SelectedActualCotangentEvaluationBridge318 then derives

    D(t) = [(ev d)(ev delta a)-(ev a)(ev delta d)]/(ev d)^2 * sigma(e).

This is not an extra quotient or generic derivative equivalence.
The equality t*d=a in B is derived by injection into the **same** K.
Apply Leibniz inside B and cancel only ev(d) in L. No field map K -> L,
division by a nonunit in the arithmetic stalk or smoothly ramified
trait is used.

On all fine levels the geometric D is the ordinary relative
differential of the same coarse noncontact t pulled back in
characteristic zero: the stack forgetful maps on the full levels are
étale, and t is finite étale off the five exact contacts after passing
to the maximal stack (generic sign acts trivially on the base).
The common point's cotangent is identified by this same natural
cotangent base-change map, not by equal numerical values of t. In
particular Dt is nonzero on the genuine model. Native proof of
étaleness/relative cotangent comparison, including the identification
of the two levels' V with the same generic point fiber, is still an
explicit geometric input. Source actual_dt calculates the resulting
quotient without assuming any of the two section values.

## Exact branch gauge and finite norm on the original arch pair

Put P0(X)=X(X-32)(X-76832)(X+343), J=2765952000. The old cleared
numerator evaluates exactly, not just projectively:

    ev(r0)=J^2/P0(q) * h^2;   ev(r1)=q*ev(r0),

where h is the displayed quotient in L. This follows by evaluating
P_a as P0(q)*ev(d)^4 and using the original exact fraction identity.
Thus the actual point tensor at either finite level is

    [J^2/P0(q), q J^2/P0(q)] * (Dt tensor Dt).

For the ith archived branch, with y_i^2=c_i(t-b_i) and the original
b_i=0,32,76832,-343, the gauge is the **rational**
rho_i=c_i/[4(q-b_i)]. Hence (dy_i)^2=rho_i (Dt)^2 on the very same
generic point fiber. Its nonzero rational coefficient means no
archimedean sign choice or compatibility of representative complex
embeddings is needed. By the archived exact complex coefficient
calculation, the two named branch coefficients times rho_i are
precisely J^2/P0(q), qJ^2/P0(q) in P. One embedding descends this
scalar identity to P by injectivity, then the fixed embedding P->L
transfers it to the actual field. No separate identification of
complex points with Galois-conjugate marks is inferred.

SelectedSameIntrinsicSectionFiniteArch318 proves the equality to
the actual finite tensors and applies the divided-Yuan finite
bound to exactly this archived pair in the common cotangent.
In particular it needs neither an independently chosen finite
square frame nor a supplied equality of the original point section
vectors. The linear map sigma is used twice in TensorProduct.map;
the original KS must still be the same one polarized cohomological
map, pulled to the actual generic fiber and compared with those
square specializations. The previous effective offsets and
archimedean norm normalization are unchanged; 210 is not absorbed
twice.

## Native boundary and the independent J lane

The smallest remaining geometric datum for this join is the
commuting fundamental cotangent map on the actual universal-family
trait, on **integral** arithmetic elements and identified with the
same marked ordinary cotangent over L. This is justified on paper by
relative differential/base extension on the characteristic-zero
smooth locus and the identification of the dualizing fundamental
map there. Full PEL representability and the Yuan cohomological base
change are not implemented natively. No root row, arch height or
nonzero dt on an arbitrary chart is assumed in the new coefficient
proofs.

Height's actual modular Jacobian period/finite Abel terminal needs
the same common L but no shared determinant frame: J=X_1(M)'s
Jacobian and A are distinct objects. Its period degree in the
Gaudron–Rémond convention (with exact additive shift g log(pi)/2
in the Abel/Petersson comparison) supplies h_J and g<=M^2;
the same-A quotient inequality takes that h_J. The present
two-column normalization then supplies the separate same-A
direction with +120. Neither statement about the analytic period
matrix or connected quotient follows from this cotangent packet.

## Static replay

    sha256sum -c SHA256SUMS
    python3 check_same_section.py | cmp - EXACT-SAME-SECTION.json

The arithmetic replay checks every branch for each signed rational
fraction control, including zero-derivative cases that would be
forbidden at the real geometric generic point. It is not a Lean
build or evidence that a surrogate isogeny compares A and J.
