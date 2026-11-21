# The same arithmetic inverse gives the original analytic branch norm

This composes the ordinary cotangent specialization, actual Yuan
comparison on the common fine family, and actual principal-polarization
period computations. It removes the independently supplied complex KS
scalar row in SelectedYuanKSComplexScalar318.normalize on the exact
coefficient used at finite places. The selected quaternionic abelian
surface A is unchanged and distinct from the modular Jacobian.

## One arithmetic scalar on the literal ordinary tangent

Take the same selected noncontact point t=q=32u/v and common number
field L. At every finite place use the genuine proper trait on U(3),
or U(11) at 3. These levels have the same polarized surface and the
same generic mark on U(33). The ordinary relative cotangent supplies
dt as a basis at that generic mark. It localizes the original t chart;
it is not the cotangent of a constant surface over Spec L. The stalk
fraction gives the same specialized tensor from each allowed integral
model even if the arithmetic denominator of t is not a unit at the
closed point.

Choose one nonzero generator H0 of det omega_A over L, and an ordered
basis (h1,h2) of omega_A with h1∧h2=H0 (rescale the second vector of
any basis by a nonzero scalar). Use its actual dual basis for Lie A.
Let B0 be the matrix of the dimension-two polarized Kodaira–Spencer
map of the family, with that source basis, that dual target and base
cotangent dt. Write B=det B0. The image theorem on the intact fine
model, or the ordinary generic comparison, gives B≠0. By definition
of the determinant of this actual map,

    Ψ(H0²) = B (dt)².                                      (1)

There is no 210 division in (1): Ψ is the undivided Yuan map. The
factor 210 in the finite integrality statement is the scalar in the
image of Ψ on the arithmetic stalk before pulling back the proper
trait. Over L it is invertible but is not discarded from the
integral estimate.

For one archived branch index i let b_i be its original contact
0, 32, 76832 or −343, and c_i its original twist. The literal rational
square gauge ρ_i=c_i/[4(q−b_i)] lies in L. The branch equation
y_i²=c_i(t−b_i) gives η_i=dy_i/dt=c_i/(2y_i) at the complex mark,
with η_i²=ρ_i. The nonzero t−b_i and y_i are guaranteed by the
original noncontact tests. Transport of the gauge needs no root sign.
Let

    κ_i = ρ_i/B in L.                                      (2)

This is the inverse under (1) of the actual branch square, not a
complex scalar chosen afterward: linearity gives Ψ⁻¹(ρ_i(dt)²)=κ_i H0².
The same-section calculation identifies the two archived sections
a_{ij}ρ_i(dt)² with the actual integral tensors' specializations,
with j=0,1. Thus the finite assertion is on the inverse
210 a_{ij}κ_i in the same Hodge square. This identifies the finite
coefficient by an exact equality, not an equality between two
independent rational generators. The existing bound with the local
metric of H0 applies unchanged.

## The complex frame changes on both sides

Let σ:L→C be the actual chosen embedding and work on the true complex
family on U(33) over a small disc. Use local coordinate z=t−q
and the actual upper uniformizer τ=f(z), so dt=dz and
dτ=f'(0)dt at the point; f'(0)≠0 since both are local coordinates.
This is the f in the old positive Poincaré pullback, not a separately
rescaled disc. At a complex place using the conjugate representative
choose the compatible analytic lift, rather than identify a complex
embedding with its conjugate as a field map.

Let X be the matrix whose columns are σ(h1),σ(h2) in the analytic
basis dz_1,dz_2 of the surface (fiber coordinates, not the base z).
Then c=det X is the analytic scalar of the same H0. If the analytic
Lie coordinates of a vector are v, its coordinates in the actual
dual of (σ(h1),σ(h2)) are X^t v: the two basis forms evaluate X^t
on v. No conjugation occurs because this is the complex bilinear
invariant-form/Lie pairing, not a Hermitian metric. There is neither
a second gauge nor X^{-t} on the output coordinates of this matrix.

Let M be the actual analytic polarized KS matrix in dz_j,
∂/∂z_j and dτ. The period cohomology packet identifies it by the
full comparison to the cotangent connecting map, giving

    det M = 210/(2πi)².

The coherent proper-fiber cohomology comparison and étale naturality
apply to this same family and original relative cotangent. Changing
domain, codomain and base coordinate in that order gives

    σ(B0) = f'(0) X^t M X,
    σ(B)  = c² [210/(2πi)²] (f'(0))².                       (3)

This is a congruence, not a similarity transformation: omitting
the dual target frame loses one c. If the polarized Čech conventions
reverse common sign there are two columns, and (3) is unchanged.
Taking the determinant already accounts for the square of f';
no further tensor factor is applied.

Apply σ to κ_i B=ρ_i, and substitute (3) and η_i²=ρ_i. The old
independently supplied KS scalar row is now a conclusion:

    σ(κ_i)c² [210/(2πi)²] (f'(0))² = η_i².                 (4)

The principal period calculation gives the Hodge norm
||H0||²=|c|² 210 (Im f(0))²/π² on exactly this ordered Hodge determinant
and real quaternion lattice; the same real μ produces the complex μ
in (3), its determinant forced to be 210. Taking norms of (4) gives

    |σ(κ_i)| ||H0||² =
        4 |η_i²| (Im f(0))² / |f'(0)|².

This is the literal original Petersson quadratic norm of the branch
square. Multiplying by the two archived section coefficients gives
the existing archimedean section bound on precisely the same
Hodge-square elements as the finite bound. It introduces no new
factor into the +120 cutoff (nor changes the established +64 paper).
In particular 210 is not both a second finite correction and a
fresh archimedean correction.

## Exact realizations and limitations

The source derives the determinant, the inverse equality in the
finite linear equivalence, the old branch row and its norm.
It consumes the dimension-two cohomology comparison and the actual
base-field matrix chart after base change; (3)'s first line follows
classically from the same-family diagram and the exact coordinate
changes above. It does not assume (3)'s second line or (4) in native
form, but does not construct a native coherent GAGA/Picard comparison,
fine PEL scheme or arithmetic cohomology chart either.
The Hodge norm is derived from the same μ, not another number input.
No new hypothesis on rank, metric of the separate modular Jacobian,
or Lean-kernel verification is claimed.

For the conventions see [Yuan v2 §§1, 4.1–4.3](https://arxiv.org/html/2205.11334v2);
the previous stalk, family, period and Čech proofs in the immutable
donor list establish the comparison on the selected family.

    sha256sum -c SHA256SUMS
    python3 check_shared_dt.py | cmp - EXACT-SHARED-DT.json

Run the workspace-relative donor manifest from the workspace root.
