module
public import NebentypusOrder318
public import EulerIndex318
public section
noncomputable section
namespace ModularIndex318
set_option maxHeartbeats 0
variable {G Q U K : Type*} [Group G] [Group Q] [Fintype Q] [Group U] [Field K]

/-- Exact determinant, finite field restriction and Dirichlet pullback feed
the actual prime-factor index product. No free character-order bound remains. -/
theorem index_from_determinant
    (q:G→*Q) (pi:G→*U) (hpi:Function.Surjective pi)
    (epsilon:U→*Kˣ) (cyclotomic determinant:G→*Kˣ)
    (hdet:∀g,determinant g=epsilon (pi g)*cyclotomic g)
    (hsq:∀g,q g=1→determinant g^2=cyclotomic g^2)
    (N R:ℕ) (C d:ℝ) (hR:0<R) (hC:0<C)
    (hdegree:Fintype.card Q≤2304*R)
    (hsupport:∀p∈N.primeFactors,p∣R)
    (hlevel:(N:ℝ)≤C*(R:ℝ)^2)
    (hindex:d=(N:ℝ)*epsilon.ker.index*EulerIndex318.eulerProduct N) :
    d<2^14*C*(R:ℝ)^((97:ℝ)/32) :=
  EulerIndex318.index_bound N R epsilon.ker.index C d hR hC hsupport hlevel
    (NebentypusOrder318.determinant_finite_index_bound q pi hpi epsilon
      cyclotomic determinant hdet hsq R hdegree) hindex

/-- The same actual data now removes both independent hindex and character
order premises from the logarithmic49/8 Jacobian transfer. -/
theorem jacobian_growth_from_determinant
    (q:G→*Q) (pi:G→*U) (hpi:Function.Surjective pi)
    (epsilon:U→*Kˣ) (cyclotomic determinant:G→*Kˣ)
    (hdet:∀g,determinant g=epsilon (pi g)*cyclotomic g)
    (hsq:∀g,q g=1→determinant g^2=cyclotomic g^2)
    (N R d:ℕ) (h:ℝ) (hR:0<R) (hN0:0<N) (hd0:0<d)
    (hdegree:Fintype.card Q≤2304*R)
    (hsupport:∀p∈N.primeFactors,p∣R)
    (hlevel:(N:ℝ)≤ActualLogWeight318.C*(R:ℝ)^2)
    (hindex:(d:ℝ)=(N:ℝ)*epsilon.ker.index*EulerIndex318.eulerProduct N)
    (hJacobian:h≤2^11*(d:ℝ)^2*(Real.log (6*(d:ℝ)*N))^2) :
    h<2^65*ActualLogWeight318.C^2*(R:ℝ)^((49:ℝ)/8) :=
  EulerIndex318.jacobian_growth_of_index N R epsilon.ker.index d h hR hN0 hd0
    hsupport hlevel
    (NebentypusOrder318.determinant_finite_index_bound q pi hpi epsilon
      cyclotomic determinant hdet hsq R hdegree) hindex hJacobian

end ModularIndex318
#print axioms ModularIndex318.index_from_determinant
#print axioms ModularIndex318.jacobian_growth_from_determinant
