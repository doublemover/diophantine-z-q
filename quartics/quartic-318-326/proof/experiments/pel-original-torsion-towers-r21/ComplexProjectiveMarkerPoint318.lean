module
public import CubicHomogeneousMarker318
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public section
noncomputable section
namespace ComplexProjectiveMarkerPoint318
open Polynomial AlgebraicGeometry
variable {ι:Type*}
abbrev Equations:=MvPolynomial ι ℂ
abbrev grading:ℕ→Submodule ℂ (Equations (ι:=ι)):=MvPolynomial.homogeneousSubmodule ι ℂ
local instance standardGrading:GradedAlgebra (grading (ι:=ι)):=MvPolynomial.gradedAlgebra
@[expose] def marker(v:ι→ℂ):Equations→+*ℂ[X]:=
  CubicHomogeneousMarker318.marker (RingHom.id ℂ) v
lemma kernel_homogeneous(v:ι→ℂ):
    (RingHom.ker (marker v)).IsHomogeneous grading:=by
  intro n p hp
  change marker v (MvPolynomial.decomposition.decompose' p n)=0
  rw [MvPolynomial.decomposition.decompose'_apply]
  change CubicHomogeneousMarker318.marker (RingHom.id ℂ) v
    (MvPolynomial.homogeneousComponent n p)=0
  rw [CubicHomogeneousMarker318.homogeneous_component]
  change marker v p=0 at hp
  rw [hp,Polynomial.coeff_zero,Polynomial.monomial_zero_right]
@[expose] def kernel(v:ι→ℂ):HomogeneousIdeal grading:=
  ⟨RingHom.ker (marker v),kernel_homogeneous v⟩
instance kernel_isPrime(v:ι→ℂ):(kernel v).toIdeal.IsPrime:=
  RingHom.ker_isPrime (marker v)
lemma variable_mem_iff(v:ι→ℂ)(j:ι):
    MvPolynomial.X j∈kernel v↔v j=0:=by
  change marker v (MvPolynomial.X j)=0↔v j=0
  simp only [marker,CubicHomogeneousMarker318.marker,MvPolynomial.eval₂Hom_X']
  constructor
  · intro h
    have hc:=congrArg (fun p:ℂ[X]=>p.coeff 3) h
    simpa only [Polynomial.coeff_monomial,if_pos rfl,Polynomial.coeff_zero] using hc
  · intro h
    rw [h,Polynomial.monomial_zero_right]

/-- Actual relevant homogeneous PRIME, obtained from a domain-valued
polynomial marker. It represents a nonzero homogeneous coordinate vector
in the genuine scheme Proj, not in an invented set of scheme points. -/
@[expose] def point(v:ι→ℂ)(hv:∃j,v j≠0):ProjectiveSpectrum grading where
  asHomogeneousIdeal:=kernel v
  isPrime:=RingHom.ker_isPrime (marker v)
  not_irrelevant_le:=by
    intro h
    obtain ⟨j,hj⟩:=hv
    have hjI:MvPolynomial.X j∈HomogeneousIdeal.irrelevant grading:=
      HomogeneousIdeal.mem_irrelevant_of_mem grading (by norm_num:0<(1:ℕ))
        (MvPolynomial.isHomogeneous_X ℂ j)
    exact hj ((variable_mem_iff v j).mp (h hjI))
lemma homogeneous_mem_iff(v:ι→ℂ)(hv:∃j,v j≠0)(p:Equations)(n:ℕ)
    (hp:p.IsHomogeneous n):p∈(point v hv).asHomogeneousIdeal↔MvPolynomial.eval v p=0:=by
  change marker v p=0↔_
  rw [marker,CubicHomogeneousMarker318.homogeneous_marker _ _ p n hp]
  constructor
  · intro h
    have hc:=congrArg (fun q:ℂ[X]=>q.coeff (3*n)) h
    simpa only [Polynomial.coeff_monomial,if_pos rfl,Polynomial.coeff_zero] using hc
  · intro h
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) v p=0 at h
    rw [h,Polynomial.monomial_zero_right]
end ComplexProjectiveMarkerPoint318
