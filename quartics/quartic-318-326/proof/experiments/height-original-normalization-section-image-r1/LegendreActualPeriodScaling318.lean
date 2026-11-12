module
public import LegendreModularPeriodLattice318
public import NormalizedLegendreProjectiveModel318
public import ShortScaling318
public section
noncomputable section
namespace LegendreActualPeriodScaling318
open LegendreModularPeriodLattice318
variable (l:ℂ) [Fact (l≠0 ∧ l≠1)]
local instance target_elliptic : (NormalizedLegendreProjectiveModel318.curve l).IsElliptic :=
  NormalizedLegendreProjectiveModel318.curve_elliptic l (Fact.out: l≠0 ∧ l≠1).1 (Fact.out: l≠0 ∧ l≠1).2
local instance target_short : (NormalizedLegendreProjectiveModel318.curve l).IsShortNF :=
  ⟨rfl,rfl,rfl⟩
local instance modular_short (tau:UpperHalfPlane) : (ModularWeierstrass318.curve tau).IsShortNF :=
  ⟨rfl,rfl,rfl⟩

/-- A period parameter PRODUCED from surjectivity of the genuine modular
j on the upper half-plane, not from the degree-four rational j-map. -/
@[expose] def parameter : UpperHalfPlane:=
  (ActualJSurjective318.surjective (NormalizedLegendreProjectiveModel318.curve l).j).choose
lemma parameter_j : ActualQJ318.jInvariant (parameter l)=
    (NormalizedLegendreProjectiveModel318.curve l).j :=
  (ActualJSurjective318.surjective (NormalizedLegendreProjectiveModel318.curve l).j).choose_spec

/-- Equality of actual algebraic j is consumed ONLY by the proved short
model classification, yielding concrete fourth/sixth-power coefficients.
The full lattice and the 2*pi convention are then explicitly inserted. -/
theorem exists_native_scaling : ∃u:ℂˣ,
    NormalizedLegendreProjectiveModel318.A l=(u:ℂ)^4*
      OriginalPeriodProjectiveModel318.A (lattice (parameter l)) ∧
    NormalizedLegendreProjectiveModel318.B l=(u:ℂ)^6*
      OriginalPeriodProjectiveModel318.B (lattice (parameter l)) := by
  have hj:(ModularWeierstrass318.curve (parameter l)).j=
      (NormalizedLegendreProjectiveModel318.curve l).j:=by
    rw [ModularWeierstrass318.curve_j,parameter_j]
  obtain ⟨v,h4,h6⟩:=ShortScaling318.exists_scaling_of_j_eq
    (ModularWeierstrass318.curve (parameter l)) (NormalizedLegendreProjectiveModel318.curve l) hj
  let s:ℂˣ:=Units.mk0 (2*(Real.pi:ℂ)) (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hs:(s:ℂ)≠0:=Units.ne_zero s
  have ht4:(NormalizedLegendreProjectiveModel318.curve l).a₄=
      NormalizedLegendreProjectiveModel318.A l:=by
    dsimp [NormalizedLegendreProjectiveModel318.curve,NormalizedWeierstrass318.model];ring
  have ht6:(NormalizedLegendreProjectiveModel318.curve l).a₆=
      NormalizedLegendreProjectiveModel318.B l:=by
    dsimp [NormalizedLegendreProjectiveModel318.curve,NormalizedWeierstrass318.model];ring
  refine ⟨v/s,?_,?_⟩
  · rw [←ht4,h4,native_a4]
    change (v:ℂ)^4*_ = ((v:ℂ)/(s:ℂ))^4*((s:ℂ)^4*_)
    field_simp [hs]
    <;> ring
  · rw [←ht6,h6,native_a6]
    change (v:ℂ)^6*_ = ((v:ℂ)/(s:ℂ))^6*((s:ℂ)^6*_)
    field_simp [hs]
    <;> ring
@[expose] def scaling : ℂˣ:=(exists_native_scaling l).choose
lemma scaling_spec :
    NormalizedLegendreProjectiveModel318.A l=(scaling l:ℂ)^4*
      OriginalPeriodProjectiveModel318.A (lattice (parameter l)) ∧
    NormalizedLegendreProjectiveModel318.B l=(scaling l:ℂ)^6*
      OriginalPeriodProjectiveModel318.B (lattice (parameter l)) :=
  (exists_native_scaling l).choose_spec
end LegendreActualPeriodScaling318
