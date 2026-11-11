module
public import ThreeExceptionalParameter318
public import LiteralThreeCompactParameter318
public import ThirdArithmeticHolomorphic318
public import AnalyticThreeSignPoints318
public section
noncomputable section
open Filter Topology
open scoped Manifold ContDiff MatrixGroups
namespace ActualThreeExceptionalParameter318
open ThreeExceptionalParameter318 CanonicalXModularity318
open GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318 ModularCurveChange318
set_option maxHeartbeats 0

lemma pointX_root (tau : UpperHalfPlane)
    (P : (ModularWeierstrass318.curve tau).toAffine.Point) (hP : addOrderOf P=3) :
    (ThreeTorsionIdentity318.divisionPolynomial (ModularWeierstrass318.curve tau).a₄
      (ModularWeierstrass318.curve tau).a₆).eval (pointX P)=0 := by
  cases P with
  | zero =>
    change addOrderOf (0 : (ModularWeierstrass318.curve tau).toAffine.Point)=3 at hP
    simp at hP
  | some x y hn =>
    exact (AnalyticThreeSignPoints318.root_iff tau x).mpr ⟨y,hn,hP⟩

/-- The relation is proved for the original marked period 1/3 at every
upper-half-plane point, including both exceptional elliptic j values. -/
theorem standard_relation (tau : UpperHalfPlane) :
    relation (ModularForm.E₄ tau) (ModularForm.E₆ tau) (standardX tau)=0 := by
  have h := pointX_root tau (MarkedPeriod318.standardPoint 3 tau)
    (MarkedPeriod318.standardPoint_order 3 tau)
  change (ThreeTorsionIdentity318.divisionPolynomial (-ModularForm.E₄ tau/48)
    (-ModularForm.E₆ tau/864)).eval (standardX tau)=0 at h
  simp only [ThreeTorsionIdentity318.divisionPolynomial,Polynomial.eval_sub,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_X,Polynomial.eval_C] at h
  unfold relation
  linear_combination 2304*h

lemma discriminant_relation (tau : UpperHalfPlane) :
    (ModularForm.E₄ tau)^3-(ModularForm.E₆ tau)^2=1728*ModularForm.discriminant tau := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq tau
  linear_combination -1728*h

lemma discriminant_ne_zero (tau : UpperHalfPlane) :
    (ModularForm.E₄ tau)^3-(ModularForm.E₆ tau)^2 ≠ 0 := by
  rw [discriminant_relation]
  exact mul_ne_zero (by norm_num) (ModularForm.discriminant_ne_zero tau)

/-- The actual extended coordinate, using the same E4/E6 series and genuine
1/3 torsion point. No choice of an analytic branch or lift is introduced. -/
@[expose] def periodParameter (tau : UpperHalfPlane) : ℂ :=
  glued (ModularForm.E₄ tau) (ModularForm.E₆ tau) (standardX tau)

lemma E4_analyticAt (tau : UpperHalfPlane) :
    AnalyticAt ℂ (fun z => ModularForm.E₄ (UpperHalfPlane.ofComplex z)) (tau:ℂ) := by
  exact (UpperHalfPlane.mdifferentiable_iff.mp
    (ModularForm.E (k:=4) (by norm_num)).holo').analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet tau tau.im_pos

lemma E6_analyticAt (tau : UpperHalfPlane) :
    AnalyticAt ℂ (fun z => ModularForm.E₆ (UpperHalfPlane.ofComplex z)) (tau:ℂ) := by
  exact (UpperHalfPlane.mdifferentiable_iff.mp
    (ModularForm.E (k:=6) (by norm_num)).holo').analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet tau tau.im_pos

/-- Actual holomorphic extension over the full upper half plane, including
the former j=0 and j=1728 exclusions. This is not yet a quotient atlas theorem. -/
theorem periodParameter_analyticAt (tau : UpperHalfPlane) :
    AnalyticAt ℂ (fun z => periodParameter (UpperHalfPlane.ofComplex z)) (tau:ℂ) := by
  apply glued_analyticAt (E4_analyticAt tau) (E6_analyticAt tau)
    (ThirdArithmeticHolomorphic318.standardX_analyticAt tau)
  · simpa only [UpperHalfPlane.ofComplex_apply] using discriminant_ne_zero tau
  · exact Filter.Eventually.of_forall (fun z => standard_relation (UpperHalfPlane.ofComplex z))

lemma scale_formula (tau : UpperHalfPlane) (h : OpenJComplexEvaluation318.Admissible tau) :
    CanonicalXScale318.scale (tau:ℂ)=ModularForm.E₆ tau/(12*ModularForm.E₄ tau) := by
  have hj0 : OpenJLocalComparison318.j (tau:ℂ) ≠ 0 := by
    simpa [OpenJLocalComparison318.j] using h.1
  have hj1728 : OpenJLocalComparison318.j (tau:ℂ)-1728 ≠ 0 := by
    simpa [OpenJLocalComparison318.j] using sub_ne_zero.mpr h.2
  have h4 := ActualJImmersion318.E4_ne_zero tau h
  unfold CanonicalXScale318.scale LocalShortScaling318.ratio
    OpenJLocalComparison318.A OpenJLocalComparison318.B
    OpenJLocalComparison318.C OpenJLocalComparison318.D
  simp only [UpperHalfPlane.ofComplex_apply,ModularWeierstrass318.curve,
    NormalizedWeierstrass318.model]
  field_simp
  ring

lemma arithmeticX_formula (tau : UpperHalfPlane) (h : OpenJComplexEvaluation318.Admissible tau) :
    arithmeticX tau=12*ModularForm.E₄ tau*standardX tau/ModularForm.E₆ tau := by
  rw [arithmeticX,scale_formula tau h]
  field_simp

/-- On the entire old admissible locus the new extension is exactly the old
literal parameter, not just another function with the same j-invariant. -/
theorem periodParameter_eq_old (tau : UpperHalfPlane)
    (h : OpenJComplexEvaluation318.Admissible tau) :
    periodParameter tau=ThreeCompactParameter318.parameter
      (ActualQJ318.jInvariant tau) (arithmeticX tau) := by
  have h4 := ActualJImmersion318.E4_ne_zero tau h
  have h6 := ActualJImmersion318.E6_ne_zero tau h
  have hp : primaryDenominator (ModularForm.E₄ tau) (standardX tau) ≠ 0 := by
    intro he
    exact h4 ((primary_zero_iff (discriminant_ne_zero tau) (standard_relation tau)).mp he).1
  rw [periodParameter,glued_primary hp,arithmeticX_formula tau h]
  exact (old_parameter_eq_primary h4 h6 (ModularForm.discriminant_ne_zero tau)
    (discriminant_relation tau)).symm

/-- Compatibility with the original descended source comparison. -/
theorem periodParameter_projection (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : OpenJComplexEvaluation318.Admissible tau) :
    periodParameter tau=
      (LiteralThreeCompactParameter318.sourceParameter N
        (ThreeArithmeticQuotient318.projection tau h)).val := by
  rw [LiteralThreeCompactParameter318.sourceParameter_apply,
    ModularArithmeticCoordinates318.sourceX_projection,periodParameter_eq_old tau h]
  rfl

/-- At the former 0/0 case the actual holomorphic coordinate has the
specific simple-zero branch value, rather than an arbitrary filled value. -/
lemma exceptional_value_actual (tau : UpperHalfPlane)
    (h4 : ModularForm.E₄ tau=0) (hu : standardX tau=0) : periodParameter tau = -27 := by
  have h6 : ModularForm.E₆ tau ≠ 0 := by
    intro h6
    have hd := discriminant_ne_zero tau
    simp [h4,h6] at hd
  rw [periodParameter,h4,hu]
  exact exceptional_value h6

theorem periodParameter_ne_zero (tau : UpperHalfPlane) : periodParameter tau ≠ 0 :=
  glued_ne_zero (discriminant_ne_zero tau) (standard_relation tau)

/-- Exact j compatibility throughout the full upper half plane. -/
theorem periodParameter_j (tau : UpperHalfPlane) :
    ThreeCompactParameter318.J (periodParameter tau)=ActualQJ318.jInvariant tau := by
  rw [periodParameter,J_glued (discriminant_ne_zero tau) (standard_relation tau),
    discriminant_relation]
  unfold ActualQJ318.jInvariant
  field_simp

theorem periodParameter_invariant (g : SL(2,ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma1 3)
    (tau : UpperHalfPlane) : periodParameter (g•tau)=periodParameter tau := by
  have h4 := E4_transform ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) ⟨g,rfl⟩ tau
  have h6 := E6_transform ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) ⟨g,rfl⟩ tau
  change ModularForm.E₄ (g•tau)=_ at h4
  change ModularForm.E₆ (g•tau)=_ at h6
  have hu := standardX_transform g hg tau
  unfold periodParameter
  rw [h4,h6,hu]
  exact glued_weight_invariant _ _ _ _ (UpperHalfPlane.denom_ne_zero _ tau)

lemma image_invariant (g : image 3) (tau : UpperHalfPlane) :
    periodParameter (g•tau)=periodParameter tau := by
  obtain ⟨gamma,hgamma⟩ := g.property
  have he : (g:DerivativeCocycle318.G)=positiveMatrix 3 gamma := hgamma.symm
  change periodParameter ((g:DerivativeCocycle318.G)•tau)=_
  rw [he]
  exact periodParameter_invariant gamma.val gamma.property tau

theorem periodParameter_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω periodParameter := by
  intro tau
  apply UpperHalfPlane.contMDiffAt_iff.mpr
  exact (periodParameter_analyticAt tau).contDiffAt

/-- A genuine continuous coordinate on the entire original Gamma1(3) orbit
quotient, retaining elliptic stabilizers rather than deleting their points. -/
@[expose] def quotientParameter : Base (image 3) → ℂ :=
  Quotient.lift periodParameter (by
    intro a b hab
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp hab
    rw [←hg]
    exact image_invariant g b)

@[simp] lemma quotientParameter_projection (tau : UpperHalfPlane) :
    quotientParameter (quotientMap 3 tau)=periodParameter tau := rfl

theorem quotientParameter_continuous : Continuous quotientParameter := by
  apply (MulAction.isOpenQuotientMap_quotientMk (Γ := image 3)
    (T := UpperHalfPlane)).isQuotientMap.continuous_iff.mpr
  exact periodParameter_holomorphic.continuous

theorem quotientParameter_ne_zero (q : Base (image 3)) : quotientParameter q ≠ 0 := by
  induction q using Quotient.inductionOn with
  | h tau => exact periodParameter_ne_zero tau

theorem quotientParameter_j (q : Base (image 3)) :
    ThreeCompactParameter318.J (quotientParameter q)=QuotientJ318.jMap 3 q := by
  induction q using Quotient.inductionOn with
  | h tau => exact periodParameter_j tau

/-- Equality on the old quotient is pointwise equality with its original
arithmetic comparison, not just compatibility after forgetting down to j. -/
theorem quotientParameter_restrict (N : ℕ) [NeZero N]
    (q : ThreeArithmeticQuotient318.Source) :
    quotientParameter q.val=(LiteralThreeCompactParameter318.sourceParameter N q).val := by
  obtain ⟨tau,htau⟩ := quotient_surjective 3 q.val
  have ht : OpenJComplexEvaluation318.Admissible tau := by
    have hj := congrArg (QuotientJ318.jMap 3) htau
    rw [QuotientJ318.jMap_projection] at hj
    simpa only [OpenJComplexEvaluation318.Admissible,hj] using q.property
  have he : ThreeArithmeticQuotient318.projection tau ht=q := Subtype.ext htau
  rw [←he]
  exact periodParameter_projection N tau ht

end ActualThreeExceptionalParameter318
