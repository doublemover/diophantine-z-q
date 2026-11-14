module
public import RegularPrincipalIdealFrame318
public import SectionZeroRegularCoordinate318
public import OriginalAffineSectionZero318
public section
noncomputable section
namespace RegularSectionDualIdeal318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable (A : CommRingCat.{u}) (L : Line (Spec A))
local notation "P" => OriginalLineAffineModel318.sections A L
variable (e : P ≃ₗ[A] A) (s : P)

/-- The dual frame is evaluation at the ACTUAL vector of coefficient1. -/
@[expose] def dualCoordinate : Module.Dual A P →ₗ[A] A where
  toFun φ := φ (e.symm 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma functional_formula (φ : Module.Dual A P) (x : P) :
    φ x=dualCoordinate A L e φ * e x := by
  have hx : x=(e x) • e.symm 1 := by
    apply e.injective
    rw [map_smul,LinearEquiv.apply_symm_apply,smul_eq_mul,mul_one]
  calc
    φ x = φ ((e x) • e.symm 1) := congrArg φ hx
    _ = e x * φ (e.symm 1) := by rw [map_smul,smul_eq_mul]
    _ = dualCoordinate A L e φ * e x := mul_comm _ _

lemma dualCoordinate_bijective : Function.Bijective (dualCoordinate A L e) := by
  constructor
  · intro φ ψ h
    ext x
    rw [functional_formula A L e φ x,functional_formula A L e ψ x,h]
  · intro a
    refine ⟨a • e.toLinearMap,?_⟩
    change a * e (e.symm 1)=a
    rw [LinearEquiv.apply_symm_apply,mul_one]

@[expose] def dualFrame : Module.Dual A P ≃ₗ[A] A :=
  LinearEquiv.ofBijective (dualCoordinate A L e) (dualCoordinate_bijective A L e)

variable (hr : SectionZeroRegularCoordinate318.Regular A P s)

lemma regular_coefficient (a : A) (ha : a * e s=0) : a=0 :=
  (SectionZeroRegularCoordinate318.regular_iff A P s e).mp hr a ha

/-- Canonical evaluation into the ACTUAL zero ideal, whose inclusion is
fixed before any frame is used to prove injectivity. -/
@[expose] def evaluation : Module.Dual A P →ₗ[A] OriginalAffineSectionZero318.ideal A L s :=
  (ProjectiveSectionIdeal318.evaluation A P s).rangeRestrict

lemma evaluation_bijective : Function.Bijective (evaluation A L s) := by
  constructor
  · intro φ ψ he
    have hv : φ s=ψ s := congrArg Subtype.val he
    apply (dualFrame A L e).injective
    apply sub_eq_zero.mp
    apply regular_coefficient A L e s hr
    rw [sub_mul,← functional_formula A L e φ s,← functional_formula A L e ψ s,hv,sub_self]
  · intro x
    obtain ⟨φ,hφ⟩ := x.property
    exact ⟨φ,Subtype.ext hφ⟩

/-- The dual of the SAME actual affine line is the literal section-zero
ideal via its canonical evaluation, not merely via equal module ranks. -/
@[expose] def equivalence : Module.Dual A P ≃ₗ[A] OriginalAffineSectionZero318.ideal A L s :=
  LinearEquiv.ofBijective (evaluation A L s) (evaluation_bijective A L e s hr)

lemma equivalence_value (φ : Module.Dual A P) :
    (equivalence A L e s hr φ).val=φ s := rfl

/-- Frame-independence at the actual map into the original ring: the
ideal-line isomorphism is always the SAME evaluation map. -/
lemma equivalence_frame_independent (e' : P ≃ₗ[A] A) :
    (equivalence A L e s hr).toLinearMap=(equivalence A L e' s hr).toLinearMap := rfl
end RegularSectionDualIdeal318
