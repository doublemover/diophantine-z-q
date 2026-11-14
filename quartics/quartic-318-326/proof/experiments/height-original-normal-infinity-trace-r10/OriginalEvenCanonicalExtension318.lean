module
public import OriginalEvenReciprocalCenter318
public import SmoothInfinityModelPoint318
public import OriginalCommonOddCanonicalExtension318
public section
noncomputable section
namespace OriginalEvenCanonicalExtension318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
local notation "V" => OriginalPointFinitePlaceRoots318.V c t w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "C" => OriginalEvenReciprocalCenter318.Ring c t w D
variable (heven : ∀ i,D.exponent i=0)
include heven in
lemma coefficients_even (i : Fin 4) : D.coefficients i=(D.unit i:V)*1 := by
  simp [Data.coefficients,heven i]

@[expose] def globalImage (s : Γ(OriginalWholeIntrinsicSections318.tensorSquare c t w D,⊤)) :=
  OddInfinityGlobalCanonicalSections318.globalImage V 1 D.unit D.coefficients a rfl
    (coefficients_even c t w D heven) s
variable (P : OriginalEvenReciprocalCenter318.Center c t w D)
@[expose] def modelPoint : DVRNormalizedInfinityOrder318.Order V D.coefficients a →+* V :=
  SmoothInfinityModelPoint318.modelPoint V 1 D.unit D.coefficients a rfl
    (coefficients_even c t w D heven) P.coordinate P.ratios P.root_equation
lemma modelPoint_signed (i : Fin 4) : D.multiplier i*(t:K c t)*algebraMap V (K c t)
    (modelPoint c t w D heven P (FourRootOrderSigns318.generator
      (DVRNormalizedInfinityOrder318.coefficient V D.coefficients a) i))=roots c t i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [modelPoint,SmoothInfinityModelPoint318.modelPoint_zero,one_mul]
    exact P.original_zero
  · rw [modelPoint,SmoothInfinityModelPoint318.modelPoint_succ,one_mul]
    exact P.original_others j

theorem generic_extension (ht : (t:K c t)≠0) :
    Spec.map (CommRingCat.ofHom (algebraMap V (K c t))) ≫
      (Spec.map (CommRingCat.ofHom (modelPoint c t w D heven P)) ≫
        NormalizedWholeOpenMaps318.infinityChart V D.coefficients a)=D.genericPoint := by
  apply NormalizedGenericPointExtension318.infinity_extension V (K c t)
    D.coefficients a (t:K c t) D.normalizedRoots D.root_equation ht
    (SmoothInfinityModelPoint318.reciprocal V 1 D.unit P.coordinate) P.reciprocal
    (modelPoint c t w D heven P)
    (SmoothInfinityModelPoint318.modelPoint_polynomial V 1 D.unit D.coefficients a rfl
      (coefficients_even c t w D heven) P.coordinate P.ratios P.root_equation)
  intro i
  change _ = (roots c t i/D.multiplier i)/(t:K c t)
  apply (eq_div_iff ht).2
  apply (eq_div_iff (D.multiplier_ne i)).2
  simpa only [mul_comm,mul_left_comm,mul_assoc] using modelPoint_signed c t w D heven P i

variable (h2 : IsUnit (2:V))
include h2 in
lemma global0_integral : globalImage c t w D heven (OriginalWholeIntrinsicSections318.global0 c t w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (OddInfinityGenericCanonical318.baseMap V 1 D.unit a)
      (OddInfinityIntegralCanonicalTensors318.integral0 V 1 D.unit a) :=
  OddInfinityGlobalCanonicalSections318.global0_integral V 1 D.unit D.coefficients a rfl
    (coefficients_even c t w D heven) h2
include h2 in
lemma global1_integral : globalImage c t w D heven (OriginalWholeIntrinsicSections318.global1 c t w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (OddInfinityGenericCanonical318.baseMap V 1 D.unit a)
      (OddInfinityIntegralCanonicalTensors318.integral1 V 1 D.unit a) :=
  OddInfinityGlobalCanonicalSections318.global1_integral V 1 D.unit D.coefficients a rfl
    (coefficients_even c t w D heven) h2

structure Extension where
  center : OriginalEvenReciprocalCenter318.Center c t w D
  smooth : Algebra.Smooth V C
  point_recovery : Spec.map (CommRingCat.ofHom (algebraMap V (K c t))) ≫
    (Spec.map (CommRingCat.ofHom (modelPoint c t w D heven center)) ≫
      NormalizedWholeOpenMaps318.infinityChart V D.coefficients a)=D.genericPoint
  section0 : globalImage c t w D heven (OriginalWholeIntrinsicSections318.global0 c t w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (OddInfinityGenericCanonical318.baseMap V 1 D.unit a)
      (OddInfinityIntegralCanonicalTensors318.integral0 V 1 D.unit a)
  section1 : globalImage c t w D heven (OriginalWholeIntrinsicSections318.global1 c t w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (OddInfinityGenericCanonical318.baseMap V 1 D.unit a)
      (OddInfinityIntegralCanonicalTensors318.integral1 V 1 D.unit a)

include h2 in
theorem exists_extension (ht : ¬w (t:K c t)≤1) : Nonempty (Extension c t w D heven) := by
  obtain ⟨P⟩ := OriginalEvenReciprocalCenter318.exists_center c t w D ht heven
  have ht0 : (t:K c t)≠0 := by
    intro h
    apply ht
    simp only [h,map_zero,zero_le]
  exact ⟨⟨P,ThreePolynomialEtaleChart318.smooth V (OriginalEvenReciprocalCenter318.coefficients c t w D) h2,
    generic_extension c t w D heven P ht0,global0_integral c t w D heven h2,
    global1_integral c t w D heven h2⟩⟩
end OriginalEvenCanonicalExtension318
