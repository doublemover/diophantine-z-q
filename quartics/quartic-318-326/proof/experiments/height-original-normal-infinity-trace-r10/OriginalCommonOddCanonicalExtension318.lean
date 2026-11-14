module
public import OriginalOddCanonicalGenericPoint318
public import OriginalWholeIntrinsicSections318
public section
noncomputable section
namespace OriginalCommonOddCanonicalExtension318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalOddCanonicalCenter318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
local notation "V" => OriginalPointFinitePlaceRoots318.V c t w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "C" => OriginalOddReciprocalCenter318.Ring c t w D
variable (hodd : ∀ i,D.exponent i=1)

@[expose] def globalImage (s : Γ(OriginalWholeIntrinsicSections318.tensorSquare c t w D,⊤)) :=
  OddInfinityGlobalCanonicalSections318.globalImage V D.pi D.unit D.coefficients a rfl
    (coefficients_odd c t w D hodd) s

variable (h2 : IsUnit (2:V))
include h2 in
lemma global0_integral : globalImage c t w D hodd (OriginalWholeIntrinsicSections318.global0 c t w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (OddInfinityGenericCanonical318.baseMap V D.pi D.unit a)
      (OddInfinityIntegralCanonicalTensors318.integral0 V D.pi D.unit a) :=
  OddInfinityGlobalCanonicalSections318.global0_integral V D.pi D.unit D.coefficients a rfl
    (coefficients_odd c t w D hodd) h2
include h2 in
lemma global1_integral : globalImage c t w D hodd (OriginalWholeIntrinsicSections318.global1 c t w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (OddInfinityGenericCanonical318.baseMap V D.pi D.unit a)
      (OddInfinityIntegralCanonicalTensors318.integral1 V D.pi D.unit a) :=
  OddInfinityGlobalCanonicalSections318.global1_integral V D.pi D.unit D.coefficients a rfl
    (coefficients_odd c t w D hodd) h2

/-- The actual original reciprocal point acquires a true smooth integral
chart, whole generic-point recovery, and actual integral canonical tensor
extensions of BOTH same global sections. No regularity or global dualizing
identification for the old proper model is inferred. -/
structure Extension where
  center : OriginalOddReciprocalCenter318.Center c t w D
  smooth : Algebra.Smooth V C
  point_recovery : Spec.map (CommRingCat.ofHom (algebraMap V (K c t))) ≫
    (Spec.map (CommRingCat.ofHom (modelPoint c t w D hodd center)) ≫
      NormalizedWholeOpenMaps318.infinityChart V D.coefficients a)=D.genericPoint
  section0 : globalImage c t w D hodd (OriginalWholeIntrinsicSections318.global0 c t w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (OddInfinityGenericCanonical318.baseMap V D.pi D.unit a)
      (OddInfinityIntegralCanonicalTensors318.integral0 V D.pi D.unit a)
  section1 : globalImage c t w D hodd (OriginalWholeIntrinsicSections318.global1 c t w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (OddInfinityGenericCanonical318.baseMap V D.pi D.unit a)
      (OddInfinityIntegralCanonicalTensors318.integral1 V D.pi D.unit a)

include h2 in
theorem exists_extension (ht : ¬w (t:K c t)≤1) : Nonempty (Extension c t w D hodd) := by
  obtain ⟨P⟩ := OriginalOddReciprocalCenter318.exists_center c t w D ht hodd
  have ht0 : (t:K c t)≠0 := by
    intro h
    apply ht
    simp only [h,map_zero,zero_le]
  exact ⟨⟨P,OriginalOddReciprocalCenter318.smooth c t w D h2,
    generic_extension c t w D hodd P ht0,global0_integral c t w D hodd h2,
    global1_integral c t w D hodd h2⟩⟩

include h2 in
/-- Parity is produced from the original point, rather than supplied by
a favorable branch assumption. The all-even branch stays explicit. -/
theorem even_or_extension (ht : ¬w (t:K c t)≤1) :
    (∀ i,D.exponent i=0) ∨ ∃ ho : ∀ i,D.exponent i=1,Nonempty (Extension c t w D ho) := by
  rcases OriginalReciprocalParity318.even_or_odd c t w D ht with he|ho
  · exact Or.inl he
  · exact Or.inr ⟨ho,exists_extension c t w D ho h2 ht⟩
end OriginalCommonOddCanonicalExtension318
