module
public import OriginalEvenFiniteCanonicalCenter318
public section
noncomputable section
namespace OriginalEvenFiniteCanonicalExtension318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalEvenFiniteCanonicalCenter318 FinitePivotCanonicalSource318
variable (c : Fin 4 → ℚˣ) (tau : ℚ) (w : FinitePlace (K c tau)) (D : Data c tau w)
  (he : ∀ k,D.exponent k=0) (i : Fin 4)
local notation "V" => OriginalPointFinitePlaceRoots318.V c tau w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "d" => D.coefficients
local notation "C" => FinitePivotCanonicalSource318.Chart V 1 (D.unit i) d a i
@[expose] def globalImage (s : Γ(OriginalWholeIntrinsicSections318.tensorSquare c tau w D,⊤)) :=
  FinitePivotGlobalCanonicalSections318.globalImage V 1 (D.unit i) d a i
    (coefficient_even c tau w D he i) s
variable (h2 : IsUnit (2:V))
include h2 in
lemma global0_integral : globalImage c tau w D he i (OriginalWholeIntrinsicSections318.global0 c tau w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (FinitePivotGenericCanonical318.baseMap V 1 (D.unit i) d a i)
      (FinitePivotIntegralCanonicalTensors318.integral0 V 1 (D.unit i) d a i) :=
  FinitePivotGlobalCanonicalSections318.global0_integral V 1 (D.unit i) d a i
    (coefficient_even c tau w D he i) h2
include h2 in
lemma global1_integral : globalImage c tau w D he i (OriginalWholeIntrinsicSections318.global1 c tau w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (FinitePivotGenericCanonical318.baseMap V 1 (D.unit i) d a i)
      (FinitePivotIntegralCanonicalTensors318.integral1 V 1 (D.unit i) d a i) :=
  FinitePivotGlobalCanonicalSections318.global1_integral V 1 (D.unit i) d a i
    (coefficient_even c tau w D he i) h2
structure Extension where
  center : Center c tau w D i
  smooth : Algebra.Smooth V C
  point_recovery : Spec.map (CommRingCat.ofHom (algebraMap V (K c tau))) ≫
    (Spec.map (CommRingCat.ofHom (modelPoint c tau w D he i center)) ≫
      NormalizedWholeOpenMaps318.finiteChart V d a)=D.genericPoint
  section0 : globalImage c tau w D he i (OriginalWholeIntrinsicSections318.global0 c tau w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (FinitePivotGenericCanonical318.baseMap V 1 (D.unit i) d a i)
      (FinitePivotIntegralCanonicalTensors318.integral0 V 1 (D.unit i) d a i)
  section1 : globalImage c tau w D he i (OriginalWholeIntrinsicSections318.global1 c tau w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (FinitePivotGenericCanonical318.baseMap V 1 (D.unit i) d a i)
      (FinitePivotIntegralCanonicalTensors318.integral1 V 1 (D.unit i) d a i)
include h2 in
theorem of_center (P : Center c tau w D i) : Nonempty (Extension c tau w D he i) :=
  ⟨⟨P,OddTwistDilatationEtale318.smooth V 1 (D.unit i) (a i) (others V d i) (others V a i) h2,
    generic_extension c tau w D he i P,global0_integral c tau w D he i h2,
    global1_integral c tau w D he i h2⟩⟩
include h2 in
/-- The pivot is produced from the original all-even finite point. -/
theorem exists_extension (ht : w (tau:K c tau)≤1)
    (hsep : ∀ i j : Fin 4,i≠j→IsUnit (a i-a j)) :
    ∃ i,Nonempty (Extension c tau w D he i) := by
  obtain ⟨i,⟨P⟩⟩ := exists_center c tau w D he ht hsep
  exact ⟨i,of_center c tau w D he i h2 P⟩
end OriginalEvenFiniteCanonicalExtension318
