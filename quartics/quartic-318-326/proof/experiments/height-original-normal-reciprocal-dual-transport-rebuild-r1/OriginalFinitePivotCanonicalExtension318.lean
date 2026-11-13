module
public import OriginalFinitePivotCanonicalCenter318
public import OriginalWholeIntrinsicSections318
public section
noncomputable section
namespace OriginalFinitePivotCanonicalExtension318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalFinitePivotCanonicalCenter318 FinitePivotCanonicalSource318
variable (c : Fin 4 → ℚˣ) (tau : ℚ) (w : FinitePlace (K c tau)) (D : Data c tau w) (i : Fin 4)
  (hi : D.exponent i=1)
local notation "V" => OriginalPointFinitePlaceRoots318.V c tau w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "d" => D.coefficients
local notation "C" => FinitePivotCanonicalSource318.Chart V D.pi (D.unit i) d a i
@[expose] def globalImage (s : Γ(OriginalWholeIntrinsicSections318.tensorSquare c tau w D,⊤)) :=
  FinitePivotGlobalCanonicalSections318.globalImage V D.pi (D.unit i) d a i
    (pivot_coefficient c tau w D i hi) s
variable (h2 : IsUnit (2:V))
include h2 in
lemma global0_integral : globalImage c tau w D i hi (OriginalWholeIntrinsicSections318.global0 c tau w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (FinitePivotGenericCanonical318.baseMap V D.pi (D.unit i) d a i)
      (FinitePivotIntegralCanonicalTensors318.integral0 V D.pi (D.unit i) d a i) :=
  FinitePivotGlobalCanonicalSections318.global0_integral V D.pi (D.unit i) d a i
    (pivot_coefficient c tau w D i hi) h2
include h2 in
lemma global1_integral : globalImage c tau w D i hi (OriginalWholeIntrinsicSections318.global1 c tau w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (FinitePivotGenericCanonical318.baseMap V D.pi (D.unit i) d a i)
      (FinitePivotIntegralCanonicalTensors318.integral1 V D.pi (D.unit i) d a i) :=
  FinitePivotGlobalCanonicalSections318.global1_integral V D.pi (D.unit i) d a i
    (pivot_coefficient c tau w D i hi) h2

structure Extension where
  center : Center c tau w D i
  smooth : Algebra.Smooth V C
  point_recovery : Spec.map (CommRingCat.ofHom (algebraMap V (K c tau))) ≫
    (Spec.map (CommRingCat.ofHom (modelPoint c tau w D i hi center)) ≫
      NormalizedWholeOpenMaps318.finiteChart V d a)=D.genericPoint
  section0 : globalImage c tau w D i hi (OriginalWholeIntrinsicSections318.global0 c tau w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (FinitePivotGenericCanonical318.baseMap V D.pi (D.unit i) d a i)
      (FinitePivotIntegralCanonicalTensors318.integral0 V D.pi (D.unit i) d a i)
  section1 : globalImage c tau w D i hi (OriginalWholeIntrinsicSections318.global1 c tau w D)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V)
      (FinitePivotGenericCanonical318.baseMap V D.pi (D.unit i) d a i)
      (FinitePivotIntegralCanonicalTensors318.integral1 V D.pi (D.unit i) d a i)
include h2 in
/-- The ACTUAL original finite point with an odd normalized pivot twist
and separated other contacts has a produced smooth integral canonical
extension, including both unchanged global sections and the entire
original generic scheme point. The original pivot need not be index0. -/
theorem exists_extension (ht : w (tau:K c tau)≤1)
    (hsep : ∀ j : Fin 3,IsUnit (a i-a (FourRootPivot318.indices i j.succ))) :
    Nonempty (Extension c tau w D i hi) := by
  obtain ⟨P⟩ := exists_center c tau w D i hi ht hsep
  exact ⟨⟨P,OddTwistDilatationEtale318.smooth V D.pi (D.unit i) (a i)
    (others V d i) (others V a i) h2,generic_extension c tau w D i hi P,
    global0_integral c tau w D i hi h2,global1_integral c tau w D i hi h2⟩⟩
end OriginalFinitePivotCanonicalExtension318
