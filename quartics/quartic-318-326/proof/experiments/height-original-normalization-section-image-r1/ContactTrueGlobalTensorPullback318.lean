module
public import IntrinsicFramedTensorSections318
public import ContactGlobalBicanonical318
public import ContactBicanonicalGenericPullback318
public section
noncomputable section
namespace ContactTrueGlobalTensorPullback318
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (i : Fin 4)
local notation "A" => ContactIntrinsicFrames318.BranchRing c i
local notation "j" => ContactIntrinsicFrames318.branchEmbedding c i
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "h" => ContactIntrinsicFrames318.branch_structure c i
local notation "e" => ContactDifferentialFrames318.sourceLocalizationFrame c i
local notation "x" => ContactFrameNormalization318.sourceCoordinate c i

/-- Restriction of an arbitrary GENUINE global Omega tensor Omega section
on the proper Q-normalization to its entire original branch affine chart,
then the canonical algebraic tensor via the actual normalized frame. -/
@[expose] def chartTensor (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    KaehlerDifferential ℚ A ⊗[A] KaehlerDifferential ℚ A :=
  IntrinsicFramedTensorSections318.tensor j p h e x
    ((ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op s)

lemma chartTensor_q0 : chartTensor c i (ContactGlobalBicanonical318.q0 c) =
    ContactBicanonicalCoefficients318.branchQ0 c i •
      (KaehlerDifferential.D ℚ A x ⊗ₜ[A] KaehlerDifferential.D ℚ A x) := by
  unfold chartTensor
  rw [ContactGlobalBicanonical318.q0_restrict c (some i)]
  exact IntrinsicFramedTensorSections318.tensor_weighted j p h e _ x
    (ContactFrameNormalization318.source_coordinate_normalized c i)

lemma chartTensor_q1 : chartTensor c i (ContactGlobalBicanonical318.q1 c) =
    ContactBicanonicalCoefficients318.branchQ1 c i •
      (KaehlerDifferential.D ℚ A x ⊗ₜ[A] KaehlerDifferential.D ℚ A x) := by
  unfold chartTensor
  rw [ContactGlobalBicanonical318.q1_restrict c (some i)]
  exact IntrinsicFramedTensorSections318.tensor_weighted j p h e _ x
    (ContactFrameNormalization318.source_coordinate_normalized c i)

variable {K B : Type*} [Field K] [CharZero K] [CommRing B]
  [Algebra K B] [Algebra ℚ B] [IsScalarTower ℚ K B]
  (f : A →ₐ[ℚ] B)

/-- The literal whole scheme map into the original proper smooth curve,
through its actual branch embedding, not a displayed point-coordinate tuple. -/
@[expose] def schemeMap : Spec (CommRingCat.of B) ⟶ ContactGlobalSmooth318.Model c :=
  Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j

lemma schemeMap_over_Q : schemeMap c i f ≫ p =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ B)) := by
  rw [schemeMap,Category.assoc,h,←Spec.map_comp]
  congr 1
  ext r
  exact f.commutes r

/-- Full balanced pullback of the actual global sections, including the
true Q-to-K change of differential base. Its source is the original
intrinsic bicanonical sheaf, not the arithmetic candidate line. -/
@[expose] def image (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    KaehlerDifferential K B ⊗[B] KaehlerDifferential K B :=
  BaseChangingDifferentialTensor318.tensorMap (S:=K) f (chartTensor c i s)

lemma image_q0 : image c i f (ContactGlobalBicanonical318.q0 c) =
    ContactBicanonicalGenericPullback318.branchImage c i f := by
  rw [image,chartTensor_q0,BaseChangingDifferentialTensor318.tensorMap_weighted,
    BaseChangingDifferentialTensor318.pureImage_D]
  rfl
lemma image_q1 : image c i f (ContactGlobalBicanonical318.q1 c) =
    f (ContactBicanonicalCoefficients318.branchQ1 c i) •
      (KaehlerDifferential.D K B (f x) ⊗ₜ[B] KaehlerDifferential.D K B (f x)) := by
  rw [image,chartTensor_q1,BaseChangingDifferentialTensor318.tensorMap_weighted,
    BaseChangingDifferentialTensor318.pureImage_D]
end ContactTrueGlobalTensorPullback318
