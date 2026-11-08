module
public import LiteralKernelCoordinateRing318
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace KernelScalarExtension318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (S:Type) [CommRing S] [Algebra (OpenJModel318.Base N) S]
local notation "R" => OpenJModel318.Base N
local notation "C" => LiteralKernelCoordinateRing318.Ring N
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "p" => LiteralKernelFiniteEtale318.structureMap N
abbrev ring := S ⊗[R] C
abbrev scheme := pullback b p

/-- The comparison preserves the actual base projection and the actual
kernel-coordinate isomorphism, before taking Spec of scalar extension. -/
@[expose] def comparison : scheme N S ⟶ pullback b (Spec.algebraMap R C) :=
  pullback.map b p b (Spec.algebraMap R C) (𝟙 _) (LiteralKernelCoordinateRing318.iso N).hom (𝟙 _)
    (by simp) (by simpa only [Category.comp_id] using (LiteralKernelCoordinateRing318.iso_hom_base N).symm)
instance comparison_iso : IsIso (comparison N S) := by dsimp only [comparison]; infer_instance
@[reassoc] lemma comparison_fst : comparison N S ≫ pullback.fst _ _=pullback.fst b p := by simp [comparison]
@[reassoc] lemma comparison_snd : comparison N S ≫ pullback.snd _ _=
    pullback.snd b p ≫ (LiteralKernelCoordinateRing318.iso N).hom := by simp [comparison]
@[reassoc] lemma comparison_inv_fst : inv (comparison N S) ≫ pullback.fst b p=pullback.fst b (Spec.algebraMap R C) := by
  rw [←comparison_fst N S,←Category.assoc,IsIso.inv_hom_id,Category.id_comp]
@[reassoc] lemma comparison_inv_snd : inv (comparison N S) ≫ pullback.snd b p=
    pullback.snd b (Spec.algebraMap R C) ≫ (LiteralKernelCoordinateRing318.iso N).inv := by
  apply (cancel_mono (LiteralKernelCoordinateRing318.iso N).hom).mp
  rw [Category.assoc,Category.assoc,Iso.inv_hom_id,Category.comp_id,←comparison_snd,
    ←Category.assoc,IsIso.inv_hom_id,Category.id_comp]

/-- Actual Spec model of the literal kernel after every coefficient algebra
extension, including nonreduced and nonflat coefficient algebras. -/
@[expose] def iso : scheme N S ≅ Spec (CommRingCat.of (ring N S)) :=
  asIso (comparison N S) ≪≫ pullbackSpecIso R S C
@[reassoc] theorem iso_inv_base : (iso N S).inv ≫ pullback.fst b p=Spec.algebraMap S (ring N S) := by
  rw [iso,Iso.trans_inv,asIso_inv,Category.assoc,comparison_inv_fst,pullbackSpecIso_inv_fst']
@[reassoc] theorem iso_inv_kernel : (iso N S).inv ≫ pullback.snd b p=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[R] ring N S).toRingHom) ≫
      (LiteralKernelCoordinateRing318.iso N).inv := by
  rw [iso,Iso.trans_inv,asIso_inv,Category.assoc,comparison_inv_snd,←Category.assoc,pullbackSpecIso_inv_snd]
  rfl

lemma finite : Module.Finite S (ring N S) := by
  haveI:=LiteralKernelCoordinateRing318.finite N
  infer_instance
lemma free : Module.Free S (ring N S) := by
  haveI:=LiteralKernelCoordinateRing318.free N
  infer_instance
lemma etale : Algebra.Etale S (ring N S) := by
  haveI:=LiteralKernelCoordinateRing318.etale N
  infer_instance
lemma rank_nine [NeZero N] [Nontrivial S] : Module.finrank S (ring N S)=9 := by
  haveI:=LiteralKernelCoordinateRing318.free N
  change Module.finrank S (S ⊗[R] C)=9
  rw [Module.finrank_baseChange,LiteralKernelCoordinateRing318.rank_nine_of_level_ne_zero]
end KernelScalarExtension318
