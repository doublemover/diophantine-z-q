module
public import CompletedKernelBaseChange318
public import KernelScalarExtension318
public import LiteralKernelCover318
public import CompletedAdditionCoefficient318
public section
noncomputable section
namespace ActualKernelBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type} [CommRing R] [CommRing S] [Algebra R S]
variable (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
local notation "a" => algebraMap R S
local notation "hS" => CompletedKernelBaseChange318.mappedDiscriminant (S:=S) A B hD

/-- Every compatibility field now has its proved actual producer. -/
@[expose] def data := CompletedKernelBaseChange318.data A B hD
  (CompletedAdditionCoefficient318.tripling (S:=S) A B hD hS)
@[expose] def map := ZeroFiberBaseChange318.map (data (S:=S) A B hD)
@[expose] def iso := ZeroFiberBaseChange318.iso (data (S:=S) A B hD)
@[reassoc] theorem iso_inv_base : (iso (S:=S) A B hD).inv ≫
    pullback.snd (CompletedIteratedAddition318.tripling (a A) (a B) hS) (WeierstrassGluing318.infinity (a A) (a B))=
      pullback.snd (pullback.snd (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B))
        (Spec.map (CommRingCat.ofHom a)) := ZeroFiberBaseChange318.fromBaseChange_snd (data A B hD)
@[reassoc] theorem iso_inv_kernel : (iso (S:=S) A B hD).inv ≫ map A B hD=
    pullback.fst (pullback.snd (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B))
      (Spec.map (CommRingCat.ofHom a)) := ZeroFiberBaseChange318.fromBaseChange_map (data A B hD)
theorem isPullback : IsPullback (map (S:=S) A B hD)
    (pullback.snd (CompletedIteratedAddition318.tripling (a A) (a B) hS) (WeierstrassGluing318.infinity (a A) (a B)))
    (pullback.snd (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B))
    (Spec.map (CommRingCat.ofHom a)) := ZeroFiberBaseChange318.isPullback (data A B hD)
@[reassoc] theorem map_curve : map (S:=S) A B hD ≫
    pullback.fst (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B)=
    pullback.fst (CompletedIteratedAddition318.tripling (a A) (a B) hS) (WeierstrassGluing318.infinity (a A) (a B)) ≫
      WeierstrassCoefficientMap318.coefficientMap A B := ZeroFiberBaseChange318.map_fst (data A B hD)
@[reassoc] theorem map_base : map (S:=S) A B hD ≫
    pullback.snd (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B)=
    pullback.snd (CompletedIteratedAddition318.tripling (a A) (a B) hS) (WeierstrassGluing318.infinity (a A) (a B)) ≫
      Spec.map (CommRingCat.ofHom a) := ZeroFiberBaseChange318.map_snd (data A B hD)
end ActualKernelBaseChange318

namespace ActualLiteralKernelBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (S:Type) [CommRing S] [Algebra (OpenJModel318.Base N) S]
local notation "R" => OpenJModel318.Base N
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "a" => algebraMap R S
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "hS" => CompletedKernelBaseChange318.mappedDiscriminant (S:=S) A B hD
abbrev fiber := pullback (CompletedIteratedAddition318.tripling (a A) (a B) hS)
  (WeierstrassGluing318.infinity (a A) (a B))
@[expose] def structureMap : fiber N S ⟶ Spec (CommRingCat.of S) := pullback.snd _ _

/-- The kernel of actual tripling on the actual changed-coefficient curve
has the exact scalar-extended full-kernel coordinate ring. -/
@[expose] def iso : fiber N S ≅ Spec (CommRingCat.of (KernelScalarExtension318.ring N S)) :=
  ActualKernelBaseChange318.iso (S:=S) A B hD ≪≫
    pullbackSymmetry (LiteralKernelFiniteEtale318.structureMap N) (Spec.map (CommRingCat.ofHom a)) ≪≫
      KernelScalarExtension318.iso N S

@[reassoc] theorem iso_inv_base : (iso N S).inv ≫ structureMap N S=
    Spec.algebraMap S (KernelScalarExtension318.ring N S) := by
  simp only [iso,Iso.trans_inv,structureMap,Category.assoc,ActualKernelBaseChange318.iso_inv_base]
  change (KernelScalarExtension318.iso N S).inv ≫
    (pullbackSymmetry (LiteralKernelFiniteEtale318.structureMap N) (Spec.map (CommRingCat.ofHom a))).inv ≫
      pullback.snd (LiteralKernelFiniteEtale318.structureMap N) (Spec.map (CommRingCat.ofHom a))=_
  rw [pullbackSymmetry_inv_comp_snd,KernelScalarExtension318.iso_inv_base]

theorem finite_etale_flat_surjective : IsFinite (structureMap N S) ∧ Etale (structureMap N S) ∧
    Flat (structureMap N S) ∧ Surjective (structureMap N S) := by
  have H:=ActualKernelBaseChange318.isPullback (S:=S) A B hD
  obtain ⟨hf,he,hfl,hs⟩:=LiteralKernelCover318.finite_etale_flat_surjective N
  exact ⟨MorphismProperty.of_isPullback H hf,MorphismProperty.of_isPullback H he,
    MorphismProperty.of_isPullback H hfl,MorphismProperty.of_isPullback H hs⟩
end ActualLiteralKernelBaseChange318
