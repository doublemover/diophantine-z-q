module
public import ChangedKernelProductAlgebra318
public section
noncomputable section
namespace ChangedKernelProjection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (S:Type) [CommRing S] [Algebra (OpenJModel318.Base N) S] [Invertible (3:S)]
local notation "R" => OpenJModel318.Base N
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "a" => algebraMap R S
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "hS" => CompletedKernelBaseChange318.mappedDiscriminant (S:=S) A B hD
local notation "tr" => CompletedIteratedAddition318.tripling (a A) (a B) hS
local notation "e" => WeierstrassGluing318.infinity (a A) (a B)
local notation "mapK" => ActualKernelBaseChange318.map (S:=S) A B hD
local notation "C" => LiteralKernelCoordinateRing318.Ring N

@[reassoc] theorem finite_map : ThreeTorsionTriplingFiber318.toFiber (a A) (a B) hS ≫ mapK=
    ThreeTorsionSchemeBaseChange318.schemeMap (S:=S) A B hD ≫ ThreeTorsionTriplingFiber318.toFiber A B hD := by
  apply pullback.hom_ext (f:=CompletedIteratedAddition318.tripling A B hD)
    (g:=WeierstrassGluing318.infinity A B)
  · simp only [Category.assoc,ActualKernelBaseChange318.map_curve,
      ThreeTorsionTriplingFiber318.toFiber_fst_assoc,ThreeTorsionTriplingFiber318.toFiber_fst,
      ThreeTorsionSchemeBaseChange318.completed_inclusion]
  · simp only [Category.assoc,ActualKernelBaseChange318.map_base,
      ThreeTorsionTriplingFiber318.toFiber_snd_assoc,ThreeTorsionTriplingFiber318.toFiber_snd,
      ThreeTorsionSchemeBaseChange318.schemeMap_base]

@[expose] def zero : Spec (CommRingCat.of S) ⟶ ActualLiteralKernelBaseChange318.fiber N S :=
  pullback.lift e (𝟙 _) (by rw [CompletedZeroTripling318.tripling_origin,Category.id_comp])
@[reassoc] lemma zero_curve : zero N S ≫ pullback.fst tr e=e := by simp [zero]
@[reassoc] lemma zero_base : zero N S ≫ pullback.snd tr e=𝟙 _ := by simp [zero]
@[reassoc] theorem zero_map : zero N S ≫ mapK=Spec.map (CommRingCat.ofHom a) ≫ LiteralKernelZeroSection318.toKernel N := by
  apply pullback.hom_ext (f:=CompletedIteratedAddition318.tripling A B hD)
    (g:=WeierstrassGluing318.infinity A B)
  · simp only [Category.assoc,ActualKernelBaseChange318.map_curve,zero_curve_assoc,
      LiteralKernelZeroSection318.toKernel_fst,WeierstrassCoefficientMap318.coefficientMap_infinity]
  · simp only [Category.assoc,ActualKernelBaseChange318.map_base,zero_base_assoc,
      LiteralKernelZeroSection318.toKernel_snd,Category.id_comp,Category.comp_id]

/-- Exact comparison with the original kernel projection, in addition to
its already established scalar-base projection. -/
@[reassoc] theorem scalarIso_inv_map : (ActualLiteralKernelBaseChange318.iso N S).inv ≫ mapK=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[R]
      KernelScalarExtension318.ring N S).toRingHom) ≫ (LiteralKernelCoordinateRing318.iso N).inv := by
  simp only [ActualLiteralKernelBaseChange318.iso,Iso.trans_inv,Category.assoc,
    ActualKernelBaseChange318.iso_inv_kernel]
  change (KernelScalarExtension318.iso N S).inv ≫
    (pullbackSymmetry (LiteralKernelFiniteEtale318.structureMap N) (Spec.map (CommRingCat.ofHom a))).inv ≫
      pullback.fst (LiteralKernelFiniteEtale318.structureMap N) (Spec.map (CommRingCat.ofHom a))=_
  rw [pullbackSymmetry_inv_comp_fst,KernelScalarExtension318.iso_inv_kernel]
end ChangedKernelProjection318
