module
public import ChangedKernelProjection318
public section
noncomputable section
namespace ChangedKernelProductScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (S:Type) [CommRing S] [Algebra (OpenJModel318.Base N) S] [Invertible (3:S)]
local notation "R" => OpenJModel318.Base N
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "a" => algebraMap R S
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "hS" => CompletedKernelBaseChange318.mappedDiscriminant (S:=S) A B hD
local notation "T" => ThreeTorsionAlgebra318.Ring A B hD
local notation "T'" => ThreeTorsionCoefficientMap318.Changed (S:=S) A B hD
local notation "C" => LiteralKernelCoordinateRing318.Ring N
local notation "C'" => ChangedKernelProductAlgebra318.Ring N S
local notation "mapK" => ActualKernelBaseChange318.map (S:=S) A B hD
local notation "eqv" => ChangedKernelProductAlgebra318.equivalence N S

@[expose] def iso : ActualLiteralKernelBaseChange318.fiber N S ≅ Spec (CommRingCat.of C') :=
  ActualLiteralKernelBaseChange318.iso N S ≪≫
    Scheme.Spec.mapIso (eqv).toRingEquiv.toCommRingCatIso.symm.op

@[reassoc] theorem iso_inv_base : (iso N S).inv ≫ ActualLiteralKernelBaseChange318.structureMap N S=
    Spec.algebraMap S C' := by
  simp only [iso,Iso.trans_inv,Category.assoc,ActualLiteralKernelBaseChange318.iso_inv_base]
  change Spec.map (CommRingCat.ofHom (eqv).toAlgHom.toRingHom) ≫ Spec.algebraMap S (KernelScalarExtension318.ring N S)=_
  rw [←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) (eqv).toAlgHom.comp_algebraMap

@[reassoc] lemma finite_coordinate : Spec.map (CommRingCat.ofHom (RingHom.fst T' S)) ≫
    Spec.map (CommRingCat.ofHom (eqv).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[R]
        KernelScalarExtension318.ring N S).toRingHom)=
    ThreeTorsionSchemeBaseChange318.schemeMap (S:=S) A B hD ≫
      Spec.map (CommRingCat.ofHom (RingHom.fst T R)) := by
  change _=Spec.map (CommRingCat.ofHom (ThreeTorsionCoefficientMap318.coefficientMap (S:=S) A B hD).toRingHom) ≫ _
  rw [←Spec.map_comp,←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f:C →+* T'=>Spec.map (CommRingCat.ofHom f))
    (ChangedKernelProductAlgebra318.first_projection N S)
@[reassoc] lemma zero_coordinate : Spec.map (CommRingCat.ofHom (RingHom.snd T' S)) ≫
    Spec.map (CommRingCat.ofHom (eqv).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[R]
        KernelScalarExtension318.ring N S).toRingHom)=
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom (RingHom.snd T R)) := by
  rw [←Spec.map_comp,←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f:C →+* S=>Spec.map (CommRingCat.ofHom f))
    (ChangedKernelProductAlgebra318.second_projection N S)

/-- The first product projection gives the unchanged original torsion inclusion
into the actual changed tripling kernel, not an arbitrary component map. -/
@[reassoc] theorem finite_inv : Spec.map (CommRingCat.ofHom (RingHom.fst T' S)) ≫ (iso N S).inv=
    ThreeTorsionTriplingFiber318.toFiber (a A) (a B) hS := by
  apply (ActualKernelBaseChange318.isPullback (S:=S) A B hD).hom_ext
  · simp only [iso,Iso.trans_inv,Category.assoc,ChangedKernelProjection318.scalarIso_inv_map]
    change Spec.map (CommRingCat.ofHom (RingHom.fst T' S)) ≫
      Spec.map (CommRingCat.ofHom (eqv).toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[R]
          KernelScalarExtension318.ring N S).toRingHom) ≫ (LiteralKernelCoordinateRing318.iso N).inv=_
    simp only [finite_coordinate_assoc,←LiteralKernelCoordinateRing318.finite_projection,
      Category.assoc,Iso.hom_inv_id,Category.comp_id,ChangedKernelProjection318.finite_map]
  · change (Spec.map (CommRingCat.ofHom (RingHom.fst T' S)) ≫ (iso N S).inv) ≫
      ActualLiteralKernelBaseChange318.structureMap N S=_
    rw [Category.assoc,iso_inv_base,ThreeTorsionTriplingFiber318.toFiber_snd,←Spec.map_comp]
    rfl

@[reassoc] theorem zero_inv : Spec.map (CommRingCat.ofHom (RingHom.snd T' S)) ≫ (iso N S).inv=
    ChangedKernelProjection318.zero N S := by
  apply (ActualKernelBaseChange318.isPullback (S:=S) A B hD).hom_ext
  · simp only [iso,Iso.trans_inv,Category.assoc,ChangedKernelProjection318.scalarIso_inv_map]
    change Spec.map (CommRingCat.ofHom (RingHom.snd T' S)) ≫
      Spec.map (CommRingCat.ofHom (eqv).toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[R]
          KernelScalarExtension318.ring N S).toRingHom) ≫ (LiteralKernelCoordinateRing318.iso N).inv=_
    simp only [zero_coordinate_assoc,←LiteralKernelCoordinateRing318.zero_projection,
      Category.assoc,Iso.hom_inv_id,Category.comp_id,ChangedKernelProjection318.zero_map]
  · change (Spec.map (CommRingCat.ofHom (RingHom.snd T' S)) ≫ (iso N S).inv) ≫
      ActualLiteralKernelBaseChange318.structureMap N S=_
    rw [Category.assoc,iso_inv_base,ChangedKernelProjection318.zero_base,←Spec.map_comp]
    exact Spec.map_id _
end ChangedKernelProductScheme318
