module
public import ThreeTorsionBaseChange318
public import ThreeTorsionCompletedDoubling318
public section
noncomputable section
namespace ThreeTorsionSchemeBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ThreeTorsionAlgebra318 ThreeTorsionCoefficientMap318 ThreeTorsionBaseChange318
open scoped TensorProduct
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
lemma spec_tensor_right {R S T U:Type} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S U] [IsScalarTower R S U]
    (f:S ⊗[R] T →ₐ[S] U) (g:T →ₐ[R] U)
    (h:∀x:T,f (Algebra.TensorProduct.includeRight x)=g x) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (pullbackSpecIso R S T).inv ≫ pullback.snd _ _=
      Spec.map (CommRingCat.ofHom g.toRingHom) := by
  rw [pullbackSpecIso_inv_snd,←Spec.map_comp]
  have he:f.toRingHom.comp (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom=g.toRingHom := by
    apply RingHom.ext
    exact h
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) he

variable {R S:Type} [CommRing R] [CommRing S] [Algebra R S]
variable [Invertible (3:R)] [Invertible (3:S)] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
local notation "a" => algebraMap R S
local notation "hS" => CompletedKernelBaseChange318.mappedDiscriminant (S:=S) A B hD

@[expose] def schemeMap : ThreeTorsionScheme318.scheme (a A) (a B) hS ⟶ ThreeTorsionScheme318.scheme A B hD :=
  Spec.map (CommRingCat.ofHom (coefficientMap (S:=S) A B hD).toRingHom)
@[expose] def iso : pullback (Spec.map (CommRingCat.ofHom a)) (ThreeTorsionScheme318.structureMap A B hD) ≅
    ThreeTorsionScheme318.scheme (a A) (a B) hS :=
  pullbackSpecIso R S (Ring A B hD) ≪≫
    Scheme.Spec.mapIso (equivalence (S:=S) A B hD).toRingEquiv.toCommRingCatIso.symm.op
@[reassoc] theorem iso_inv_base : (iso (S:=S) A B hD).inv ≫ pullback.fst _ _=
    ThreeTorsionScheme318.structureMap (a A) (a B) hS := by
  change Spec.map (CommRingCat.ofHom (forward (S:=S) A B hD).toRingHom) ≫
    (pullbackSpecIso R S (Ring A B hD)).inv ≫ pullback.fst _ _=_
  rw [pullbackSpecIso_inv_fst',←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) (forward (S:=S) A B hD).comp_algebraMap
@[reassoc] theorem iso_inv_torsion : (iso (S:=S) A B hD).inv ≫ pullback.snd _ _=schemeMap A B hD := by
  change Spec.map (CommRingCat.ofHom (forward (S:=S) A B hD).toRingHom) ≫
    (pullbackSpecIso R S (Ring A B hD)).inv ≫ pullback.snd _ _=_
  exact spec_tensor_right (forward (S:=S) A B hD) (coefficientMap (S:=S) A B hD)
    (forward_includeRight A B hD)

@[reassoc] theorem schemeMap_base : schemeMap (S:=S) A B hD ≫ ThreeTorsionScheme318.structureMap A B hD=
    ThreeTorsionScheme318.structureMap (a A) (a B) hS ≫ Spec.map (CommRingCat.ofHom a) := by
  change Spec.map (CommRingCat.ofHom (coefficientMap (S:=S) A B hD).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Ring A B hD)))=_
  change _=Spec.map (CommRingCat.ofHom (algebraMap S (Changed A B hD))) ≫ Spec.map (CommRingCat.ofHom a)
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  ext r
  exact (coefficientMap (S:=S) A B hD).commutes r

theorem isPullback : IsPullback (schemeMap (S:=S) A B hD)
    (ThreeTorsionScheme318.structureMap (a A) (a B) hS) (ThreeTorsionScheme318.structureMap A B hD)
      (Spec.map (CommRingCat.ofHom a)) := by
  apply IsPullback.flip
  exact IsPullback.of_iso_pullback ⟨(schemeMap_base A B hD).symm⟩ (iso A B hD).symm
    (iso_inv_base A B hD) (iso_inv_torsion A B hD)

lemma coordinate_compatibility : (coefficientMap (S:=S) A B hD).comp (ThreeTorsionScheme318.coordinateMap A B hD)=
    ((ThreeTorsionScheme318.coordinateMap (a A) (a B) hS).restrictScalars R).comp
      (AffineBaseChange318.coefficientMap A B) := by
  apply WeierstrassOverlap318.affine_hom_ext
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,ThreeTorsionScheme318.coordinateMap_x,
      coefficientMap_x,AffineBaseChange318.coefficientMap_x]
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,ThreeTorsionScheme318.coordinateMap_y,
      coefficientMap_y,AffineBaseChange318.coefficientMap_y]
@[reassoc] theorem finite_inclusion : schemeMap (S:=S) A B hD ≫ ThreeTorsionScheme318.inclusion A B hD=
    ThreeTorsionScheme318.inclusion (a A) (a B) hS ≫ WeierstrassCoefficientMap318.finiteMap A B := by
  change Spec.map (CommRingCat.ofHom (coefficientMap (S:=S) A B hD).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (ThreeTorsionScheme318.coordinateMap A B hD).toRingHom)=
    Spec.map (CommRingCat.ofHom (ThreeTorsionScheme318.coordinateMap (a A) (a B) hS).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (AffineBaseChange318.coefficientMap A B).toRingHom)
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f:ShortAffineJacobian318.Ring A B →ₐ[R] Changed (S:=S) A B hD=>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (coordinate_compatibility A B hD)
@[reassoc] theorem completed_inclusion : schemeMap (S:=S) A B hD ≫ ThreeTorsionCompletedDoubling318.inclusion A B hD=
    ThreeTorsionCompletedDoubling318.inclusion (a A) (a B) hS ≫ WeierstrassCoefficientMap318.coefficientMap A B := by
  simp only [ThreeTorsionCompletedDoubling318.inclusion,Category.assoc,finite_inclusion_assoc,
    WeierstrassCoefficientMap318.finite_coefficientMap]
end ThreeTorsionSchemeBaseChange318
