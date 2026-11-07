module
public import InfinitySmooth318
public import AffineSchemeBaseChange318
public section
noncomputable section
namespace InfinityBaseChange318
open InfinityChart318
open scoped TensorProduct
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

abbrev Changed (A B:R) := Ring (algebraMap R S A) (algebraMap R S B)
@[expose] def coefficientMap (A B:R) : Ring A B →ₐ[R] Changed (S:=S) A B :=
  lift A B (x _ _) (z _ _) (by
    rw [IsScalarTower.algebraMap_apply R S (Changed (S:=S) A B) A,
      IsScalarTower.algebraMap_apply R S (Changed (S:=S) A B) B]
    exact relation _ _)
@[simp] theorem coefficientMap_x (A B:R) : coefficientMap (S:=S) A B (x A B)=x _ _ := lift_x ..
@[simp] theorem coefficientMap_z (A B:R) : coefficientMap (S:=S) A B (z A B)=z _ _ := lift_z ..

@[expose] def forward (A B:R) : S ⊗[R] Ring A B →ₐ[S] Changed (S:=S) A B :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (coefficientMap A B) (fun _ _ => Commute.all _ _)
@[expose] def backward (A B:R) : Changed (S:=S) A B →ₐ[S] S ⊗[R] Ring A B :=
  lift (R:=S) (S:=S ⊗[R] Ring A B) (algebraMap R S A) (algebraMap R S B)
    (Algebra.TensorProduct.includeRight (x A B)) (Algebra.TensorProduct.includeRight (z A B)) (by
      have h := congrArg (Algebra.TensorProduct.includeRight : Ring A B →ₐ[R] S ⊗[R] Ring A B)
        (relation A B)
      simp only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes] at h
      rw [IsScalarTower.algebraMap_apply R S (S ⊗[R] Ring A B) A,
        IsScalarTower.algebraMap_apply R S (S ⊗[R] Ring A B) B] at h
      exact h)
@[simp] theorem backward_x (A B:R) : backward (S:=S) A B (x _ _)=Algebra.TensorProduct.includeRight (x A B) := lift_x ..
@[simp] theorem backward_z (A B:R) : backward (S:=S) A B (z _ _)=Algebra.TensorProduct.includeRight (z A B) := lift_z ..
@[simp] theorem forward_includeRight (A B:R) (a:Ring A B) :
    forward (S:=S) A B (Algebra.TensorProduct.includeRight a)=coefficientMap A B a := by
  simp [forward,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]
@[simp] theorem forward_includeLeft (A B:R) (s:S) :
    forward (S:=S) A B ((Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] Ring A B) s)=algebraMap S _ s := by
  simp [forward,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul]

theorem forward_backward (A B:R) : (forward (S:=S) A B).comp (backward A B)=AlgHom.id S _ := by
  apply hom_ext
  · simp only [AlgHom.comp_apply,backward_x,forward_includeRight,coefficientMap_x,AlgHom.id_apply]
  · simp only [AlgHom.comp_apply,backward_z,forward_includeRight,coefficientMap_z,AlgHom.id_apply]
theorem backward_forward (A B:R) : (backward (S:=S) A B).comp (forward A B)=AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply hom_ext (R:=R) (S:=S ⊗[R] Ring A B) A B
    · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,forward_includeRight,
        coefficientMap_x,backward_x,AlgHom.id_apply]
    · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,forward_includeRight,
        coefficientMap_z,backward_z,AlgHom.id_apply]

/-- Actual tensor base change of the entire infinity chart, with explicit coordinate maps. -/
@[expose] def baseChangeEquiv (A B:R) : S ⊗[R] Ring A B ≃ₐ[S] Changed (S:=S) A B :=
  AlgEquiv.ofAlgHom (forward A B) (backward A B) (forward_backward A B) (backward_forward A B)

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
/-- The actual infinity-chart Scheme pullback is the changed-coefficient infinity chart. -/
@[expose] def schemeIso (A B:R) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (InfinitySmooth318.structureMap A B) ≅
      InfinitySmooth318.scheme (algebraMap R S A) (algebraMap R S B) :=
  pullbackSpecIso R S (Ring A B) ≪≫
    Scheme.Spec.mapIso (baseChangeEquiv (S:=S) A B).toRingEquiv.toCommRingCatIso.symm.op

theorem schemeIso_inv_base (A B:R) : (schemeIso (S:=S) A B).inv ≫ pullback.fst _ _=
    InfinitySmooth318.structureMap (algebraMap R S A) (algebraMap R S B) := by
  change Spec.map (CommRingCat.ofHom (forward (S:=S) A B).toRingHom) ≫
    (pullbackSpecIso R S (Ring A B)).inv ≫ pullback.fst _ _=_
  rw [pullbackSpecIso_inv_fst',←Spec.map_comp]
  congr 1
  ext s
  exact (forward A B).commutes s


theorem schemeIso_inv_curve (A B:R) : (schemeIso (S:=S) A B).inv ≫ pullback.snd _ _=
    Spec.map (CommRingCat.ofHom (coefficientMap (S:=S) A B).toRingHom) := by
  have he : (forward (S:=S) A B).toRingHom.comp
      (Algebra.TensorProduct.includeRight : Ring A B →ₐ[R] S ⊗[R] Ring A B).toRingHom=
      (coefficientMap (S:=S) A B).toRingHom := by
    apply RingHom.ext
    intro x
    exact forward_includeRight (S:=S) A B x
  change Spec.map (CommRingCat.ofHom (forward (S:=S) A B).toRingHom) ≫
    (pullbackSpecIso R S (Ring A B)).inv ≫ pullback.snd _ _=_
  rw [pullbackSpecIso_inv_snd R S (Ring A B),←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) he

end InfinityBaseChange318
