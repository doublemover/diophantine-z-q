module
public import FourSimpleQuadraticUniversal318
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace FourSimpleQuadraticBaseChange318
open FourSimpleQuadraticEtale318
open scoped TensorProduct
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (q : Fin 4 → R)
abbrev mapped := fun i => algebraMap R S (q i)
abbrev Changed := Ring (mapped (S:=S) q)
@[expose] def coefficientMap : Ring q →ₐ[R] Changed (S:=S) q :=
  FourSimpleQuadraticUniversal318.lift q (generator (mapped (S:=S) q))
    (fun i => by
      rw [IsScalarTower.algebraMap_apply R S (Changed (S:=S) q)]
      exact generator_relation (mapped (S:=S) q) i)
    (FourSimpleQuadraticUniversal318.derivative_unit _)

theorem coefficientMap_generator (i : Fin 4) : coefficientMap (S:=S) q (generator q i)=
    generator (mapped (S:=S) q) i := FourSimpleQuadraticUniversal318.lift_generator _ _ _ _ i

@[expose] def forward : S ⊗[R] Ring q →ₐ[S] Changed (S:=S) q :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (coefficientMap q) (fun _ _ => Commute.all _ _)
@[expose] def backward : Changed (S:=S) q →ₐ[S] S ⊗[R] Ring q :=
  FourSimpleQuadraticUniversal318.lift (mapped (S:=S) q)
    (fun i => Algebra.TensorProduct.includeRight (generator q i))
    (fun i => by
      have h := congrArg (Algebra.TensorProduct.includeRight : Ring q →ₐ[R] S ⊗[R] Ring q)
        (generator_relation q i)
      simp only [map_pow,map_add,AlgHom.commutes] at h
      rw [IsScalarTower.algebraMap_apply R S (S ⊗[R] Ring q)] at h
      exact h)
    (fun i => by
      have h := (FourSimpleQuadraticUniversal318.derivative_unit q i).map
        (Algebra.TensorProduct.includeRight : Ring q →ₐ[R] S ⊗[R] Ring q).toRingHom
      simpa only [map_add,map_mul,map_ofNat,map_one] using h)

theorem backward_generator (i : Fin 4) : backward (S:=S) q (generator (mapped (S:=S) q) i)=
    Algebra.TensorProduct.includeRight (generator q i) :=
  FourSimpleQuadraticUniversal318.lift_generator _ _ _ _ i

theorem forward_includeRight (x : Ring q) : forward (S:=S) q (Algebra.TensorProduct.includeRight x)=
    coefficientMap (S:=S) q x := by
  simp [forward,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]

theorem forward_backward : (forward (S:=S) q).comp (backward q)=AlgHom.id S _ := by
  apply FourSimpleQuadraticUniversal318.hom_ext
  intro i
  simp only [AlgHom.comp_apply,backward_generator,forward_includeRight,
    coefficientMap_generator,AlgHom.id_apply]

theorem backward_forward : (backward (S:=S) q).comp (forward q)=AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply FourSimpleQuadraticUniversal318.hom_ext
    intro i
    simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,forward_includeRight,
      coefficientMap_generator,backward_generator,AlgHom.id_apply]

@[expose] def equivalence : S ⊗[R] Ring q ≃ₐ[S] Ring (mapped (S:=S) q) :=
  AlgEquiv.ofAlgHom (forward q) (backward q) (forward_backward q) (backward_forward q)

theorem equivalence_generator (i : Fin 4) : equivalence (S:=S) q (1 ⊗ₜ[R] generator q i)=
    generator (mapped (S:=S) q) i := by
  change forward (S:=S) q (Algebra.TensorProduct.includeRight (generator q i))=_
  rw [forward_includeRight,coefficientMap_generator]
end FourSimpleQuadraticBaseChange318
