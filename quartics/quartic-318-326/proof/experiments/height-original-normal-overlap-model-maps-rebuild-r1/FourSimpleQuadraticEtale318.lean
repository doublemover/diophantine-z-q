module
public import SimpleQuadraticEtalePoint318
public import Mathlib.RingTheory.TensorProduct.Basic
public section
noncomputable section
namespace FourSimpleQuadraticEtale318
open SimpleQuadraticEtalePoint318
open scoped TensorProduct
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (q : Fin 4 → R)
abbrev Pair01 := EtaleRing (q 0) ⊗[R] EtaleRing (q 1)
abbrev Pair23 := EtaleRing (q 2) ⊗[R] EtaleRing (q 3)
abbrev Ring := Pair01 q ⊗[R] Pair23 q

theorem etale : Algebra.Etale R (Ring q) := by
  letI (i : Fin 4) : Algebra.Etale R (EtaleRing (q i)) := SimpleQuadraticEtalePoint318.etale _
  letI : Algebra.Etale R (Pair01 q) := Algebra.Etale.comp R (EtaleRing (q 0)) (Pair01 q)
  letI : Algebra.Etale R (Pair23 q) := Algebra.Etale.comp R (EtaleRing (q 2)) (Pair23 q)
  exact Algebra.Etale.comp R (Pair01 q) (Ring q)

@[expose] def rootInclusion (i : Fin 4) : EtaleRing (q i) →ₐ[R] Ring q := by
  fin_cases i
  · exact Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft
  · exact Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeRight
  · exact Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft
  · exact Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight
@[expose] def generator (i : Fin 4) : Ring q := rootInclusion q i (SimpleQuadraticEtalePoint318.root (q i))
theorem generator_relation (i : Fin 4) :
    (generator q i)^2+generator q i=algebraMap R (Ring q) (q i) := by
  have h := congrArg (rootInclusion q i) (SimpleQuadraticEtalePoint318.root_equation (q i))
  simpa only [map_add,map_pow,AlgHom.commutes,generator] using h

variable {S : Type*} [CommRing S] (ev : R →+* S) (hq : ∀ i,ev (q i)=0)
@[expose] def pointAlg : letI : Algebra R S := ev.toAlgebra; Ring q →ₐ[R] S := by
  letI : Algebra R S := ev.toAlgebra
  let f (i : Fin 4) : EtaleRing (q i) →ₐ[R] S :=
    { SimpleQuadraticEtalePoint318.point (q i) ev (hq i) with
      commutes' := SimpleQuadraticEtalePoint318.point_scalar (q i) ev (hq i) }
  exact Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift (f 0) (f 1) (fun _ _ => Commute.all _ _))
    (Algebra.TensorProduct.lift (f 2) (f 3) (fun _ _ => Commute.all _ _))
    (fun _ _ => Commute.all _ _)
@[expose] def point : Ring q →+* S := (pointAlg q ev hq).toRingHom

theorem point_scalar (r : R) : point q ev hq (algebraMap R (Ring q) r)=ev r :=
  (pointAlg q ev hq).commutes r

theorem point_generator (i : Fin 4) : point q ev hq (generator q i)=0 := by
  letI : Algebra R S := ev.toAlgebra
  fin_cases i <;> simp [point,pointAlg,generator,rootInclusion,
    Algebra.TensorProduct.lift_tmul,SimpleQuadraticEtalePoint318.point_root]
end FourSimpleQuadraticEtale318
