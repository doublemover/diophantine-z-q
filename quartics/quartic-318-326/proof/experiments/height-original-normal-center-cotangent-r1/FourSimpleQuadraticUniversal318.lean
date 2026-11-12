module
public import FourSimpleQuadraticEtale318
public import SimpleQuadraticEtaleUniversal318
public section
noncomputable section
namespace FourSimpleQuadraticUniversal318
open FourSimpleQuadraticEtale318
open scoped TensorProduct
set_option maxHeartbeats 1200000
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (q : Fin 4 → R) (z : Fin 4 → S)
  (hz : ∀ i,(z i)^2+z i=algebraMap R S (q i))
  (hd : ∀ i,IsUnit (2*z i+1))
@[expose] def lift : Ring q →ₐ[R] S :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift
      (SimpleQuadraticEtaleUniversal318.lift (q 0) (z 0) (hz 0) (hd 0))
      (SimpleQuadraticEtaleUniversal318.lift (q 1) (z 1) (hz 1) (hd 1))
      (fun _ _ => Commute.all _ _))
    (Algebra.TensorProduct.lift
      (SimpleQuadraticEtaleUniversal318.lift (q 2) (z 2) (hz 2) (hd 2))
      (SimpleQuadraticEtaleUniversal318.lift (q 3) (z 3) (hz 3) (hd 3))
      (fun _ _ => Commute.all _ _))
    (fun _ _ => Commute.all _ _)

theorem lift_generator (i : Fin 4) : lift q z hz hd (generator q i)=z i := by
  fin_cases i <;> simp [lift,generator,rootInclusion,Algebra.TensorProduct.lift_tmul,
    SimpleQuadraticEtaleUniversal318.lift_root]

theorem hom_ext {f g : Ring q →ₐ[R] S}
    (h : ∀ i,f (generator q i)=g (generator q i)) : f=g := by
  apply Algebra.TensorProduct.ext
  · apply Algebra.TensorProduct.ext
    · apply SimpleQuadraticEtaleUniversal318.hom_ext
      exact h 0
    · apply SimpleQuadraticEtaleUniversal318.hom_ext
      exact h 1
  · apply Algebra.TensorProduct.ext
    · apply SimpleQuadraticEtaleUniversal318.hom_ext
      exact h 2
    · apply SimpleQuadraticEtaleUniversal318.hom_ext
      exact h 3

theorem derivative_unit (i : Fin 4) : IsUnit (2*generator q i+1) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := SimpleQuadraticEtalePoint318.EtaleRing (q i))
    (SimpleQuadraticEtalePoint318.derivativeValue (q i))
  have he : algebraMap (SimpleQuadraticEtalePoint318.RootRing (q i))
      (SimpleQuadraticEtalePoint318.EtaleRing (q i))
      (SimpleQuadraticEtalePoint318.derivativeValue (q i))=
      2*SimpleQuadraticEtalePoint318.root (q i)+1 := by
    simp [SimpleQuadraticEtalePoint318.derivativeValue,
      SimpleQuadraticEtalePoint318.equation,SimpleQuadraticEtalePoint318.root,
      map_add,map_mul,map_ofNat]
  rw [he] at h
  simpa only [map_add,map_mul,map_ofNat,map_one,generator] using
    h.map (rootInclusion q i).toRingHom
end FourSimpleQuadraticUniversal318
