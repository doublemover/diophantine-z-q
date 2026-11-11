module
public import IntegralRootPointMaps318
public section
noncomputable section
namespace FourRootCoefficientEquivalence318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S]
  (e : R ≃+* S) (a : Fin 4 → R) (b : Fin 4 → S) (hab : ∀ i,e (a i)=b i)
@[expose] def map : FourRootOrder318.Order a →+* FourRootOrder318.Order b := by
  letI : Algebra R (FourRootOrder318.Order b) :=
    ((algebraMap S (FourRootOrder318.Order b)).comp e.toRingHom).toAlgebra
  exact (IntegralRootPointMaps318.fourMap a (FourRootOrderSigns318.generator b) (fun i => by
    rw [FourRootOrderSigns318.generator_square]
    change algebraMap S _ (b i)=algebraMap S _ (e (a i))
    rw [hab i])).toRingHom

theorem map_scalar (r : R) : map e a b hab (algebraMap R (FourRootOrder318.Order a) r)=
    algebraMap S (FourRootOrder318.Order b) (e r) := by
  letI : Algebra R (FourRootOrder318.Order b) :=
    ((algebraMap S (FourRootOrder318.Order b)).comp e.toRingHom).toAlgebra
  exact (IntegralRootPointMaps318.fourMap a (FourRootOrderSigns318.generator b) (fun i => by
    rw [FourRootOrderSigns318.generator_square]
    change algebraMap S _ (b i)=algebraMap S _ (e (a i))
    rw [hab i])).commutes r

theorem map_generator (i : Fin 4) : map e a b hab (FourRootOrderSigns318.generator a i)=
    FourRootOrderSigns318.generator b i := by
  letI : Algebra R (FourRootOrder318.Order b) :=
    ((algebraMap S (FourRootOrder318.Order b)).comp e.toRingHom).toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator _ _ _ i

theorem inverse_coefficients (i : Fin 4) : e.symm (b i)=a i := by rw [←hab i]; exact e.symm_apply_apply _

theorem inverse_map :
    (map e.symm b a (inverse_coefficients e a b hab)).comp (map e a b hab)=
      RingHom.id (FourRootOrder318.Order a) := by
  apply IntegralRootPointMaps318.four_ringHom_ext
  · ext r
    simp only [RingHom.comp_apply,map_scalar,RingHom.id_apply,e.symm_apply_apply]
  · intro i
    simp only [RingHom.comp_apply,map_generator,RingHom.id_apply]

theorem map_inverse :
    (map e a b hab).comp (map e.symm b a (inverse_coefficients e a b hab))=
      RingHom.id (FourRootOrder318.Order b) := by
  apply IntegralRootPointMaps318.four_ringHom_ext
  · ext r
    simp only [RingHom.comp_apply,map_scalar,RingHom.id_apply,e.apply_symm_apply]
  · intro i
    simp only [RingHom.comp_apply,map_generator,RingHom.id_apply]

@[expose] def equivalence : FourRootOrder318.Order a ≃+* FourRootOrder318.Order b where
  __ := map e a b hab
  invFun := map e.symm b a (inverse_coefficients e a b hab)
  left_inv r := RingHom.congr_fun (inverse_map e a b hab) r
  right_inv r := RingHom.congr_fun (map_inverse e a b hab) r
end FourRootCoefficientEquivalence318
