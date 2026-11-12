module
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace AwayRingEquivalence318
variable {R S : Type*} [CommRing R] [CommRing S]
  (e : R ≃+* S) (a : R) (b : S) (h : e a=b)
@[expose] def map : Localization.Away a →+* Localization.Away b :=
  IsLocalization.Away.lift a (show IsUnit
    (((algebraMap S (Localization.Away b)).comp e.toRingHom) a) from by
      change IsUnit (algebraMap S (Localization.Away b) (e a))
      rw [h]
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b) b)

theorem map_base (r : R) : map e a b h (algebraMap R (Localization.Away a) r)=
    algebraMap S (Localization.Away b) (e r) := IsLocalization.Away.lift_eq _ _ _

theorem inverse_element : e.symm b=a := by rw [←h]; exact e.symm_apply_apply _

theorem inverse_map : (map e.symm b a (inverse_element e a b h)).comp (map e a b h)=
    RingHom.id (Localization.Away a) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  ext r
  simp only [RingHom.comp_apply,map_base,e.symm_apply_apply,RingHom.id_apply]

theorem map_inverse : (map e a b h).comp (map e.symm b a (inverse_element e a b h))=
    RingHom.id (Localization.Away b) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers b)
  ext r
  simp only [RingHom.comp_apply,map_base,e.apply_symm_apply,RingHom.id_apply]

@[expose] def equivalence : Localization.Away a ≃+* Localization.Away b where
  __ := map e a b h
  invFun := map e.symm b a (inverse_element e a b h)
  left_inv r := RingHom.congr_fun (inverse_map e a b h) r
  right_inv r := RingHom.congr_fun (map_inverse e a b h) r
end AwayRingEquivalence318
