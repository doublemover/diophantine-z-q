module
public import FourRootSignBaseChange318
public section
noncomputable section
namespace FourRootOrderSignAction318
open FourRootOrderSigns318
variable {F : Type*} [CommRing F] (a : Fin 4 → F)
/-- Composition is the literal pointwise Boolean exclusive-or. -/
theorem composition (s t : Fin 4 → Bool) :
    (signEquiv a s).trans (signEquiv a t) = signEquiv a (fun i => Bool.xor (s i) (t i)) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply FourRootSignBaseChange318.hom_ext
  intro i
  change signEquiv a t (signEquiv a s (generator a i)) =
    signEquiv a (fun j => Bool.xor (s j) (t j)) (generator a i)
  rw [signEquiv_generator, signEquiv_generator]
  cases hs : s i <;> cases ht : t i <;>
    simp [hs, ht, signEquiv_generator]

theorem identity : signEquiv a (fun _ => false) = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply FourRootSignBaseChange318.hom_ext
  intro i
  exact signEquiv_generator a (fun _ => false) i
end FourRootOrderSignAction318
