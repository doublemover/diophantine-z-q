module
public import FourRootOrderSignAction318
public import ContactGlobalSigns318
public section
noncomputable section
namespace ContactGlobalSignAction318
open AlgebraicGeometry CategoryTheory ContactKummerOrder318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
local instance : IsIntegralHom (ContactProjectiveModel318.modelMap c) :=
  ContactProjectiveModel318.modelMap_integral c

theorem open_composition (s t : Fin 4 → Bool) :
    ContactGlobalSigns318.openMap c s ≫ ContactGlobalSigns318.openMap c t =
      ContactGlobalSigns318.openMap c (fun i => Bool.xor (s i) (t i)) := by
  unfold ContactGlobalSigns318.openMap
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (congrArg (fun e : OpenOrder c ≃ₐ[OpenBase] OpenOrder c => e x)
    (FourRootOrderSignAction318.composition _ t s)).trans (by simp [Bool.xor_comm, ContactGlobalSigns318.openEquiv])

theorem open_identity : ContactGlobalSigns318.openMap c (fun _ => false) = 𝟙 _ := by
  unfold ContactGlobalSigns318.openMap ContactGlobalSigns318.openEquiv
  rw [FourRootOrderSignAction318.identity]
  exact Spec.map_id _

/-- Exact composition on the entire original contact normalization. -/
@[reassoc] theorem composition (s t : Fin 4 → Bool) :
    ContactGlobalSigns318.map c s ≫ ContactGlobalSigns318.map c t =
      ContactGlobalSigns318.map c (fun i => Bool.xor (s i) (t i)) := by
  apply Scheme.Hom.normalization.hom_ext (ContactProjectiveModel318.coverMap c)
    _ _ (ContactProjectiveModel318.modelMap c)
  · change ContactProjectiveModel318.sourceOpen c ≫
      (ContactGlobalSigns318.map c s ≫ ContactGlobalSigns318.map c t) =
      ContactProjectiveModel318.sourceOpen c ≫ ContactGlobalSigns318.map c _
    rw [←Category.assoc, ContactGlobalSigns318.on_open, Category.assoc,
      ContactGlobalSigns318.on_open, ←Category.assoc, open_composition,
      ContactGlobalSigns318.on_open]
  · rw [Category.assoc, ContactGlobalSigns318.over_line, ContactGlobalSigns318.over_line]
    rfl
  · rw [ContactGlobalSigns318.over_line]
    rfl

theorem identity : ContactGlobalSigns318.map c (fun _ => false) = 𝟙 _ := by
  apply Scheme.Hom.normalization.hom_ext (ContactProjectiveModel318.coverMap c)
    _ _ (ContactProjectiveModel318.modelMap c)
  · change ContactProjectiveModel318.sourceOpen c ≫ ContactGlobalSigns318.map c _ =
      ContactProjectiveModel318.sourceOpen c ≫ 𝟙 _
    rw [ContactGlobalSigns318.on_open, open_identity, Category.id_comp, Category.comp_id]
  · rw [ContactGlobalSigns318.over_line]
    rfl
  · rw [Category.id_comp]
    rfl

theorem commute (s t : Fin 4 → Bool) :
    ContactGlobalSigns318.map c s ≫ ContactGlobalSigns318.map c t =
      ContactGlobalSigns318.map c t ≫ ContactGlobalSigns318.map c s := by
  rw [composition, composition]
  congr 1
  funext i
  exact Bool.xor_comm _ _
end ContactGlobalSignAction318
