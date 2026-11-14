module
public import OriginalNormalClosureGalois318
public import LabeledContactInertiaSigns318
public section
noncomputable section
namespace LabeledFullInertiaCardinality318
variable {G : Type*} [Group G] (H : Subgroup G)

lemma trivial_card (h : ∀ g, g ∈ H ↔ g = 1) : Nat.card H = 1 := by
  have heq : H = ⊥ := by ext g; simpa only [Subgroup.mem_bot] using h g
  rw [heq]
  simp

/-- Count the ENTIRE specified inertia subgroup, not merely two known elements. -/
lemma double_card (g : G) (hg : g ≠ 1)
    (h : ∀ a, a ∈ H ↔ a = 1 ∨ a = g) : Nat.card H = 2 := by
  classical
  let e : H ≃ Bool :=
    { toFun := fun a => if a.val = 1 then false else true
      invFun := fun b => if b then ⟨g,(h g).mpr (Or.inr rfl)⟩ else ⟨1,H.one_mem⟩
      left_inv := by
        intro a
        apply Subtype.ext
        rcases (h a.val).mp a.property with ha | ha
        · simp [ha]
        · simp [ha,hg]
      right_inv := by intro b; cases b <;> simp [hg] }
  rw [Nat.card_congr e]
  simp

variable {L : Type*} [Field L] [Algebra (RatFunc ℚ) L]
  (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)

lemma labeled_card (I : Subgroup (L ≃ₐ[RatFunc ℚ] L)) (k : Fin 4)
    (h : ∀ σ, σ ∈ I ↔ σ = 1 ∨ labels σ = FourBinaryCharacters318.flip k) :
    Nat.card I = 2 := by
  let σ := labels.symm (FourBinaryCharacters318.flip k)
  have hn : σ ≠ 1 := by
    intro he
    have hh := congrArg labels he
    exact LabeledContactInertiaSigns318.flip_ne_one k (by simpa [σ] using hh)
  apply double_card I σ hn
  intro a
  rw [h a]
  have he : labels a = FourBinaryCharacters318.flip k ↔ a = σ := by
    rw [← labels.injective.eq_iff]
    simp only [σ, labels.apply_symm_apply]
  rw [he]
end LabeledFullInertiaCardinality318
