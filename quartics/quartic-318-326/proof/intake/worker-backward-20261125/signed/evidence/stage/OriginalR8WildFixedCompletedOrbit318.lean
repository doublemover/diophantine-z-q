module
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Logic.Function.Basic
public section
noncomputable section

namespace OriginalR8WildFixedCompletedOrbit318

universe u v w
variable {G : Type u} {I : Type v} [Group G] [MulAction G I]
variable {B : I → Type w} [∀ i, Zero (B i)] [MulAction G (∀ i, B i)]

/-- Actual coordinate insertion at the selected completed factor.
Used to express the stabilizer action, not a unital ring inclusion. -/
@[expose] def seed [DecidableEq I] (i₀ : I) (a : B i₀) : ∀ i, B i :=
  Function.update 0 i₀ a

/-- The extension from one completed local factor is determined by its
stabilizer and the *whole* transitive orbit. The hypothesis perm is the
literal action on coordinates supplied by the finite completion CRT.
No averaging, arbitrary branch identification or assumption that the
other factors are isomorphic without the specified transport. -/
theorem evaluation [DecidableEq I]
    (i₀ : I) (a : B i₀)
    (transitive : ∀ i : I, ∃ g : G, g • i₀ = i)
    (perm : ∀ (g : G) (i : I) (x y : ∀ j, B j),
      x i = y i → (g • x) (g • i) = (g • y) (g • i)) :
    (∀ h : G, h • i₀ = i₀ → (h • seed i₀ a) i₀ = a) ↔
      ∃! x : (∀ i, B i), (∀ g : G, g • x = x) ∧ x i₀ = a := by
  classical
  let z := seed i₀ a
  have hz : z i₀ = a := Function.update_self _ _ _
  constructor
  · intro h
    choose t ht using transitive
    have same (i : I) (p q : G) (hp : p • i₀ = i) (hq : q • i₀ = i) :
        (p • z) i = (q • z) i := by
      let k := q⁻¹ * p
      have hk : k • i₀ = i₀ := by
        rw [show k = q⁻¹ * p from rfl,mul_smul,hp,← hq,inv_smul_smul]
      have hread : (k • z) i₀ = z i₀ := (h k hk).trans hz.symm
      have H := perm q i₀ (k • z) z hread
      have hmul : q * k = p := by simp [k,mul_assoc]
      simpa only [hq,smul_smul,hmul] using H
    let x : ∀ i, B i := fun i => (t i • z) i
    have hbase : x i₀ = a := by
      change (t i₀ • z) i₀ = a
      exact h _ (ht i₀)
    refine ⟨x,⟨?_,hbase⟩,?_⟩
    · intro g
      funext i
      let j := g⁻¹ • i
      have hgj : g • j = i := smul_inv_smul _ _
      have hread : x j = (t j • z) j := rfl
      have H := perm g j x (t j • z) hread
      rw [hgj,smul_smul] at H
      have htx : (g * t j) • i₀ = i := by rw [mul_smul,ht j,hgj]
      exact H.trans (same i (g * t j) (t i) htx (ht i))
    · intro y hy
      funext i
      have H := perm (t i) i₀ y z (hy.2.trans hz.symm)
      simpa only [hy.1 (t i),ht i,x] using H
  · rintro ⟨x,hx,-⟩ h hfix
    have H := perm h i₀ z x (hz.trans hx.2.symm)
    rw [hfix,hx.1 h,hx.2] at H
    exact H

end OriginalR8WildFixedCompletedOrbit318

#print axioms OriginalR8WildFixedCompletedOrbit318.evaluation
