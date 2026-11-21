module
public import ActualFTRayIndexTwo318
public section
noncomputable section
namespace ActualFTRayOrderedClassTags318

open ActualFTRayIndexTwo318

variable {A G J : Type*} [CommGroup A] [Group G] {σ : A →* A}
variable (P : Presentation (G := G) σ) (g : J → A)
variable (hI : Function.Injective g) (hSep : ∀ a b, g a ≠ σ (g b))

include hI hSep in
/-- Distinct allowed positive Gaussian tags cannot overlap as rational
conjugacy classes. This uses a single fixed signed branch, not a
different sign at each fresh prime. -/
theorem unique (x : G) (a b : J) :
    (∃ t : G, t * P.incl (g a) * t⁻¹ = x) →
    (∃ t : G, t * P.incl (g b) * t⁻¹ = x) → a=b := by
  intro ha hb
  rcases (P.conjugate_iff (g a) x).mp ha with A | A <;>
    rcases (P.conjugate_iff (g b) x).mp hb with B | B
  · exact hI (P.inj (A.symm.trans B))
  · exact False.elim (hSep a b (P.inj (A.symm.trans B)))
  · exact False.elim (hSep b a (P.inj (B.symm.trans A)))
  · -- Conjugation in G is injective, so we need no additional inverse data on σ.
    have H : P.j * P.incl (g a) * P.j⁻¹ = P.j * P.incl (g b) * P.j⁻¹ := by
      rw [P.conjugates (g a),P.conjugates (g b)]
      exact A.symm.trans B
    exact hI (P.inj (mul_left_cancel (mul_right_cancel H)))

/-- Tag recovery from an actual chosen Frobenius element, with no
arbitrary class choice hidden in the weight definition. Non-members
of every retained class give exactly none. -/
def select (Frob : ℕ → Option G) (n : ℕ) : Option J := by
  classical
  exact if h : ∃ j : J, ∃ x : G, Frob n = some x ∧
      (∃ t : G, t * P.incl (g j) * t⁻¹ = x)
    then some (Classical.choose h) else none

include hI hSep in
theorem select_eq_some (Frob : ℕ → Option G) (n : ℕ) (j : J) :
    select P g Frob n = some j ↔
    ∃ x : G, Frob n=some x ∧ (∃ t : G, t * P.incl (g j) * t⁻¹=x) := by
  classical
  unfold select
  split
  · rename_i h
    obtain ⟨y,hy,hC⟩ := Classical.choose_spec h
    constructor
    · intro e
      have he := Option.some.inj e
      rw [←he]
      exact ⟨y,hy,hC⟩
    · rintro ⟨x,hx,hX⟩
      have he : x=y := Option.some.inj (hx.symm.trans hy)
      subst x
      exact congrArg some (unique P g hI hSep y _ _ hC hX)
  · rename_i h
    constructor
    · intro e
      cases e
    · intro e
      exact False.elim (h ⟨j,e⟩)

end ActualFTRayOrderedClassTags318
