module
public import ActualFTRayOrderedClassTags318
public section
noncomputable section
namespace ActualFTRelativeTag318

open ActualFTRayIndexTwo318 ActualFTRayOrderedClassTags318

variable {A G J : Type*} [CommGroup A] [Group G] {σ : A →* A}
variable (R : Presentation (G := G) σ) (g : J → A)
variable (F : ℕ → Option G)

/-- Keep only rational Frobenius values lying in the relative
Artin subgroup. Non-split and ramified primes do not gain a tag. -/
def relative (n : ℕ) : Option A := by
  classical
  exact if h : ∃ a : A, F n=some (R.incl a)
    then some (Classical.choose h) else none

theorem relative_eq (n : ℕ) (a : A) :
    relative R F n=some a ↔ F n=some (R.incl a) := by
  classical
  unfold relative
  split
  · rename_i h
    have H := Classical.choose_spec h
    constructor
    · intro E
      have ha := Option.some.inj E
      rw [←ha]
      exact H
    · intro E
      exact congrArg some (R.inj (Option.some.inj (H.symm.trans E)))
  · rename_i h
    constructor
    · intro E
      cases E
    · intro E
      exact False.elim (h ⟨a,E⟩)

/-- No external classTag equivalence is required: transform one exact
classification of the old finite selected subset. The same Frob n
is used on both sides; no independent tag picks at the two endpoints. -/
theorem support_iff (hI : Function.Injective g) (hSep : ∀ a b, g a ≠ σ (g b))
    (allowed : A → Prop)
    (hAllowed : ∀ a, allowed a ↔ ∃ j, a=g j ∨ a=σ (g j)) (n : ℕ) :
    (select R g F n).isSome ↔ ∃ a, relative R F n=some a ∧ allowed a := by
  constructor
  · intro h
    cases hO : select R g F n with
    | none =>
      have hb : (none : Option J).isSome = true :=
        (congrArg (fun t : Option J => t.isSome) hO).symm.trans h
      have h0 : (false : Bool) = true := (Option.isSome_none (α:=J)).symm.trans hb
      cases h0
    | some j =>
      obtain ⟨y,hy,hyC⟩ := (select_eq_some R g hI hSep F n j).mp hO
      obtain hY | hY := (R.conjugate_iff (g j) y).mp hyC
      · exact ⟨g j,(relative_eq R F n _).mpr (hy.trans (congrArg some hY)),
          (hAllowed _).mpr ⟨j,Or.inl rfl⟩⟩
      · exact ⟨σ (g j),(relative_eq R F n _).mpr (hy.trans (congrArg some hY)),
          (hAllowed _).mpr ⟨j,Or.inr rfl⟩⟩
  · rintro ⟨a,ha,hb⟩
    obtain ⟨j,h|h⟩ := (hAllowed a).mp hb
    · have hf := (relative_eq R F n a).mp ha
      have hy : ∃ t : G, t * R.incl (g j) * t⁻¹=R.incl a :=
        (R.conjugate_iff (g j) _).mpr (Or.inl (congrArg R.incl h))
      rw [(select_eq_some R g hI hSep F n j).mpr ⟨R.incl a,hf,hy⟩] <;> rfl
    · have hf := (relative_eq R F n a).mp ha
      have hy : ∃ t : G, t * R.incl (g j) * t⁻¹=R.incl a :=
        (R.conjugate_iff (g j) _).mpr (Or.inr (congrArg R.incl h))
      rw [(select_eq_some R g hI hSep F n j).mpr ⟨R.incl a,hf,hy⟩] <;> rfl

end ActualFTRelativeTag318
