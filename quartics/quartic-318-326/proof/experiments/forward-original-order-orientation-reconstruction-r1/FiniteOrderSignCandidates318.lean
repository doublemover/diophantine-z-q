module
public import FiniteOrderSignChoices318
public section
noncomputable section
namespace FiniteOrderSignCandidates318
open FiniteOrderSignChoices318
variable {ι : Type*} [Fintype ι]
@[expose] def candidates (a b : ι → ℕ) (P : (ι → Bool) → Prop) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter (fun s => Nat.Coprime (leftLCM a b s) (rightLCM a b s) ∧ P s)
lemma mem_iff (a b : ι → ℕ) (P : (ι → Bool) → Prop) (s : ι → Bool) :
    s∈candidates a b P ↔ Nat.Coprime (leftLCM a b s) (rightLCM a b s) ∧ P s := by
  classical
  simp only [candidates,Finset.mem_filter,Finset.mem_univ,true_and]
lemma subset_two (a b : ι → ℕ) (P : (ι → Bool) → Prop) (q : ℕ) (hq : q.Prime)
    (t : ι → Bool) (ht : ∀ i,q∣left a b t i) : candidates a b P⊆{t,flip t} := by
  classical
  intro s hs
  have he:=two_choices a b q hq t ht s ((mem_iff a b P s).mp hs).1
  simpa only [Finset.mem_insert,Finset.mem_singleton] using he
lemma card_le_two (a b : ι → ℕ) (P : (ι → Bool) → Prop) (q : ℕ) (hq : q.Prime)
    (t : ι → Bool) (ht : ∀ i,q∣left a b t i) : (candidates a b P).card≤2 := by
  classical
  exact (Finset.card_le_card (subset_two a b P q hq t ht)).trans Finset.card_le_two
lemma nonempty_iff (a b : ι → ℕ) (P : (ι → Bool) → Prop) (q : ℕ) (hq : q.Prime)
    (t : ι → Bool) (ht : ∀ i,q∣left a b t i) :
    (candidates a b P).Nonempty ↔ t∈candidates a b P ∨ flip t∈candidates a b P := by
  classical
  constructor
  · rintro ⟨s,hs⟩
    have he:=two_choices a b q hq t ht s ((mem_iff a b P s).mp hs).1
    rcases he with rfl|rfl
    · exact Or.inl hs
    · exact Or.inr hs
  · rintro (h|h)
    · exact ⟨t,h⟩
    · exact ⟨flip t,h⟩
end FiniteOrderSignCandidates318
