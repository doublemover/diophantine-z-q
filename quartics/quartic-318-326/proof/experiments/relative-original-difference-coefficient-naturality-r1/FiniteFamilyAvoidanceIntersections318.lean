module
public import FiniteFamilyAvoidanceEquiv318
public section
noncomputable section
namespace FiniteFamilyAvoidanceIntersections318
open AlgebraicGeometry CategoryTheory
open FiniteFamilyAvoidanceOpen318 FiniteFamilyAvoidanceFactor318
universe u
variable {Z B X : Scheme.{u}} (p : Z ⟶ B) [UniversallyClosed p] (q : Z ⟶ X)
lemma monotone {U V : X.Opens} (h : U≤V) : locus p q U≤locus p q V := by
  intro b hb
  rw [mem_locus] at hb ⊢
  exact fun z hz => h (hb z hz)
/-- The overlap is the genuine intersection avoidance open. Requiring
the whole family in each source chart equals requiring it in their intersection. -/
lemma intersection (U V : X.Opens) : locus p q (U⊓V)=locus p q U⊓locus p q V := by
  ext b
  change b∈locus p q (U⊓V) ↔ b∈locus p q U ∧ b∈locus p q V
  simp only [mem_locus]
  constructor
  · intro h
    exact ⟨fun z hz => (h z hz).1,fun z hz => (h z hz).2⟩
  · rintro ⟨hU,hV⟩ z hz
    exact ⟨hU z hz,hV z hz⟩
lemma top : locus p q ⊤=⊤ := by
  ext b
  simp only [mem_locus]
  exact iff_true_intro (fun _ _ => trivial)
end FiniteFamilyAvoidanceIntersections318
