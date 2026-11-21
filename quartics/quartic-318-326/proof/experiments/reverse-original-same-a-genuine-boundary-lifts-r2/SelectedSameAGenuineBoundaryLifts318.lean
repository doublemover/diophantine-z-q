module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# The canonical degree-zero connecting boundary produces true global lifts

Use the actual opens of the closed fibre and the given actual short exact
sequence as a sequence of additive sheaves. There is no supplied
cohomology equivalence and no Čech-acyclicity input.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameAGenuineBoundaryLifts318

universe u w

variable (X : TopCat.{u})
local notation "J" => Opens.grothendieckTopology X
local notation "T" => (⊤ : Opens X)
variable [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The usual H0 boundary applied to a section on the literal top open. -/
noncomputable def boundary {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact) :
    S.X₃.obj.obj (op T) →+ S.X₁.H 1 :=
  (Sheaf.H.δ hS 0 1 rfl).comp (Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm.toAddMonoidHom

theorem boundary_natural {S S' : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (g : S ⟶ S')
    (s : S.X₃.obj.obj (op T)) :
    boundary X hS' (g.τ₃.hom.app (op T) s) =
      Sheaf.H.map g.τ₁ 1 (boundary X hS s) := by
  change Sheaf.H.δ hS' 0 1 rfl
    ((Sheaf.H.equiv₀ S'.X₃ isTerminalTop).symm (g.τ₃.hom.app (op T) s)) = _
  rw [← Sheaf.H.equiv₀_symm_naturality isTerminalTop g.τ₃ s]
  exact Sheaf.H.δ_naturality 0 1 rfl hS hS' g ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s)

/-- The actual global-section map lifts a global form whose actual
connecting class is zero. -/
theorem actual_global_lift {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (s : S.X₃.obj.obj (op T)) (h : boundary X hS s = 0) :
    ∃ t : S.X₂.obj.obj (op T), S.g.hom.app (op T) t = s :=
  Sheaf.H.longSequence_equiv₀_exact₃ hS isTerminalTop s h

/-- In the application these are the two actual invariant basis forms. -/
theorem two_actual_global_lifts {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (s₁ s₂ : S.X₃.obj.obj (op T)) (h₁ : boundary X hS s₁ = 0) (h₂ : boundary X hS s₂ = 0) :
    ∃ t₁ t₂ : S.X₂.obj.obj (op T),
      S.g.hom.app (op T) t₁ = s₁ ∧ S.g.hom.app (op T) t₂ = s₂ := by
  obtain ⟨t₁, ht₁⟩ := actual_global_lift X hS s₁ h₁
  obtain ⟨t₂, ht₂⟩ := actual_global_lift X hS s₂ h₂
  exact ⟨t₁, t₂, ht₁, ht₂⟩

end SelectedSameAGenuineBoundaryLifts318
