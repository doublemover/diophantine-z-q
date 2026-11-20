module
public import SelectedCompletedMultiplication318
public import GluedNegation318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassGluing318
open SelectedPointedShortScaling318

namespace SelectedSignedMultiplication318
variable {R : Type u} [CommRing R]
variable (A B C D : R) (r : Rˣ) (hA : A = (r:R)^4*C) (hB : B = (r:R)^6*D)
local notation "γ" => gluedMap A B C D r hA hB

/-- On the actual completed curve, switching to the negative root changes
the actual comparison by the genuine target negation. -/
theorem negative_branch (hnA : A = (↑(-r):R)^4*C) (hnB : B = (↑(-r):R)^6*D) :
    gluedMap A B C D (-r) hnA hnB = γ ≫ GluedNegation318.negation A B := by
  apply FiniteChartSchematicDensity318.hom_ext_to_completed C D A B
  · simp only [Category.assoc,GluedNegation318.negation_over_base,glued_base]
  · have hf : finiteMap A B C D (-r) hnA hnB =
        finiteMap A B C D r hA hB ≫ GluedNegation318.finiteNeg A B := by
      unfold finiteMap GluedNegation318.finiteNeg
      rw [←Spec.map_comp]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
        (congrArg AlgHom.toRingHom
          (SelectedShortAffineScaling318.hom_neg_scale A B C D r hA hB hnA hnB))
    calc
      _ = finiteMap A B C D (-r) hnA hnB ≫ finiteChart A B := finite_glued ..
      _ = (finiteMap A B C D r hA hB ≫ GluedNegation318.finiteNeg A B) ≫ finiteChart A B := by
        rw [hf]
      _ = _ := by
        symm
        rw [←Category.assoc,finite_glued,Category.assoc,GluedNegation318.finiteChart_negation,
          ←Category.assoc]

variable {X Y : R} {T : Scheme.{u}}

/-- Actual vanishing of [m], with the base projection of the given point
and the original zero section retained. -/
abbrev Killed (h : IsUnit (-16*(4*X^3+27*Y^2))) (m : ℕ) (p : T ⟶ scheme X Y) : Prop :=
  p ≫ SelectedCompletedMultiplication318.mul X Y h m =
    (p ≫ structureMap X Y) ≫ infinity X Y

/-- The genuine positive lower-order equations, not only a nonzero test. -/
abbrev ExactTests (h : IsUnit (-16*(4*X^3+27*Y^2))) (m : ℕ) (p : T ⟶ scheme X Y) : Prop :=
  Killed h m p ∧ ∀ k : ℕ, 0 < k → k < m → ¬Killed h k p

variable (g : IsUnit (-16*(4*C^3+27*D^2)))
local notation "g₁" => SelectedCompletedAdditiveScaling318.target_smooth_disc A B C D r hA hB g

/-- Both the full kernel equation and every lower-order equation are
preserved by the same pointed completed scaling. -/
theorem exact_tests_iff (m : ℕ) (p : T ⟶ scheme C D) :
    ExactTests g₁ m (p ≫ γ) ↔ ExactTests g m p := by
  let h (k : ℕ) := SelectedCompletedMultiplication318.kills_iff A B C D r hA hB g k p
  constructor
  · intro hp
    exact ⟨(h m).mp hp.1,fun k hk hm h0 => hp.2 k hk hm ((h k).mpr h0)⟩
  · intro hp
    exact ⟨(h m).mpr hp.1,fun k hk hm h0 => hp.2 k hk hm ((h k).mp h0)⟩

end SelectedSignedMultiplication318

#print axioms SelectedSignedMultiplication318.negative_branch
#print axioms SelectedSignedMultiplication318.exact_tests_iff
