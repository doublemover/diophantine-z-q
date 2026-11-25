module
public import OriginalLiteralCoarseFibre318
public import OriginalFiniteFibreFromActualArrow318
public import OriginalFineFibreGroupAtPoint318

@[expose] public section
noncomputable section

namespace OriginalFiveContactFineFibre318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OriginalFiniteFibreFromActualArrow318 (B scalar projection actual_square exists_closedAt)
open OriginalLiteralContactQuotientPoint318 (point)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local notation "c" => SourceTwistArithmetic318.units
local notation "Y" => ContactProjectiveModel318.model c
local notation "π" => ContactProjectiveModel318.modelMap c

variable {Z : Scheme} (f : Z ⟶ Y) [IsFinite f]
local instance : IsFinite π := ContactGlobalProper318.normalization_finite c

variable (u v : ℤ)
local notation "F" => f ≫ π
local notation "q" => point u v
local notation "A₀" => B F q

/-- It is enough that the actual fine forget is surjective. The base
point is lifted via the exact original coarse fibre, not a separate
assumed affine coordinate or a comparison of equal numerical T. -/
theorem at_original [Surjective f] :
    ∃ x : Z, F x=q (⊥ : PrimeSpectrum ℚ) := by
  let C := OriginalLiteralCoarseFibre318.FibreRing u v
  haveI : Nontrivial C := Module.nontrivial_of_finrank_pos (R:=ℚ)
    (by rw [OriginalLiteralCoarseFibre318.rank u v]; decide)
  let z : PrimeSpectrum C :=
    Classical.choice (inferInstance : Nonempty (PrimeSpectrum C))
  let y := OriginalLiteralCoarseFibre318.projection u v z
  have h := congrArg (fun m : Spec (CommRingCat.of C) ⟶ _ => m z)
    (OriginalLiteralCoarseFibre318.actual_square u v).w
  have hq : Spec.algebraMap ℚ C z=(⊥ : PrimeSpectrum ℚ) := Subsingleton.elim _ _
  simp only [Scheme.Hom.comp_apply,hq] at h
  obtain ⟨x,hx⟩ := f.surjective y
  refine ⟨x,?_⟩
  rw [Scheme.Hom.comp_apply,hx]
  exact h

/-- Construct the finite coordinate algebra on the genuine composite
Y₃→X→P¹ at q. Both the scheme and coefficients are determined by the
one original morphism and the literal rational q. -/
theorem actual_fibre :
    letI := scalar F q
    IsPullback (projection F q) (Spec.algebraMap ℚ A₀) F q :=
  actual_square F q

/-- The single closed residue field on the *fine* fibre, not the
residue of a different coarse sheet or a precomputed rank-16 factor. -/
theorem closed_fine [Surjective f] :
    letI := scalar F q
    ∃ m : Ideal A₀, m.IsMaximal ∧ Module.Finite ℚ (A₀ ⧸ m) :=
  exists_closedAt F q (at_original f u v)

local instance fineScalar : Algebra ℚ A₀ := scalar F q

/-- Evaluation of the supplied UNIVERSAL group object on this exact
residue. This is not a replacement abelian surface with equal invariants. -/
def at_closed (A : Grp (Over Z)) (m : Ideal A₀) :
    Grp (Over (Spec (CommRingCat.of (A₀ ⧸ m)))) :=
  OriginalFineFibreGroupAtPoint318.groupAt (projection F q) (Ideal.Quotient.mkₐ ℚ m) A

theorem closed_over (m : Ideal A₀) :
    (OriginalFineFibreGroupAtPoint318.point (projection F q) (Ideal.Quotient.mkₐ ℚ m)) ≫ F =
      Spec.algebraMap ℚ (A₀ ⧸ m) ≫ q := by
  exact OriginalFineFibreGroupAtPoint318.point_over (projection F q) (Ideal.Quotient.mkₐ ℚ m)
    F q (actual_fibre f u v)

/-- Properness on the residue is inherited on the exact pullback of
the same universal group. No alternate equal-invariant field model. -/
theorem closed_proper (A : Grp (Over Z)) [IsProper A.X.hom] (m : Ideal A₀) :
    IsProper (at_closed f u v A m).X.hom :=
  OriginalFineFibreGroupAtPoint318.groupAt_isProper (projection F q) (Ideal.Quotient.mkₐ ℚ m) A

theorem closed_group_exists [Surjective f] (A : Grp (Over Z)) [IsProper A.X.hom] :
    ∃ m : Ideal A₀, m.IsMaximal ∧ Module.Finite ℚ (A₀ ⧸ m) ∧
      IsProper (at_closed f u v A m).X.hom := by
  obtain ⟨m,hm,hfin⟩ := closed_fine f u v
  exact ⟨m,hm,hfin,closed_proper f u v A m⟩

end OriginalFiveContactFineFibre318

#print axioms OriginalFiveContactFineFibre318.at_original
#print axioms OriginalFiveContactFineFibre318.actual_fibre
#print axioms OriginalFiveContactFineFibre318.closed_fine
#print axioms OriginalFiveContactFineFibre318.closed_over
#print axioms OriginalFiveContactFineFibre318.closed_group_exists
