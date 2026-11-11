module
public import ContactLinearFiberDisjoint318
public import BoundedFiniteFamilyAvoidance318
public import FiniteAffineRankComparison318
public import ContactHilbertData318
public section
noncomputable section
namespace ContactHilbertAvoidance318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactHilbertData318 FiniteFamilyAvoidanceOpen318
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (N : ℕ)
  (D : BoundedRank S c N)
local notation "Z" => D.val.ideal.subscheme
local notation "p" => ContactHilbertData318.projection S c D.val
local notation "i" => D.val.ideal.subschemeι
/-- Original projective-line map on the WHOLE actual divisor family. -/
@[expose] def toLine : Z ⟶ ProjectiveJLine318.scheme ℚ :=
  i ≫ pullback.fst (ContactIntrinsicDifferentials318.structureMap c)
    (RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) S) ≫ ContactProjectiveModel318.modelMap c
@[expose] def sourceOpen (j : Fin (N+1)) : (ProjectiveJLine318.scheme ℚ).Opens :=
  ContactLinearFiberDisjoint318.locus (j.val : ℚ)
lemma pair_cover (j k : Fin (N+1)) (h : j≠k) : sourceOpen N j⊔sourceOpen N k=⊤ := by
  apply ContactLinearFiberDisjoint318.pair_cover
  have hv : j.val≠k.val := fun e => h (Fin.ext e)
  exact_mod_cast hv
lemma rank_bound (x : PrimeSpectrum S) : p.finrank x≤N := by
  exact D.property x
@[expose] def locus (j : Fin (N+1)) : (Spec S).Opens :=
  FiniteFamilyAvoidanceOpen318.locus p (toLine S c N D) (sourceOpen N j)
/-- N+1 EXPLICIT rational fiber-complement charts cover every bounded
original finite-flat quotient family after Zariski coefficient localization. -/
lemma exists_chart (x : Spec S) : ∃ j,x∈locus S c N D j :=
  BoundedFiniteFamilyAvoidance318.exists_avoiding p (toLine S c N D) N
    (sourceOpen N) (pair_cover N) (rank_bound S c N D) x
lemma covers : (⨆ j,locus S c N D j)=⊤ :=
  BoundedFiniteFamilyAvoidance318.cover p (toLine S c N D) N
    (sourceOpen N) (pair_cover N) (rank_bound S c N D)
/-- Actual whole coefficient open cover; no one source chart is assumed
to contain the moving divisor globally. -/
@[expose] def cover : (Spec S).OpenCover where
  I₀ := Fin (N+1)
  X j := (locus S c N D j).toScheme
  f j := (locus S c N D j).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun _ => inferInstance⟩
    intro x
    obtain ⟨j,hj⟩ := exists_chart S c N D x
    exact ⟨j,⟨x,hj⟩,rfl⟩
end ContactHilbertAvoidance318
