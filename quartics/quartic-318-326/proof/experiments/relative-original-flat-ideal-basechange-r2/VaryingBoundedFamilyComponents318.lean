module
public import VaryingGlobalFreeQuotientEquiv318
public import VaryingBoundedDegreeFamily318
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace VaryingBoundedFamilyComponents318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingBoundedDegreeFamily318
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
@[expose] def familyInclusion : (n d : ℕ) → d ≤ n → (degreeFamily R A d ⟶ family R A n)
  | 0,0,_ => 𝟙 _
  | 0,d+1,h => False.elim (by omega)
  | n+1,d,h => if he : d=n+1 then
      eqToHom (congrArg (degreeFamily R A) he) ≫ coprod.inr
    else familyInclusion R A n d (by omega) ≫ coprod.inl
instance inclusion_open (n d : ℕ) (h : d ≤ n) : IsOpenImmersion (inclusion R A n d h) := by
  induction n generalizing d with
  | zero =>
    have hd : d=0 := by omega
    subst d
    simp only [inclusion]
    infer_instance
  | succ n ih =>
    by_cases he : d=n+1
    · subst d
      simp only [inclusion,dif_pos rfl,eqToHom_refl,Category.id_comp]
      infer_instance
    · rw [inclusion,dif_neg he]
      letI := ih d (by omega)
      infer_instance
/-- The bounded family's rank-d component is the actual original rank-d
universal quotient family, by categorical coproduct pullbacks. -/
lemma cartesian (n d : ℕ) (h : d ≤ n) : IsPullback (familyInclusion R A n d h)
    (degreeProjection R A d) (projection R A n) (inclusion R A n d h) := by
  induction n generalizing d with
  | zero =>
    have hd : d=0 := by omega
    subst d
    simpa only [familyInclusion,inclusion,projection] using
      (IsPullback.of_id_fst (f := degreeProjection R A 0))
  | succ n ih =>
    by_cases he : d=n+1
    · subst d
      simpa only [familyInclusion,inclusion,dif_pos rfl,eqToHom_refl,Category.id_comp,projection] using
        (isPullback_inr_inr_coprodMap (projection R A n) (degreeProjection R A (n+1))).flip
    · rw [familyInclusion,dif_neg he,inclusion,dif_neg he]
      exact (ih d (by omega)).paste_horiz
        (isPullback_inl_inl_coprodMap (projection R A n) (degreeProjection R A (n+1))).flip
end VaryingBoundedFamilyComponents318
