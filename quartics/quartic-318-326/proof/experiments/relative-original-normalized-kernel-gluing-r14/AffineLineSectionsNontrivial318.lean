module
public import OriginalLineAffineModel318
public section
noncomputable section
namespace AffineLineSectionsNontrivial318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable (A : CommRingCat.{u}) [Nontrivial A] (L : Line (Spec A))

/-- Genuine affine line sections cannot vanish over a nonzero ring:
the ACTUAL section module has stalk rank one at every actual prime. -/
theorem nontrivial : Nontrivial (OriginalLineAffineModel318.sections A L) := by
  by_contra hn
  letI : Subsingleton (OriginalLineAffineModel318.sections A L) :=
    not_nontrivial_iff_subsingleton.mp hn
  let p : PrimeSpectrum A := Classical.ofNonempty
  have hr := (OriginalLineAffineModel318.properties A L).2.2 p
  have hz : (0:ℕ)=1 := by
    simpa only [Module.rankAtStalk_eq_zero_of_subsingleton,Pi.zero_apply] using hr
  exact Nat.zero_ne_one hz
end AffineLineSectionsNontrivial318
