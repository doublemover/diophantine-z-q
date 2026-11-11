module
public import ContactBoundedPointRank318
public section
noncomputable section
namespace ContactBoundedPointRestriction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (f : ContactBoundedPointFamily318.SchemePoint c N b) (d : Fin (N+1))
local notation "E" => ContactBoundedPointFamily318.extract c N b f
local notation "U" => ContactBoundedRankCover318.cover c N b E
local notation "a" => ContactBoundedRankData318.base c N b E d
local notation "x" => ContactBoundedPointRank318.point c N b f d
/-- Entire original ideal restriction agrees with the actual fixed-rank
universal fiber. The proof retains all nilpotent and coefficient data. -/
lemma ideal : (ContactBoundedRankData318.data c N b E d).ideal=
    (ContactSchemePointFamily318.extract c d.val a x).ideal := by
  have hg := ClosedPullbackKernel318.ideal _ _ _ _ (ContactBoundedPointFamily318.cartesian c N b f)
  have hc := ClosedPullbackKernel318.ideal _ _ _ _ (ContactBoundedUniversalFamily318.cartesian c N d)
  have hl := ClosedPullbackKernel318.ideal _ _ _ _ (ContactSchemePointFamily318.cartesian c d.val a x)
  change (ContactBoundedPointFamily318.into c N b f).ker.comap
    (ContactBoundedHilbertBaseChange318.sourceMap c b a (U.f d) rfl)=_
  rw [hg,← Scheme.IdealSheafData.comap_comp,RelativeSchemeCoefficient318.comp]
  rw [hl,hc,← Scheme.IdealSheafData.comap_comp,RelativeSchemeCoefficient318.comp,
    ContactBoundedPointRank318.factor_into]
lemma data : ContactBoundedRankData318.data c N b E d=ContactSchemePointFamily318.extract c d.val a x :=
  ContactSchemeHilbertData318.Data.ext (ideal c N b f d)
lemma point : ContactBoundedRankData318.point c N b E d=x := by
  change ContactSchemeHilbertEquiv318.equivalence c d.val a (ContactBoundedRankData318.data c N b E d)=x
  rw [data]
  exact (ContactSchemeHilbertEquiv318.equivalence c d.val a).apply_symm_apply x
end ContactBoundedPointRestriction318
