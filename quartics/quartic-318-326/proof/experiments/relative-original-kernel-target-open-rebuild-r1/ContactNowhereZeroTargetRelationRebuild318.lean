module
public import ContactNowhereZeroTargetBaseChangeRebuild318
public section
noncomputable section
namespace ContactNowhereZeroTargetRelationRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "N" => ContactArbitraryNowhereZeroOpen318.scheme R c L
local notation "V" => ContactKernelGlobalTargetOpenRebuild318.locus R c L
local notation "n" => ContactOriginalGlobalKernelNormalizationRebuild318.normalize R c L
local notation "k" => ContactNowhereZeroSourceOpenRebuild318.inclusion R c L
local notation "m" => ContactNowhereZeroTargetNormalizationRebuild318.map R c L
include R c L in
/-- Restricting to the produced target open changes NO relation on
morphisms from any test scheme. This does not yet identify the Picard orbit sheaf. -/
lemma same_fiber {T : Scheme.{0}} (a b : T ⟶ N) :
    a ≫ m=b ≫ m ↔ a ≫ k ≫ n=b ≫ k ≫ n := by
  rw [(ContactNowhereZeroTargetCoverRebuild318.cartesian R c L).w,
    ←Category.assoc,←Category.assoc]
  exact (cancel_mono V.ι).symm
include R c L in
/-- The literal Cech pair over the target open gives the SAME original
normalization relation, including nonreduced source tests. -/
lemma cech_original :
    pullback.fst m m ≫ k ≫ n=pullback.snd m m ≫ k ≫ n :=
  (same_fiber R c L _ _).mp (pullback.condition (f := m) (g := m))
end ContactNowhereZeroTargetRelationRebuild318
