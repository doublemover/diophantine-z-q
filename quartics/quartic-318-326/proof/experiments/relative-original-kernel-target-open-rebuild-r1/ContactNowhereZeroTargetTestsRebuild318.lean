module
public import ContactNowhereZeroTargetCoverRebuild318
public import SchemePullbackHomFiberRebuild318
public section
noncomputable section
namespace ContactNowhereZeroTargetTestsRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "N" => ContactArbitraryNowhereZeroOpen318.scheme R c L
local notation "V" => ContactKernelGlobalTargetOpenRebuild318.locus R c L
local notation "n" => ContactOriginalGlobalKernelNormalizationRebuild318.normalize R c L
local notation "k" => ContactNowhereZeroSourceOpenRebuild318.inclusion R c L
local notation "m" => ContactNowhereZeroTargetNormalizationRebuild318.map R c L
/-- Exact functor-of-points classification for EVERY test scheme. It
consumes the actual Cartesian square and includes non-affine/nonreduced tests. -/
def equivalence (T : Scheme.{0}) : (T ⟶ N) ≃
    SchemePullbackHomFiberRebuild318.Compatible n V.ι T :=
  SchemePullbackHomFiberRebuild318.equivalence (ContactNowhereZeroTargetCoverRebuild318.cartesian R c L) T
lemma natural {T T' : Scheme.{0}} (f : T' ⟶ T) (a : T ⟶ N) :
    equivalence R c L T' (f ≫ a)=
      SchemePullbackHomFiberRebuild318.restrict f (equivalence R c L T a) :=
  SchemePullbackHomFiberRebuild318.natural _ f a
@[reassoc] lemma original (T : Scheme.{0})
    (q : SchemePullbackHomFiberRebuild318.Compatible n V.ι T) :
    (equivalence R c L T).symm q ≫ k=q.val.1 :=
  SchemePullbackHomFiberRebuild318.inverse_first _ T q
@[reassoc] lemma normalized (T : Scheme.{0})
    (q : SchemePullbackHomFiberRebuild318.Compatible n V.ι T) :
    (equivalence R c L T).symm q ≫ m=q.val.2 :=
  SchemePullbackHomFiberRebuild318.inverse_second _ T q
end ContactNowhereZeroTargetTestsRebuild318
