module
public import ContactNowhereZeroSourceOpenRebuild318
public section
noncomputable section
namespace ContactNowhereZeroSourceTestsRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "N" => ContactArbitraryNowhereZeroOpen318.scheme R c L
local notation "S" => ContactOriginalGlobalKernelNormalizationRebuild318.source R c L
local notation "q" => ContactOriginalGlobalKernelNormalizationRebuild318.original R c L
local notation "i" => ContactNowhereZeroSourceOpenRebuild318.inclusion R c L
local notation "π" => ContactArbitraryUniversalZero318.projection R c L
/-- On EVERY whole scheme test, the actual open in the kernel source
is characterized by emptiness of the original universal zero scheme. -/
lemma factor_iff {T : Scheme.{0}} (f : T ⟶ S) :
    (∃ a : T ⟶ N, a ≫ i = f) ↔ IsEmpty ↑(pullback π (f ≫ q)) := by
  rw [← ContactArbitraryNowhereZeroOpen318.factor_iff R c L (f ≫ q)]
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨a,by rw [Category.assoc,ContactNowhereZeroSourceOpenRebuild318.original]⟩
  · rintro ⟨a,ha⟩
    refine ⟨a,(cancel_mono q).mp ?_⟩
    rw [Category.assoc,ContactNowhereZeroSourceOpenRebuild318.original]
    exact ha
/-- Both inverse laws on all tests. This represents only the old
nowhere-zero condition INSIDE the kernel source, not the scalar quotient. -/
def points (T : Scheme.{0}) : (T ⟶ N) ≃
    {f : T ⟶ S // IsEmpty ↑(pullback π (f ≫ q))} where
  toFun a := ⟨a ≫ i,(factor_iff R c L _).mp ⟨a,rfl⟩⟩
  invFun f := Classical.choose ((factor_iff R c L f.val).mpr f.property)
  left_inv a := (cancel_mono i).mp (Classical.choose_spec
    ((factor_iff R c L (a ≫ i)).mpr ((factor_iff R c L _).mp ⟨a,rfl⟩)))
  right_inv f := Subtype.ext (Classical.choose_spec ((factor_iff R c L f.val).mpr f.property))
lemma natural {T U : Scheme.{0}} (a : T ⟶ N) (b : U ⟶ T) :
    (points R c L U (b ≫ a)).val = b ≫ (points R c L T a).val := Category.assoc _ _ _
end ContactNowhereZeroSourceTestsRebuild318
