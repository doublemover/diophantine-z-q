module
public import ContactWholeIsomPullbackLaws318
public section
noncomputable section
namespace ContactUniversalOriginalIsom318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
local notation "P" => ContactGeometricIsomRelationWitness318.parameter R c L K
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c L K
/-- The actual universal full original isomorphism on the SAME concrete
parameter. Its recovered inverse is the proved bijection, not the old
independently constructed isoOfFrame used only as an existence witness. -/
@[expose] def universal : Isoms R c L K q :=
  ContactWholeIsomPointEquivalence318.equivalence R c L K P q ⟨𝟙 P,Category.id_comp q⟩
variable {T : Scheme.{0}} (b : T ⟶ Spec R)
/-- Universal pullback uses literal native module pullback on the actual
base-changed curve. The complete representability square is natural on
EVERY whole coefficient scheme, not just affine or geometric points. -/
lemma pullback (z : Points R c L K b) :
    pullIso R c L K q b z.val z.property (universal R c L K)=
      ContactWholeIsomPointEquivalence318.equivalence R c L K T b z := by
  have h := ContactWholeIsomNaturality318.recovery R c L K q b z.val z.property
    (⟨𝟙 P,Category.id_comp q⟩ : Points R c L K q)
  have hz : pointMap R c L K q b z.val z.property
      (⟨𝟙 P,Category.id_comp q⟩ : Points R c L K q)=z := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [hz] at h
  exact h
/-- Natural represented Isom universal property for this pair of fixed
original lines: every full original family isomorphism is the pullback
of this actual universal isomorphism along ONE unique parameter point.
This is not representability of the varying-line Picard quotient. -/
lemma existsUnique (e : Isoms R c L K b) :
    ∃! z : Points R c L K b,
      pullIso R c L K q b z.val z.property (universal R c L K)=e := by
  simpa only [pullback] using ContactWholeIsomPointEquivalence318.unique_point R c L K T b e
end ContactUniversalOriginalIsom318
