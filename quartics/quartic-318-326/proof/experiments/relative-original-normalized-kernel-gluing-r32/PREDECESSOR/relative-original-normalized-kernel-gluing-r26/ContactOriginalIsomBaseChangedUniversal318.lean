module
public import ContactOriginalIsomBaseChangeNaturality318
public section
noncomputable section
namespace ContactOriginalIsomBaseChangedUniversal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
open ContactOriginalIsomBaseChangedParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K : Line (curve R c)) {T : Scheme.{0}} (t : T ⟶ Spec R)
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c L K
local notation "P" => parameter R c L K t
local notation "r" => projection R c L K t
@[expose] def universal : ContactWholeIsomNaturality318.Isoms R c L K (r ≫ t) :=
  equivalence R c L K t r ⟨𝟙 P,Category.id_comp _⟩
/-- The new universal object is the LITERAL native pullback of the old
universal full isomorphism along the actual first fiber-product projection. -/
lemma universal_is_original_pullback : universal R c L K t=
    ContactWholeIsomNaturality318.pullIso R c L K q (r ≫ t) (pullback.fst q t)
      pullback.condition (ContactUniversalOriginalIsom318.universal R c L K) := by
  rw [ContactUniversalOriginalIsom318.pullback]
  change ContactWholeIsomPointEquivalence318.equivalence R c L K P (r ≫ t)
      ⟨(𝟙 P) ≫ pullback.fst q t,_⟩=
    ContactWholeIsomPointEquivalence318.equivalence R c L K P (r ≫ t) ⟨pullback.fst q t,_⟩
  congr 1
  apply Subtype.ext
  exact Category.id_comp _
variable {S : Scheme.{0}} (s : S ⟶ T)
lemma pullback (z : Points R c L K t s) :
    ContactOriginalIsomBaseChangeNaturality318.pullIso R c L K t r s z.val z.property
      (universal R c L K t)=equivalence R c L K t s z := by
  have h := ContactOriginalIsomBaseChangeNaturality318.recovery_natural R c L K t r s
    z.val z.property (⟨𝟙 P,Category.id_comp _⟩ : Points R c L K t r)
  have hz : ContactOriginalIsomBaseChangeNaturality318.pointMap R c L K t r s z.val z.property
      (⟨𝟙 P,Category.id_comp _⟩ : Points R c L K t r)=z := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [hz] at h
  exact h
/-- After arbitrary WHOLE coefficient base change, every full original
isomorphism is the unique native pullback of the same pulled universal
object. No new representability datum is supplied as a premise. -/
lemma existsUnique (e : ContactWholeIsomNaturality318.Isoms R c L K (s ≫ t)) :
    ∃! z : Points R c L K t s,
      ContactOriginalIsomBaseChangeNaturality318.pullIso R c L K t r s z.val z.property
        (universal R c L K t)=e := by
  refine ⟨classify R c L K t s e,?_,?_⟩
  · rw [pullback]
    exact (equivalence R c L K t s).apply_symm_apply e
  · intro z hz
    rw [pullback] at hz
    apply (equivalence R c L K t s).injective
    exact hz.trans ((equivalence R c L K t s).apply_symm_apply e).symm
end ContactOriginalIsomBaseChangedUniversal318
