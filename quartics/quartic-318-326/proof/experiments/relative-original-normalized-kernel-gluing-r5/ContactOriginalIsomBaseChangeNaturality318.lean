module
public import ContactOriginalIsomBaseChangedParameter318
public section
noncomputable section
namespace ContactOriginalIsomBaseChangeNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
open ContactOriginalIsomBaseChangedParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K : Line (curve R c)) {T S S' : Scheme.{0}} (t : T ⟶ Spec R)
  (s : S ⟶ T) (s' : S' ⟶ T) (h : S' ⟶ S) (hh : h ≫ s=s')
lemma coefficient : h ≫ (s ≫ t)=s' ≫ t := by rw [←Category.assoc,hh]
@[expose] def pointMap (z : Points R c L K t s) : Points R c L K t s' :=
  ⟨h ≫ z.val,by rw [Category.assoc,z.property,hh]⟩
@[expose] def pullIso (e : ContactWholeIsomNaturality318.Isoms R c L K (s ≫ t)) :
    ContactWholeIsomNaturality318.Isoms R c L K (s' ≫ t) :=
  ContactWholeIsomNaturality318.pullIso R c L K (s ≫ t) (s' ≫ t) h (coefficient t s s' h hh) e
/-- The pulled-back scheme classifier is natural for the SAME native
full-module pullback, over every arrow of the arbitrary new base. -/
lemma classify_natural (e : ContactWholeIsomNaturality318.Isoms R c L K (s ≫ t)) :
    classify R c L K t s' (pullIso R c L K t s s' h hh e)=
      pointMap R c L K t s s' h hh (classify R c L K t s e) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [classify_fst]
    change _=(h ≫ (classify R c L K t s e).val) ≫ _
    rw [Category.assoc,classify_fst]
    exact congrArg Subtype.val (ContactWholeIsomNaturality318.classify R c L K
      (s ≫ t) (s' ≫ t) h (coefficient t s s' h hh) e)
  · rw [classify_snd]
    change s'=(h ≫ (classify R c L K t s e).val) ≫ _
    rw [Category.assoc,classify_snd,hh]
lemma recovery_natural (z : Points R c L K t s) :
    pullIso R c L K t s s' h hh (equivalence R c L K t s z)=
      equivalence R c L K t s' (pointMap R c L K t s s' h hh z) := by
  apply (equivalence R c L K t s').symm.injective
  change classify R c L K t s' _=classify R c L K t s' _
  rw [classify_natural]
  simp only [classify,Equiv.symm_apply_apply]
end ContactOriginalIsomBaseChangeNaturality318
