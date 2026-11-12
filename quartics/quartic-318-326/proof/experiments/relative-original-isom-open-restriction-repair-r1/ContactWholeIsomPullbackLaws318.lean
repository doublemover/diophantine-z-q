module
public import ContactWholeIsomNaturality318
public section
noncomputable section
namespace ContactWholeIsomPullbackLaws318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
variable {T T' T'' : Scheme.{0}}
/-- Identity law of the actual native Isom pullback, detected by the
proved faithful original classifying map, not defined by conjugating a
set bijection. -/
lemma identity (b : T ⟶ Spec R) (hi : (𝟙 T) ≫ b=b) (e : Isoms R c L K b) :
    pullIso R c L K b b (𝟙 T) hi e=e := by
  apply (ContactWholeIsomPointEquivalence318.equivalence R c L K T b).symm.injective
  change ContactGeometricIsomRelationWitness318.pointOfIso R c L K T b _=
    ContactGeometricIsomRelationWitness318.pointOfIso R c L K T b _
  rw [classify]
  apply Subtype.ext
  exact Category.id_comp _
/-- Composition law for the native coefficient pullback on ALL original
full line isomorphisms, including exact arbitrary geometric base arrows. -/
lemma composition (b : T ⟶ Spec R) (b' : T' ⟶ Spec R) (b'' : T'' ⟶ Spec R)
    (h : T' ⟶ T) (h' : T'' ⟶ T') (hh : h ≫ b=b') (hh' : h' ≫ b'=b'')
    (hc : (h' ≫ h) ≫ b=b'') (e : Isoms R c L K b) :
    pullIso R c L K b' b'' h' hh' (pullIso R c L K b b' h hh e)=
      pullIso R c L K b b'' (h' ≫ h) hc e := by
  apply (ContactWholeIsomPointEquivalence318.equivalence R c L K T'' b'').symm.injective
  change ContactGeometricIsomRelationWitness318.pointOfIso R c L K T'' b'' _=
    ContactGeometricIsomRelationWitness318.pointOfIso R c L K T'' b'' _
  rw [classify,classify,classify]
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm
end ContactWholeIsomPullbackLaws318
