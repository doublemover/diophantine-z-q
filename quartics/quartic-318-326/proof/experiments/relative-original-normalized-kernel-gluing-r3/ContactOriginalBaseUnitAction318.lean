module
public import ContactOriginalBaseUnitNaturality318
public section
noncomputable section
namespace ContactOriginalBaseUnitAction318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K : Line (curve R c)) {T : Scheme.{0}} (b : T ⟶ Spec R)
@[expose] def action (a : Γ(T,⊤)ˣ) (z : Points R c L K b) : Points R c L K b :=
  ContactOriginalIsomPointOperations318.composition R c L L K b
    ((ContactOriginalBaseUnitAutomorphisms318.equivalence R c L b).symm a) z
/-- The previously produced literal geometric shear now uses BASE
units, through the proved original structural-functions equivalence. -/
@[expose] def shear : (Γ(T,⊤)ˣ × Points R c L K b) ≃
    (Points R c L K b × Points R c L K b) :=
  (Equiv.prodCongr (ContactOriginalBaseUnitAutomorphisms318.equivalence R c L b).symm (Equiv.refl _)).trans
    (ContactOriginalIsomPointTorsor318.shear R c L K b)
lemma shear_apply (a : Γ(T,⊤)ˣ) (z : Points R c L K b) :
    shear R c L K b (a,z)=(action R c L K b a z,z) := rfl
lemma exists_unique (z w : Points R c L K b) : ∃! a : Γ(T,⊤)ˣ,action R c L K b a w=z := by
  let aw := (shear R c L K b).symm (z,w)
  have hh := (shear R c L K b).apply_symm_apply (z,w)
  have hw : aw.2=w := congrArg Prod.snd hh
  refine ⟨aw.1,?_,?_⟩
  · have ha := congrArg Prod.fst hh
    change action R c L K b aw.1 aw.2=z at ha
    simpa only [hw] using ha
  · intro a ha
    have he : shear R c L K b (a,w)=shear R c L K b aw := by
      rw [shear_apply,ha]
      exact hh.symm
    exact congrArg Prod.fst ((shear R c L K b).injective he)
variable {T' : Scheme.{0}} (b' : T' ⟶ Spec R) (h : T' ⟶ T) (hh : h ≫ b=b')
lemma natural (a : Γ(T,⊤)ˣ) (z : Points R c L K b) :
    pointMap R c L K b b' h hh (action R c L K b a z)=
    action R c L K b' (Units.map h.appTop.hom.toMonoidHom a) (pointMap R c L K b b' h hh z) := by
  unfold action
  rw [ContactOriginalIsomOperationsNaturality318.composition,
    ContactOriginalBaseUnitNaturality318.classify_natural]
end ContactOriginalBaseUnitAction318
