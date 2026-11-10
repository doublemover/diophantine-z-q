module
public import ContactZeroLineIso318
public import ContactZeroGeometricBaseChange318
public section
noncomputable section
namespace ContactZeroTransportedBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactRelativeCoefficientChange318 ContactZeroCoefficientCharts318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (s : Γ(L.object,⊤))
  (N : Line (curve S c)) (t : Γ(N.object,⊤))
  (e : (L' R S f c L).object ≅ N.object)
  (h : e.hom.app ⊤ (pulledSection R S f c L s)=t)

/-- Actual zero-scheme basechange followed by a SPECIFIED genuine line
comparison carrying the geometrically pulled section to the target one. -/
@[expose] def iso : ContactGlobalSectionZero318.scheme S c N t ≅
    pullback (curveMap R S f c) (ContactGlobalSectionZero318.into R c L s) := by
  subst t
  exact ContactZeroLineIso318.iso S c (L' R S f c L) N e (pulledSection R S f c L s) ≪≫
    ContactZeroGeometricBaseChange318.baseChangeIso R S f c L s

@[reassoc] lemma iso_fst : (iso R S f c L s N t e h).hom ≫ pullback.fst _ _ =
    ContactGlobalSectionZero318.into S c N t := by
  subst t
  change ((ContactZeroLineIso318.iso S c (L' R S f c L) N e (pulledSection R S f c L s)).hom ≫
    (ContactZeroGeometricBaseChange318.baseChangeIso R S f c L s).hom) ≫ pullback.fst _ _ = _
  rw [Category.assoc,ContactZeroGeometricBaseChange318.baseChangeIso_fst,
    ContactZeroLineIso318.iso_into]
end ContactZeroTransportedBaseChange318
