module
public import ContactZeroTransportedParameter318
public section
noncomputable section
namespace ContactZeroParameterAmbient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactRelativeCoefficientChange318 ContactZeroCoefficientCharts318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (s : Γ(L.object,⊤))

/-- The parameter Cartesian comparison retains its OTHER projection:
the actual coefficient map of zero schemes, not just the base point. -/
@[reassoc] lemma coefficient : (ContactZeroParameterBaseChange318.iso R S f c L s).hom ≫
    pullback.fst _ _=ContactZeroCoefficientMap318.map R S f c L s :=
  (ContactZeroParameterBaseChange318.square R S f c L s).isoPullback_hom_fst
@[reassoc] lemma ambient : (ContactZeroParameterBaseChange318.iso R S f c L s).hom ≫
    pullback.fst _ _ ≫ ContactGlobalSectionZero318.into R c L s=
    ContactGlobalSectionZero318.into S c (L' R S f c L)
      (pulledSection R S f c L s) ≫ curveMap R S f c := by
  rw [← Category.assoc,coefficient,ContactZeroCoefficientMap318.map_into]

variable (N : Line (curve S c)) (t : Γ(N.object,⊤))
  (e : (L' R S f c L).object ≅ N.object)
  (h : e.hom.app ⊤ (pulledSection R S f c L s)=t)

/-- The specified original line transport leaves the full original
ambient-curve comparison intact. This is required to compare two
zero-family descent arrows by the genuine closed immersion. -/
@[reassoc] lemma transported : (ContactZeroTransportedParameter318.iso R S f c L s N t e h).hom ≫
    pullback.fst _ _ ≫ ContactGlobalSectionZero318.into R c L s=
    ContactGlobalSectionZero318.into S c N t ≫ curveMap R S f c := by
  subst t
  change ((ContactZeroLineIso318.iso S c (L' R S f c L) N e (pulledSection R S f c L s)).hom ≫
    (ContactZeroParameterBaseChange318.iso R S f c L s).hom) ≫ _ = _
  rw [Category.assoc,ambient,← Category.assoc,ContactZeroLineIso318.iso_into]
end ContactZeroParameterAmbient318
