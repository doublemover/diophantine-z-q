module
public import ContactZeroTransportedBaseChange318
public import ContactZeroParameterBaseChange318
public section
noncomputable section
namespace ContactZeroTransportedParameter318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactRelativeCoefficientChange318 ContactZeroCoefficientCharts318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (s : Γ(L.object,⊤))
  (N : Line (curve S c)) (t : Γ(N.object,⊤))
  (e : (L' R S f c L).object ≅ N.object)
  (h : e.hom.app ⊤ (pulledSection R S f c L s)=t)

/-- Transported section zeros are the SAME original parameter-basechange
family, with the line associator and section comparison consumed. -/
@[expose] def iso : ContactGlobalSectionZero318.scheme S c N t ≅
    pullback (ContactGlobalResidueFlat318.projection R c L s)
      (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  subst t
  exact ContactZeroLineIso318.iso S c (L' R S f c L) N e (pulledSection R S f c L s) ≪≫
    ContactZeroParameterBaseChange318.iso R S f c L s

@[reassoc] lemma iso_projection : (iso R S f c L s N t e h).hom ≫ pullback.snd _ _=
    ContactGlobalResidueFlat318.projection S c N t := by
  subst t
  change ((ContactZeroLineIso318.iso S c (L' R S f c L) N e (pulledSection R S f c L s)).hom ≫
    (ContactZeroParameterBaseChange318.iso R S f c L s).hom) ≫ pullback.snd _ _=_
  rw [Category.assoc,ContactZeroParameterBaseChange318.iso_projection]
  unfold ContactGlobalResidueFlat318.projection
  rw [← Category.assoc,ContactZeroLineIso318.iso_into]
end ContactZeroTransportedParameter318
