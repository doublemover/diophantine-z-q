module
public import PELOriginalRosatiPolarizationFamily318
public section
noncomputable section
namespace PELOriginalRosatiTestPairing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 PELPrincipalOrderCoordinates318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318 PELOriginalSchemePointGroup318
open PELOriginalNormalizedPolarizationFamily318 PELOriginalPolarizationBicharacter318
open PELOriginalRosatiPolarizationFamily318 PELOriginalOrderHermitianAdjoint318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
variable {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ)) (x y : Points τ hτ T ρ)
abbrev act := PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ
lemma left_naturality : pairMap τ hτ ρ x y≫leftMap τ hτ a=
    pairMap τ hτ ρ (act τ hτ ρ a x) y := by
  apply pullback.hom_ext
  · simp only [leftMap,pairMap,Category.assoc,pullback.lift_fst]
    change pairMap τ hτ ρ x y≫(pullback.fst _ _≫PELOriginalOrderSchemeMorphism318.morphism τ hτ a)=
      x.val≫PELOriginalOrderSchemeMorphism318.morphism τ hτ a
    rw [←Category.assoc,pairMap,pullback.lift_fst]
  · simp only [leftMap,pairMap,Category.assoc,pullback.lift_snd] <;> rfl
lemma right_naturality : pairMap τ hτ ρ x y≫rightMap τ hτ a=
    pairMap τ hτ ρ x (act τ hτ ρ (adjoint a) y) := by
  apply pullback.hom_ext
  · simp only [rightMap,pairMap,Category.assoc,pullback.lift_fst] <;> rfl
  · simp only [rightMap,pairMap,Category.assoc,pullback.lift_snd]
    change pairMap τ hτ ρ x y≫(pullback.snd _ _≫PELOriginalOrderSchemeMorphism318.morphism τ hτ (adjoint a))=
      y.val≫PELOriginalOrderSchemeMorphism318.morphism τ hτ (adjoint a)
    rw [←Category.assoc,pairMap,pullback.lift_snd]

/-- Exact Rosati adjoint identity in the actual line-class bicharacter
on EVERY scheme test. It is pulled from a whole-product sheaf isomorphism,
not inferred from complex-point evaluations or a represented dual. -/
lemma pairing_adjoint :
    pairing τ hτ ρ (act τ hτ ρ a x) y=pairing τ hτ ρ x (act τ hτ ρ (adjoint a) y) := by
  have he := congrArg (LineClassPullbackHom318.pullback (pairMap τ hτ ρ x y))
    (class_equation τ hτ a)
  change LineClassPullbackHom318.pullback (pairMap τ hτ ρ x y)
      (LineClassPullbackHom318.pullback (leftMap τ hτ a) (classOf (family τ hτ)))=
    LineClassPullbackHom318.pullback (pairMap τ hτ ρ x y)
      (LineClassPullbackHom318.pullback (rightMap τ hτ a) (classOf (family τ hτ))) at he
  rw [←LineClassPullbackLaws318.pullback_composition,←LineClassPullbackLaws318.pullback_composition,
    left_naturality,right_naturality] at he
  exact (pair_class τ hτ ρ (act τ hτ ρ a x) y).symm.trans
    (he.trans (pair_class τ hτ ρ x (act τ hτ ρ (adjoint a) y)))
@[expose] def iso :
    (normalizedLine τ hτ ρ (act τ hτ ρ a x) y).object ≅
      (normalizedLine τ hτ ρ x (act τ hτ ρ (adjoint a) y)).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [normalizedLine_class,normalizedLine_class,pairing_adjoint]
lemma hom_inv : (iso τ hτ a ρ x y).hom≫(iso τ hτ a ρ x y).inv=𝟙 _ :=
  (iso τ hτ a ρ x y).hom_inv_id
lemma inv_hom : (iso τ hτ a ρ x y).inv≫(iso τ hτ a ρ x y).hom=𝟙 _ :=
  (iso τ hτ a ρ x y).inv_hom_id
end PELOriginalRosatiTestPairing318
