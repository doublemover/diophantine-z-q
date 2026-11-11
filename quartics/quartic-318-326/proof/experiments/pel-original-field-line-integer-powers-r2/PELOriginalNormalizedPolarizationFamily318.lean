module
public import PELOriginalPolarizationBicharacter318
public section
noncomputable section
namespace PELOriginalNormalizedPolarizationFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalSchemePointGroup318 PELOriginalCubeTestClasses318
open PELOriginalPolarizationBicharacter318 PELOriginalAlgebraicPolarizationLine318
variable (τ : ℂ) (hτ : 0 < τ.im)
@[expose] def firstPoint : Points τ hτ (Product τ hτ) (baseMap τ hτ) :=
  ⟨pullback.fst _ _,rfl⟩
@[expose] def secondPoint : Points τ hτ (Product τ hτ) (baseMap τ hτ) :=
  ⟨pullback.snd _ _,pullback.condition.symm⟩

/-- The SAME literal normalized product line with its zero-map factor.
It is defined on the WHOLE original scheme product, not separately on
complex fibers or by specifying only a line-class-valued pairing. -/
@[expose] def family : Line (Product τ hτ) :=
  normalizedLine τ hτ (baseMap τ hτ) (firstPoint τ hτ) (secondPoint τ hτ)

lemma value_pull {Y Z : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    {σ : Z ⟶ Spec (CommRingCat.of ℂ)} (f : Z ⟶ Y) (hf : f≫ρ=σ)
    (a : Points τ hτ Y ρ) :
    LineClassPullbackHom318.pullback f (value τ hτ ρ a)=
      value τ hτ σ (pull τ hτ ρ f hf a) :=
  (LineClassPullbackLaws318.pullback_composition f a.val (classOf (line τ hτ))).symm
lemma pairing_pull {Y Z : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    {σ : Z ⟶ Spec (CommRingCat.of ℂ)} (f : Z ⟶ Y) (hf : f≫ρ=σ)
    (a b : Points τ hτ Y ρ) :
    LineClassPullbackHom318.pullback f (pairing τ hτ ρ a b)=
      pairing τ hτ σ (pull τ hτ ρ f hf a) (pull τ hτ ρ f hf b) := by
  simp only [pairing,map_mul,map_inv,value_pull,map_add,map_zero]

@[expose] def pairMap {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (a b : Points τ hτ Y ρ) : Y ⟶ Product τ hτ :=
  pullback.lift a.val b.val (a.property.trans b.property.symm)
lemma pairMap_over {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (a b : Points τ hτ Y ρ) : pairMap τ hτ ρ a b≫baseMap τ hτ=ρ := by
  rw [baseMap,←Category.assoc,pairMap,pullback.lift_fst,a.property]
lemma pull_first {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (a b : Points τ hτ Y ρ) :
    pull τ hτ (baseMap τ hτ) (pairMap τ hτ ρ a b) (pairMap_over τ hτ ρ a b)
      (firstPoint τ hτ)=a := by
  apply Subtype.ext
  exact pullback.lift_fst _ _ _
lemma pull_second {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (a b : Points τ hτ Y ρ) :
    pull τ hτ (baseMap τ hτ) (pairMap τ hτ ρ a b) (pairMap_over τ hτ ρ a b)
      (secondPoint τ hτ)=b := by
  apply Subtype.ext
  exact pullback.lift_snd _ _ _
lemma pair_class {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (a b : Points τ hτ Y ρ) :
    classOf (LineSheafPullback318.line (pairMap τ hτ ρ a b) (family τ hτ))=
      pairing τ hτ ρ a b := by
  change LineClassPullbackHom318.pullback (pairMap τ hτ ρ a b)
    (classOf (normalizedLine τ hτ (baseMap τ hτ) (firstPoint τ hτ) (secondPoint τ hτ)))=_
  rw [normalizedLine_class,pairing_pull τ hτ _ _ (pairMap_over τ hτ ρ a b),pull_first,pull_second]

/-- Full arbitrary-test comparison, retaining the actual pair map and
literal four-factor line. Its two inverse sheaf maps exist on all tests,
including nonreduced tests. -/
@[expose] def testIso {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (a b : Points τ hτ Y ρ) :
    (LineSheafPullback318.line (pairMap τ hτ ρ a b) (family τ hτ)).object ≅
      (normalizedLine τ hτ ρ a b).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [pair_class,normalizedLine_class]

@[expose] def zeroLeftIso {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (a : Points τ hτ Y ρ) :
    (LineSheafPullback318.line (pairMap τ hτ ρ 0 a) (family τ hτ)).object ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  testIso τ hτ ρ 0 a ≪≫ PELOriginalPolarizationBicharacter318.zeroLeftIso τ hτ ρ a
@[expose] def zeroRightIso {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (a : Points τ hτ Y ρ) :
    (LineSheafPullback318.line (pairMap τ hτ ρ a 0) (family τ hτ)).object ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  testIso τ hτ ρ a 0 ≪≫ PELOriginalPolarizationBicharacter318.zeroRightIso τ hτ ρ a

/-- Actual symmetry of the whole product family under the actual swap
map. This assertion is an isomorphism, not an unproved coherent choice. -/
@[expose] def symmetryIso :
    (LineSheafPullback318.line
      (pairMap τ hτ (baseMap τ hτ) (secondPoint τ hτ) (firstPoint τ hτ)) (family τ hτ)).object ≅
      (family τ hτ).object :=
  testIso τ hτ (baseMap τ hτ) (secondPoint τ hτ) (firstPoint τ hτ) ≪≫
    symmetricIso τ hτ (baseMap τ hτ) (secondPoint τ hτ) (firstPoint τ hτ)
end PELOriginalNormalizedPolarizationFamily318
