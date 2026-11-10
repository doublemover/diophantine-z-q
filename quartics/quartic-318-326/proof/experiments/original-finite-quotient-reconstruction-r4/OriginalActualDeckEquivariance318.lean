module
public import OriginalDeckCurveReconstruction318
public import OriginalCurveActionComparison318
public section
noncomputable section
namespace OriginalActualDeckEquivariance318
open AlgebraicGeometry CategoryTheory
open OriginalNormalClosureGalois318 NormalClosureGeometricPoints318
open OriginalDeckArithmeticLabels318
variable {L : Type} [Field L] [Algebra (RatFunc ℚ) L]
  (ρ : ArithmeticGroup →* (L ≃ₐ[RatFunc ℚ] L)) (hfaithful : Function.Injective ρ)
  (hfixed : ∀ x : L, (∀ w : ArithmeticGroup, ρ w x = x) →
    ∃ r : RatFunc ℚ, algebraMap (RatFunc ℚ) L r = x)
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]
  {Y : Scheme} [IsIntegral Y]
  (j : Spec (CommRingCat.of (Order L)) ⟶ Y) [Mono j]
  (b : ArithmeticGroup → (Y ⟶ Y))
  (hchart : ∀ w, schemeMap L (ρ w) ≫ j = j ≫ b w)
  (g : Spec (CommRingCat.of L) ⟶ Y) (p : Y ⟶ ProjectiveJLine318.scheme ℚ)
  [IsDominant g] [IsIntegralHom p] [IsIso (DominantFunctionField318.map g)]
  (hbase : g ≫ p = ReconstructedFieldNormalization318.base L)
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))
  (hover : ∀ w, b w ≫ p = p)
  (hgeneric : ∀ w, g ≫ b w = Spec.map (CommRingCat.ofHom (ρ w).toRingHom) ≫ g)

include hfaithful hfixed hchart hover hgeneric in
/-- The reconstructed ORIGINAL curve isomorphism now intertwines every
ORIGINAL whole-curve deck map with the existing Contact sign map. This is
proved from the same generic field map and actual schematic-density theorem,
not merely an abstract identification of group labels or dimensions. -/
theorem original_curve (l m : ℂ)
    (hmodels : OriginalPublishedComplexBranches318.ModelInvariants l m)
    (hbranch : OriginalDeckCurveReconstruction318.BranchLocus j b l m) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L,
        ∃ E : Y ≅ ContactProjectiveModel318.model c,
          E.hom ≫ ContactProjectiveModel318.modelMap c = p ∧
          g ≫ E.hom = (ReconstructedFieldNormalization318.specIso L c e).hom ≫
            ContactFieldNormalization318.genericSource c ∧
          (∀ (w : ArithmeticGroup) z, ρ w (e z) = e
            (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
              (FourBinaryCharacters318.signPattern (OriginalContactInertiaBasis318.basis w)) z)) ∧
          ∀ w : ArithmeticGroup, b w ≫ E.hom = E.hom ≫ ContactGlobalSigns318.map c
            (FourBinaryCharacters318.signPattern (OriginalContactInertiaBasis318.basis w)) := by
  obtain ⟨c,e,E,hp,hg,hfield⟩ := OriginalDeckCurveReconstruction318.original_curve
    ρ hfaithful hfixed j b hchart g p hbase V hcover hnormal l m hmodels hbranch
  let E' := OriginalCandidateCurveIso318.iso g p hbase V hcover hnormal c e
  refine ⟨c,e,E',OriginalCandidateCurveIso318.iso_base g p hbase V hcover hnormal c e,
    OriginalCandidateCurveIso318.iso_source g p hbase V hcover hnormal c e,hfield,?_⟩
  intro w
  exact OriginalCurveActionComparison318.original_action c e g p hbase V hcover hnormal
    (ρ w) (FourBinaryCharacters318.signPattern (OriginalContactInertiaBasis318.basis w))
    (hfield w) (b w) (hover w) (hgeneric w)
end OriginalActualDeckEquivariance318
