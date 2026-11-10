module
public import OriginalCanonicalAffineReconstruction318
public section
noncomputable section
namespace OriginalSchemeBranchReconstruction318
open AlgebraicGeometry CategoryTheory
open OriginalDeckArithmeticLabels318 OriginalNormalClosureGalois318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y]
  (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsIntegralHom p] [IsDominant p]
  (b : ArithmeticGroup → (Y ≅ Y))

@[expose] def basePoint (z : ℂ) : Spec (CommRingCat.of ℂ) ⟶ ProjectiveJLine318.scheme ℚ :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) z)) ≫
    JLineAtlas318.chart ℚ 1

/-- The geometric input now concerns ALL actual complex Scheme points
of the original curve over each literal finite-coordinate base point. It
mentions no normal-closure ring or selected affine presentation. -/
@[expose] def BranchLaw (l m : ℂ) : Prop :=
  ∀ (z : ℂ) (q : Spec (CommRingCat.of ℂ) ⟶ Y), q ≫ p = basePoint z →
    ((∀ k, z ≠ OriginalPublishedComplexBranches318.branchValues l m k) ∧
      ∀ w : ArithmeticGroup, q ≫ (b w).hom = q ↔ w = 1) ∨
    ∃ k : Fin 4,
      z = OriginalPublishedComplexBranches318.branchValues l m k ∧
      ∀ w : ArithmeticGroup, q ≫ (b w).hom = q ↔
        w = 1 ∨ w = Multiplicative.ofAdd
          (InertiaLabels318.labels (OriginalContactInertiaBasis318.reverse k))

lemma polynomial_map (r : Polynomial ℚ →+* ℂ) :
    r = Polynomial.eval₂RingHom (algebraMap ℚ ℂ) (r Polynomial.X) := by
  apply Polynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · change r Polynomial.X = Polynomial.eval₂ (algebraMap ℚ ℂ) (r Polynomial.X) Polynomial.X
    exact Polynomial.eval₂_X.symm

lemma point_over (r : OriginalCanonicalAffineChart318.Ring p →+* ℂ) :
    (Spec.map (CommRingCat.ofHom r) ≫ OriginalCanonicalAffineChart318.chart p) ≫ p =
      basePoint (r (OriginalCanonicalAffineChart318.coefficient p Polynomial.X)) := by
  calc
    _ = Spec.map (CommRingCat.ofHom r) ≫
        (Spec.map (CommRingCat.ofHom (OriginalCanonicalAffineChart318.coefficient p)) ≫
          JLineAtlas318.chart ℚ 1) := by
      rw [Category.assoc, ← (OriginalCanonicalAffineChart318.square p).w]
    _ = Spec.map (CommRingCat.ofHom (r.comp (OriginalCanonicalAffineChart318.coefficient p))) ≫
        JLineAtlas318.chart ℚ 1 := by
      rw [← Spec.map_comp_assoc]
      all_goals rfl
    _ = _ := by rw [polynomial_map] <;> rfl

lemma canonical_branch (l m : ℂ) (h : BranchLaw p b l m) :
    OriginalCartesianCurveReconstruction318.BranchLocus b
      (OriginalCanonicalAffineChart318.chart p) (OriginalCanonicalAffineChart318.coefficient p) l m := by
  intro r
  exact h (r (OriginalCanonicalAffineChart318.coefficient p Polynomial.X))
    (Spec.map (CommRingCat.ofHom r) ≫ OriginalCanonicalAffineChart318.chart p) (point_over p r)

local instance baseIntegral : IsIntegral (ProjectiveJLine318.scheme ℚ) :=
  OriginalProjectiveBaseIntegral318.integral p
variable
  (bone : (b 1).hom = 𝟙 Y)
  (bmul : ∀ v w, (b (v*w)).hom = (b v).hom ≫ (b w).hom)
  (hover : ∀ w, (b w).hom ≫ p = p)
  (hb : Function.Injective (fun w => (b w).hom))
  (hfixed : ∀ x : Y.functionField,
    (∀ w, OriginalSchemeDeckFieldAction318.ringEquiv b w x = x) →
      ∃ r : RatFunc ℚ, (DominantFunctionField318.map p).hom (OriginalProjectiveFunctionCoordinate318.κ r) = x)
local instance actualBase : Algebra (RatFunc ℚ) Y.functionField :=
  OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ
variable {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include bone bmul hover hb hfixed hcover hnormal in
/-- Whole-curve reconstruction consumes the old quotient, old deck action,
old normal geometry and full original Scheme-point branch law. Every
intermediate affine/field/coordinate compatibility is constructed. -/
theorem original_curve (l m : ℂ)
    (hmodels : OriginalPublishedComplexBranches318.ModelInvariants l m)
    (hbranch : BranchLaw p b l m) :
    (OriginalGenericStalkNaturality318.generic Y ≫ p =
      ReconstructedFieldNormalization318.base Y.functionField) ∧
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] Y.functionField,
        ∃ E : Y ≅ ContactProjectiveModel318.model c,
          E.hom ≫ ContactProjectiveModel318.modelMap c = p ∧
          OriginalGenericStalkNaturality318.generic Y ≫ E.hom =
            (ReconstructedFieldNormalization318.specIso Y.functionField c e).hom ≫
              ContactFieldNormalization318.genericSource c ∧
          (∀ (w : ArithmeticGroup) z,
            OriginalSchemeDeckFieldAction318.ringEquiv b w (e z) = e
              (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
                (FourBinaryCharacters318.signPattern (OriginalContactInertiaBasis318.basis w)) z)) ∧
          ∀ w : ArithmeticGroup, (b w).hom ≫ E.hom = E.hom ≫ ContactGlobalSigns318.map c
            (FourBinaryCharacters318.signPattern (OriginalContactInertiaBasis318.basis w)) := by
  exact OriginalCanonicalAffineReconstruction318.original_curve p b bone bmul hover hb hfixed
    V hcover hnormal l m hmodels (canonical_branch p b l m hbranch)
end OriginalSchemeBranchReconstruction318
