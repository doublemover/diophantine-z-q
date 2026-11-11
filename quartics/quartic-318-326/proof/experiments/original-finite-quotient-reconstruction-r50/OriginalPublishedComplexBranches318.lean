module
public import ComplexLegendreCoordinates318
public import OriginalComplexPointReconstruction318
public section
noncomputable section
namespace OriginalPublishedComplexBranches318
open AlgebraicGeometry CategoryTheory Polynomial
open OriginalNormalClosureGalois318 NormalClosureGeometricPoints318
variable {L : Type} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]

/-- The actual complex quotient-subset invariants are required; a published
curve name or equality of unrelated elliptic invariants does not supply them. -/
structure ModelInvariants (l m : ℂ) : Prop where
  left_zero : l ≠ 0
  left_one : l ≠ 1
  right_zero : m ≠ 0
  right_one : m ≠ 1
  row30 : ComplexLegendreCoordinates318.legendreJ l =
    (ContactCoordinates318.quarticJ (-43) (-686) (-2915) (-1372) (-172) : ℂ)
  row42 : ComplexLegendreCoordinates318.legendreJ m =
    (ContactCoordinates318.quarticJ (-43) 600 (-986) (-600) (-43) : ℂ)
  row70 : ComplexLegendreCoordinates318.legendreJ (m/l) =
    (ContactCoordinates318.quarticJ (-43) 256 (-130) (-768) (-387) : ℂ)
  row105 : ComplexLegendreCoordinates318.legendreJ ((m-1)/(l-1)) =
    (ContactCoordinates318.quarticJ (-43) 2 505 12 (-1548) : ℂ)

/-- The fixed original coordinate is t=32s; the two uncomputed complex branch
values remain variables until the four actual model invariants determine them. -/
@[expose] def branchValues (l m : ℂ) : Fin 4 → ℂ := ![0,32,32*l,32*m]

lemma values_eq {l m : ℂ} (h : ModelInvariants l m) :
    branchValues l m = fun k => (LinearContactSquareclass318.contacts k : ℂ) := by
  obtain ⟨hl,hm⟩ := ComplexLegendreCoordinates318.coordinates_of_original_models l m
    h.left_zero h.left_one h.right_zero h.right_one h.row30 h.row42 h.row70 h.row105
  subst l
  subst m
  funext k
  fin_cases k <;> norm_num [branchValues,LinearContactSquareclass318.contacts]

lemma contactValue_rat (p : Order L →+* ℂ) (k : Fin 4) :
    contactValue L p k = (LinearContactSquareclass318.contacts k : ℂ) := by
  let f : ℚ →+* ℂ := p.comp ((algebraMap ℚ[X] (Order L)).comp Polynomial.C)
  change f (LinearContactSquareclass318.contacts k) = _
  simpa only [Rat.cast_id] using map_ratCast f (LinearContactSquareclass318.contacts k)

variable {Y : Scheme} (j : Spec (CommRingCat.of (Order L)) ⟶ Y) [Mono j]
  (a : OriginalNormalClosureGalois318.Group L → (Y ⟶ Y))
  (hj : ∀ σ, schemeMap L σ ≫ j = j ≫ a σ)

/-- A complete branch law for the actual original curve with as-yet unknown
complex branch coordinates. Labels, points and original actions stay literal. -/
@[expose] def BranchLocus (labels : OriginalNormalClosureGalois318.Group L ≃* FourBinaryCharacters318.Group)
    (l m : ℂ) : Prop :=
  ∀ p : Order L →+* ℂ,
    ((∀ k, coordinate L p ≠ branchValues l m k) ∧
      ∀ σ : OriginalNormalClosureGalois318.Group L, OriginalCurveGeometricStabilizers318.point j p ≫ a σ =
        OriginalCurveGeometricStabilizers318.point j p ↔ σ = 1) ∨
    ∃ k : Fin 4, coordinate L p = branchValues l m k ∧
      ∀ σ : OriginalNormalClosureGalois318.Group L, OriginalCurveGeometricStabilizers318.point j p ≫ a σ =
        OriginalCurveGeometricStabilizers318.point j p ↔
          σ = 1 ∨ labels σ = FourBinaryCharacters318.flip k

/-- The previously supplied literal contacts are now derived from the four
actual complex quotient invariants. Neither rationality nor the six candidate
cross-ratios is supplied as a hypothesis. -/
theorem normalized_branch_locus (labels : OriginalNormalClosureGalois318.Group L ≃* FourBinaryCharacters318.Group)
    (l m : ℂ) (hmodels : ModelInvariants l m) (hbranch : BranchLocus j a labels l m) :
    OriginalComplexPointReconstruction318.ComplexBranchLocus j a labels := by
  intro p
  have h := hbranch p
  have hv := values_eq hmodels
  simpa only [hv,contactValue_rat] using h

variable [IsIntegral Y]
  (g : Spec (CommRingCat.of L) ⟶ Y) (p : Y ⟶ ProjectiveJLine318.scheme ℚ)
  [IsDominant g] [IsIntegralHom p] [IsIso (DominantFunctionField318.map g)]
  (hbase : g ≫ p = ReconstructedFieldNormalization318.base L)
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include hj hbase hcover hnormal in
/-- Original curve reconstruction with the literal branch values DERIVED
from the genuine published quotient-subset invariant equations over C.
PEL algebraization, the whole original branch law and those equations remain
geometric inputs; no numerical invariant substitutes for their construction. -/
theorem original_curve (labels : OriginalNormalClosureGalois318.Group L ≃* FourBinaryCharacters318.Group)
    (l m : ℂ) (hmodels : ModelInvariants l m) (hbranch : BranchLocus j a labels l m) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L,
        ∃ E : Y ≅ ContactProjectiveModel318.model c,
          E.hom ≫ ContactProjectiveModel318.modelMap c = p ∧
          g ≫ E.hom = (ReconstructedFieldNormalization318.specIso L c e).hom ≫
            ContactFieldNormalization318.genericSource c ∧
          ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
            (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
              (FourBinaryCharacters318.signPattern (labels σ)) z) :=
  OriginalComplexPointReconstruction318.original_curve j a hj g p hbase V hcover hnormal
    labels (normalized_branch_locus j a labels l m hmodels hbranch)
end OriginalPublishedComplexBranches318
