module
public import IntegralRationalFullOverlap318
public import IntegralEveryBranchLocalization318
public import BranchOverlapLocalization318
public import ContactUnbranchedDifferentialFrame318
public section
noncomputable section
namespace IntegralRationalFiniteAtlas318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralSourceBranches318 IntegralOverlapChartMaps318 IntegralAllBranchOverlapMaps318
open IntegralRationalFullOverlap318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c : Fin 4 → ℚˣ)
local instance sourceCommRing : CommRing (SourceOrder ℚ c) := inferInstance
local instance overlapCommRing : CommRing (Overlap ℚ c) := inferInstance
local instance branchCommRing (i : Fin 4) : CommRing (IntegralBranchCoordinates318.B ℚ c i) := inferInstance
local instance originalOpenCommRing : CommRing (ContactKummerOrder318.OpenOrder c) := inferInstance
local instance originalBranchCommRing (i : Fin 4) :
    CommRing (BranchOverlapLocalization318.Branch c i) := inferInstance
local instance sourceOverlapAlgebra : Algebra (SourceOrder ℚ c) (Overlap ℚ c) :=
  IntegralFullOverlapLocalization318.sourceAlgebra ℚ c
local instance originalSourceAlgebra : Algebra (SourceOrder ℚ c) (ContactKummerOrder318.OpenOrder c) :=
  IntegralRationalFullOverlap318.originalAlgebra c

/-- The finite branch denominators and their ambient source presentations
are literally the original labeled rational ones. -/
@[expose] def branchEquiv (i : Fin 4) :
    IntegralBranchCoordinates318.B ℚ c i ≃ₐ[ℚ] BranchOverlapLocalization318.Branch c i := by
  change Localization.Away (SourceDenominatorCover318.denominator c i) ≃ₐ[ℚ]
    Localization.Away (SourceDenominatorCover318.denominator c i)
  exact AlgEquiv.refl

theorem branchEquiv_source (i : Fin 4) (a : SourceOrder ℚ c) :
    branchEquiv c i (algebraMap (SourceOrder ℚ c) (IntegralBranchCoordinates318.B ℚ c i) a) =
      algebraMap (ContactKummerOrder318.SourceOrder c) (BranchOverlapLocalization318.Branch c i)
        (sourceEquiv c a) := rfl

/-- Expose the primitive scalar square before localization extensionality,
so the latter does not unfold nested tensor carrier structures. -/
theorem branch_restriction_on_source (i : Fin 4) (x : SourceOrder ℚ c) :
    overlapEquiv c (branchMap ℚ c i
      (algebraMap (SourceOrder ℚ c) (IntegralBranchCoordinates318.B ℚ c i) x)) =
      BranchOverlapLocalization318.toOpen c i (branchEquiv c i
        (algebraMap (SourceOrder ℚ c) (IntegralBranchCoordinates318.B ℚ c i) x)) := by
  calc
    _ = overlapEquiv c (IntegralOverlapOpenImmersions318.sourceMap ℚ c x) :=
      congrArg (overlapEquiv c) (branchMap_source ℚ c i x)
    _ = SourceOpenFractionField318.orderToOpen c (sourceEquiv c x) := overlapEquiv_source c x
    _ = _ := by
      rw [branchEquiv_source,BranchOverlapLocalization318.toOpen_on_source]

/-- All four transition maps to the full unbranched overlap commute with the
original rational atlas. Equality is checked on the whole localization. -/
theorem branch_restriction (i : Fin 4) (a : IntegralBranchCoordinates318.B ℚ c i) :
    overlapEquiv c (branchMap ℚ c i a) =
      BranchOverlapLocalization318.toOpen c i (branchEquiv c i a) := by
  -- Work with the actual functions, not composites of bundled RingHoms.
  -- The scalar square below is precisely the already-checked primitive
  -- theorem, with no deep carrier/coercion conversion under composition.
  have he : (fun x : IntegralBranchCoordinates318.B ℚ c i =>
      overlapEquiv c (branchMap ℚ c i x)) =
      (fun x : IntegralBranchCoordinates318.B ℚ c i =>
        BranchOverlapLocalization318.toOpen c i (branchEquiv c i x)) := by
    apply IsLocalization.ext
      (R := SourceOrder ℚ c) (S := IntegralBranchCoordinates318.B ℚ c i)
      (P := ContactKummerOrder318.OpenOrder c)
      (Submonoid.powers (IntegralBranchDenominatorCover318.denominator ℚ c i))
      (fun x : IntegralBranchCoordinates318.B ℚ c i => overlapEquiv c (branchMap ℚ c i x))
      (fun x : IntegralBranchCoordinates318.B ℚ c i =>
        BranchOverlapLocalization318.toOpen c i (branchEquiv c i x))
    · simp only [map_one]
    · simp only [map_one]
    · intro x y
      simp only [map_mul]
    · intro x y
      simp only [map_mul]
    · intro x
      -- Normalize the two actual scalar maps inside the native extensionality
      -- goal, rather than unify an entire cached primitive-square theorem
      -- against the inferred localization/target monoid dictionaries.
      simp only [IntegralAllBranchOverlapMaps318.branchMap_source,
        IntegralRationalFullOverlap318.overlapEquiv_source,
        branchEquiv_source,BranchOverlapLocalization318.toOpen_on_source]
  exact congrFun he a

/-- The actual original dt is retained under the overlap comparison. -/
theorem coordinate :
    overlapEquivRat c (IntegralAllBranchOverlapMaps318.t ℚ c) =
      ContactUnbranchedDifferentialFrame318.coordinate c := by
  change overlapEquiv c (IntegralAllBranchOverlapMaps318.polynomialMap ℚ c X) = _
  rw [IntegralAllBranchOverlapMaps318.polynomialMap_apply ℚ c X,
    overlapEquiv_source,AlgEquiv.commutes]
  -- Consume the original opaque coordinate theorem through its own map;
  -- do not unfold the deep OpenBase algebra presentation to compare types.
  change ContactUnbranchedDifferentialFrame318.toOpen c
    (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) X) =
      ContactUnbranchedDifferentialFrame318.coordinate c
  exact ContactUnbranchedDifferentialFrame318.toOpen_coordinate c

theorem differential :
    AlgHomDifferential318.map (overlapEquivRat c).toAlgHom
      (KaehlerDifferential.D ℚ (Overlap ℚ c) (IntegralAllBranchOverlapMaps318.t ℚ c)) =
      KaehlerDifferential.D ℚ (ContactKummerOrder318.OpenOrder c)
        (ContactUnbranchedDifferentialFrame318.coordinate c) := by
  rw [AlgHomDifferential318.map_D]
  change KaehlerDifferential.D ℚ (ContactKummerOrder318.OpenOrder c)
    (overlapEquivRat c (IntegralAllBranchOverlapMaps318.t ℚ c)) = _
  exact congrArg (KaehlerDifferential.D ℚ (ContactKummerOrder318.OpenOrder c)) (coordinate c)

/-- Exact whole-source chart square, including its specified original embedding.
The infinity square is a separate compatibility obligation, not inferred here. -/
theorem finite_square :
    Spec.map (overlapEquiv c).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom (show SourceOrder ℚ c →+* Overlap ℚ c from
        (IntegralOverlapOpenImmersions318.sourceMap ℚ c).toRingHom)) =
    Spec.map (CommRingCat.ofHom (SourceOpenFractionField318.orderToOpen c)) ≫
      Spec.map (sourceEquiv c).toRingEquiv.toCommRingCatIso.hom := by
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact overlapEquiv_source c a
end IntegralRationalFiniteAtlas318
