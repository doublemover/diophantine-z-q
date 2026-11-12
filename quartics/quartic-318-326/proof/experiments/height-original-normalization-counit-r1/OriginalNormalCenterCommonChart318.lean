module
public import ActualCommonAffinePoint318
public import OriginalNormalSourceCotangent318
public import EtaleEvaluatedCotangent318
public section
noncomputable section
namespace OriginalNormalCenterCommonChart318
open NumberField CategoryTheory AlgebraicGeometry
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPlaceNormalModel318
open scoped TensorProduct
set_option maxHeartbeats 1200000
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
abbrev centerChart := OriginalNormalCenterAffineChart318.chart c t w D M
abbrev A := (centerChart c t w D M).ring
abbrev B := SourceOpenRing c t w D
@[expose] def pointA : A c t w D M ⟶ CommRingCat.of (K c t) :=
  CommRingCat.ofHom ((algebraMap (V c t w) (K c t)).comp
    (centerChart c t w D M).evaluation.hom)
@[expose] def pointB : CommRingCat.of (B c t w D) ⟶ CommRingCat.of (K c t) :=
  CommRingCat.ofHom M.fieldPoint

/-- The two actual affine charts share the SAME original full scheme
point, so a common affine neighborhood is constructed rather than assumed. -/
theorem exists_common : Nonempty (ActualCommonAffinePoint318.Data
    (centerChart c t w D M).inclusion M.source
    (pointA c t w D M) (pointB c t w D M)) := by
  letI := (centerChart c t w D M).openImmersion
  letI := M.source_open
  exact ActualCommonAffinePoint318.exists_data _ _ _ _
    (OriginalNormalCenterAffineChart318.original_generic c t w D M)

@[expose] def common := Classical.choice (exists_common c t w D M)
abbrev C := (common c t w D M).ring

/-- Derive the open-source base square for THIS Realization from its
actual projective projection, not from a chosen implementation of M. -/
theorem source_over_base : M.source ≫ M.structureMap =
    Spec.map (CommRingCat.ofHom (algebraMap (V c t w) (B c t w D))) := by
  rw [OriginalAllPlaceNormalModel318.Realization.structureMap,←Category.assoc,
    M.source_projection,Category.assoc,JLineAtlas318.chart_over_base,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  change algebraMap (IntegralDistinctContactOpen318.Base (V c t w)
    (contacts c t w) D.coefficients) (B c t w D)
      (algebraMap (Polynomial (V c t w)) _ (Polynomial.C r)) = _
  rw [IntegralReciprocalBase318.finite_C]
  exact (IsScalarTower.algebraMap_apply (V c t w)
    (IntegralDistinctContactOpen318.Base (V c t w) (contacts c t w) D.coefficients)
    (B c t w D) r).symm

theorem scalar_square : (centerChart c t w D M).scalar ≫ (common c t w D M).left =
    CommRingCat.ofHom (algebraMap (V c t w) (B c t w D)) ≫ (common c t w D M).right :=
  (common c t w D M).scalar_square M.structureMap _ _
    (centerChart c t w D M).over_base (source_over_base c t w D M).symm

local instance centerScalar : Algebra (V c t w) (A c t w D M) :=
  (centerChart c t w D M).scalar.hom.toAlgebra
local instance centerEvaluation : Algebra (A c t w D M) (V c t w) :=
  (centerChart c t w D M).evaluation.hom.toAlgebra
local instance centerGenericEvaluation : Algebra (A c t w D M) (K c t) :=
  (pointA c t w D M).hom.toAlgebra
local instance sourceEvaluation : Algebra (B c t w D) (K c t) := M.fieldPoint.toAlgebra
local instance leftAlgebra : Algebra (A c t w D M) (C c t w D M) :=
  (common c t w D M).left.hom.toAlgebra
local instance rightAlgebra : Algebra (B c t w D) (C c t w D M) :=
  (common c t w D M).right.hom.toAlgebra
local instance commonScalar : Algebra (V c t w) (C c t w D M) :=
  ((common c t w D M).left.hom.comp (centerChart c t w D M).scalar.hom).toAlgebra
local instance commonEvaluation : Algebra (C c t w D M) (K c t) :=
  (common c t w D M).evaluation.hom.toAlgebra
local instance centerScalarTower : IsScalarTower (V c t w) (A c t w D M) (C c t w D M) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
local instance sourceScalarTower : IsScalarTower (V c t w) (B c t w D) (C c t w D M) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact congrArg (fun f => f.hom r) (scalar_square c t w D M)
local instance centerPointTower : IsScalarTower (A c t w D M) (C c t w D M) (K c t) :=
  IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun f => f.hom x) (common c t w D M).left_point).symm)
local instance sourcePointTower : IsScalarTower (B c t w D) (C c t w D M) (K c t) :=
  IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun f => f.hom x) (common c t w D M).right_point).symm)
local instance centerIntegralPointTower : IsScalarTower (A c t w D M) (V c t w) (K c t) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
local instance leftEtale : Algebra.Etale (A c t w D M) (C c t w D M) :=
  RingHom.etale_algebraMap.mp (common c t w D M).left_etale
local instance rightEtale : Algebra.Etale (B c t w D) (C c t w D M) :=
  RingHom.etale_algebraMap.mp (common c t w D M).right_etale

/-- The actual center chart and actual original source now have
canonically compared evaluated cotangent fibers through their actual
common affine neighborhood. No rank or frame on the center is assumed. -/
@[expose] def comparison :
    K c t ⊗[A c t w D M] KaehlerDifferential (V c t w) (A c t w D M) ≃ₗ[K c t]
      OriginalNormalSourceCotangent318.Fiber c t w D M :=
  EtaleEvaluatedCotangent318.comparison (V c t w) (A c t w D M) (C c t w D M)
    (K c t) (B c t w D)

/-- Collapse precisely the original integral evaluation followed by
fraction-field extension; this retains its original scalar structures. -/
@[expose] def collapse :
    OriginalNormalCenterAffineChart318.GenericCotangent c t w D M ≃ₗ[K c t]
      K c t ⊗[A c t w D M] KaehlerDifferential (V c t w) (A c t w D M) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange (A c t w D M) (V c t w)
    (K c t) (K c t) (KaehlerDifferential (V c t w) (A c t w D M))

/-- Genuine comparison from the previous integral-center generic
cotangent module to the existing normalized-source generic module. -/
@[expose] def genericComparison :
    OriginalNormalCenterAffineChart318.GenericCotangent c t w D M ≃ₗ[K c t]
      OriginalNormalSourceCotangent318.Fiber c t w D M :=
  collapse c t w D M ≪≫ₗ comparison c t w D M

/-- The comparison retains the actual differential of every pair of
functions agreeing on this actual common affine neighborhood. -/
theorem genericComparison_differential (a : A c t w D M) (b : B c t w D)
    (h : (common c t w D M).left.hom a = (common c t w D M).right.hom b) :
    genericComparison c t w D M
      (AffineSectionCotangentImage318.toGeneric (centerChart c t w D M) (K c t)
        (AffineSectionCotangentImage318.differential (centerChart c t w D M) a)) =
      FramedCotangentFiber318.differential (V c t w) (B c t w D) (K c t) b := by
  simp only [genericComparison,LinearEquiv.trans_apply,collapse,
    AffineSectionCotangentImage318.toGeneric,TensorProduct.mk_apply,
    AffineSectionCotangentImage318.differential,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,one_smul]
  exact EtaleEvaluatedCotangent318.comparison_differential
    (V c t w) (A c t w D M) (C c t w D M) (K c t) (B c t w D) a b h
end OriginalNormalCenterCommonChart318
