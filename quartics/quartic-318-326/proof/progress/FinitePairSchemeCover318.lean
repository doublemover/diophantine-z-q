module
public import FinitePairCover318
public import InfinityAdditionScheme318
public import TangentOpenScheme318
public section
noncomputable section
namespace FinitePairSchemeCover318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RelativeChordAlgebra318 (PairRing)
open FinitePairCover318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

/-- Actual four-localization affine cover of the genuine tensor coordinate scheme. -/
@[expose] def coordinateCover (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    (Spec (CommRingCat.of (PairRing A B))).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R:=CommRingCat.of (PairRing A B))
    (chartElement A B) (chart_span_top A B hD)).openCover

/-- The exact same four addition domains cover the actual relative finite-pair product. -/
@[expose] def productCover (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    (RelativeChordScheme318.productScheme A B).OpenCover :=
  (coordinateCover A B hD).pushforwardIso
    (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv

@[simp] theorem productCover_chord (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    (productCover A B hD).f (0 : Fin 4)=RelativeChordScheme318.intoProduct A B := rfl
@[simp] theorem productCover_tangent (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    (productCover A B hD).f (1 : Fin 4)=TangentOpenScheme318.intoProduct A B := rfl
@[simp] theorem productCover_inverse (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    (productCover A B hD).f (2 : Fin 4)=InfinityAdditionScheme318.intoProduct A B false := rfl
@[simp] theorem productCover_twoTorsion (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    (productCover A B hD).f (3 : Fin 4)=InfinityAdditionScheme318.intoProduct A B true := rfl

/-- Unconditional actual four-chart cover for the literal OpenJ coefficients. -/
@[expose] def literalProductCover (N:ℕ) :
    (RelativeChordScheme318.productScheme (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)).OpenCover :=
  productCover _ _ (OpenJAffineScheme318.discriminant_unit N)

end FinitePairSchemeCover318
