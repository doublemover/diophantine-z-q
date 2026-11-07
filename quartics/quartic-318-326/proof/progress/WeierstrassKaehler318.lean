module
public import JacobianKaehlerFrame318
public import InfinityChart318
public import ShortAffineJacobian318
public import OpenJAffineScheme318
public section
noncomputable section
namespace WeierstrassKaehler318
open Algebra KaehlerDifferential
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

abbrev AffineChart (A B : R) (i : Fin 2) :=
  Localization.Away (ShortAffineJacobian318.presentation A B i).jacobian

/-- Explicit differential frame on either actual affine Jacobian chart. -/
@[expose] def affineFrame (A B : R) (i : Fin 2) :
    KaehlerDifferential R (AffineChart A B i) ≃ₗ[AffineChart A B i] AffineChart A B i :=
  JacobianKaehlerFrame318.frame (ShortAffineJacobian318.presentation A B i)

theorem affineFrame_dx (A B : R) :
    affineFrame A B 1 (D R (AffineChart A B 1)
      (algebraMap (ShortAffineJacobian318.Ring A B) (AffineChart A B 1)
        (ShortAffineJacobian318.x A B))) = 1 := by
  exact JacobianKaehlerFrame318.frame_differential (ShortAffineJacobian318.presentation A B 1)

theorem affineFrame_dy (A B : R) :
    affineFrame A B 0 (D R (AffineChart A B 0)
      (algebraMap (ShortAffineJacobian318.Ring A B) (AffineChart A B 0)
        (ShortAffineJacobian318.y A B))) = 1 := by
  exact JacobianKaehlerFrame318.frame_differential (ShortAffineJacobian318.presentation A B 0)

theorem affine_dx_generates (A B : R) :
    Submodule.span (AffineChart A B 1)
      (Set.singleton (D R (AffineChart A B 1)
        (algebraMap (ShortAffineJacobian318.Ring A B) (AffineChart A B 1)
          (ShortAffineJacobian318.x A B))) : Set (KaehlerDifferential R (AffineChart A B 1))) = ⊤ :=
  JacobianKaehlerFrame318.differential_generates (ShortAffineJacobian318.presentation A B 1)

theorem affine_dy_generates (A B : R) :
    Submodule.span (AffineChart A B 0)
      (Set.singleton (D R (AffineChart A B 0)
        (algebraMap (ShortAffineJacobian318.Ring A B) (AffineChart A B 0)
          (ShortAffineJacobian318.y A B))) : Set (KaehlerDifferential R (AffineChart A B 0))) = ⊤ :=
  JacobianKaehlerFrame318.differential_generates (ShortAffineJacobian318.presentation A B 0)

/-- The same actual construction at the infinity Jacobian chart. -/
@[expose] def infinityFrame (A B : R) :
    KaehlerDifferential R (InfinityChart318.SmoothRing A B) ≃ₗ[InfinityChart318.SmoothRing A B]
      InfinityChart318.SmoothRing A B :=
  JacobianKaehlerFrame318.frame (InfinityChart318.presentation A B)

theorem infinityFrame_dx (A B : R) :
    infinityFrame A B (D R (InfinityChart318.SmoothRing A B)
      (algebraMap (InfinityChart318.Ring A B) (InfinityChart318.SmoothRing A B)
        (InfinityChart318.x A B))) = 1 :=
  JacobianKaehlerFrame318.frame_differential (InfinityChart318.presentation A B)

theorem infinity_dx_generates (A B : R) :
    Submodule.span (InfinityChart318.SmoothRing A B)
      (Set.singleton (D R (InfinityChart318.SmoothRing A B)
        (algebraMap (InfinityChart318.Ring A B) (InfinityChart318.SmoothRing A B)
          (InfinityChart318.x A B))) : Set (KaehlerDifferential R (InfinityChart318.SmoothRing A B))) = ⊤ :=
  JacobianKaehlerFrame318.differential_generates (InfinityChart318.presentation A B)

/-- Dual derivations are actual universal relative derivations on these integral rings. -/
@[expose] def affineDerivation (A B : R) (i : Fin 2) :
    Derivation R (AffineChart A B i) (AffineChart A B i) :=
  KaehlerDifferential.linearMapEquivDerivation R (AffineChart A B i) (affineFrame A B i).toLinearMap

@[expose] def infinityDerivation (A B : R) :
    Derivation R (InfinityChart318.SmoothRing A B) (InfinityChart318.SmoothRing A B) :=
  KaehlerDifferential.linearMapEquivDerivation R (InfinityChart318.SmoothRing A B)
    (infinityFrame A B).toLinearMap

theorem affineDerivation_x (A B : R) :
    affineDerivation A B 1 (algebraMap (ShortAffineJacobian318.Ring A B) (AffineChart A B 1)
      (ShortAffineJacobian318.x A B)) = 1 := affineFrame_dx A B

theorem affineDerivation_y (A B : R) :
    affineDerivation A B 0 (algebraMap (ShortAffineJacobian318.Ring A B) (AffineChart A B 0)
      (ShortAffineJacobian318.y A B)) = 1 := affineFrame_dy A B

theorem infinityDerivation_x (A B : R) :
    infinityDerivation A B (algebraMap (InfinityChart318.Ring A B) (InfinityChart318.SmoothRing A B)
      (InfinityChart318.x A B)) = 1 := infinityFrame_dx A B

/-- The integral literal open-j family has these actual frames without any rank or basis premise. -/
@[expose] def literalAffineFrame (N : ℕ) (i : Fin 2) :=
  affineFrame (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) i
@[expose] def literalInfinityFrame (N : ℕ) :=
  infinityFrame (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)

end WeierstrassKaehler318
