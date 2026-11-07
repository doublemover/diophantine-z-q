module
public import AffineDifferentialSheaf318
public import WeierstrassKaehler318
public section
noncomputable section
namespace WeierstrassDifferentialSheaf318
open CategoryTheory AlgebraicGeometry KaehlerDifferential
open WeierstrassKaehler318 AffineDifferentialSheaf318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R]

/-- Actual relative differential sheaf on the genuine affine Jacobian chart scheme. -/
@[expose] def affineSheaf (A B : R) (i : Fin 2) :
    (Spec (CommRingCat.of (AffineChart A B i))).Modules :=
  differentialSheaf (R := R) (S := AffineChart A B i)

/-- Actual relative differential sheaf on the genuine infinity Jacobian chart scheme. -/
@[expose] def infinitySheaf (A B : R) :
    (Spec (CommRingCat.of (InfinityChart318.SmoothRing A B))).Modules :=
  differentialSheaf (R := R) (S := InfinityChart318.SmoothRing A B)

/-- An actual O-module sheaf isomorphism, with no supplied sheaf trivialization. -/
@[expose] def affineSheafFrame (A B : R) (i : Fin 2) :
    affineSheaf A B i ≅ SheafOfModules.unit (Spec (CommRingCat.of (AffineChart A B i))).ringCatSheaf :=
  frameIso (affineFrame A B i)

@[expose] def infinitySheafFrame (A B : R) :
    infinitySheaf A B ≅ SheafOfModules.unit
      (Spec (CommRingCat.of (InfinityChart318.SmoothRing A B))).ringCatSheaf :=
  frameIso (infinityFrame A B)

/-- The literal dx section is the normalized generator on D(2y). -/
theorem affine_dx_global (A B : R) :
    (globalFrameIso (affineFrame A B 1)).hom
      (differentialSection (R := R)
        (algebraMap (ShortAffineJacobian318.Ring A B) (AffineChart A B 1)
          (ShortAffineJacobian318.x A B))) = 1 :=
  normalized_differential_section _ _ (affineFrame_dx A B)

/-- The literal dy section is the normalized generator on the other affine chart. -/
theorem affine_dy_global (A B : R) :
    (globalFrameIso (affineFrame A B 0)).hom
      (differentialSection (R := R)
        (algebraMap (ShortAffineJacobian318.Ring A B) (AffineChart A B 0)
          (ShortAffineJacobian318.y A B))) = 1 :=
  normalized_differential_section _ _ (affineFrame_dy A B)

theorem infinity_dx_global (A B : R) :
    (globalFrameIso (infinityFrame A B)).hom
      (differentialSection (R := R)
        (algebraMap (InfinityChart318.Ring A B) (InfinityChart318.SmoothRing A B)
          (InfinityChart318.x A B))) = 1 :=
  normalized_differential_section _ _ (infinityFrame_dx A B)

/-- The literal integral open-j model inherits these actual relative sheaves. -/
@[expose] def literalAffineSheaf (N : ℕ) (i : Fin 2) :=
  affineSheaf (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) i
@[expose] def literalInfinitySheaf (N : ℕ) :=
  infinitySheaf (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)

end WeierstrassDifferentialSheaf318
