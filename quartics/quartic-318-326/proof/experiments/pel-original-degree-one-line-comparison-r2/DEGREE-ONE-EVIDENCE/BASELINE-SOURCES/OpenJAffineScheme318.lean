module
public import ShortAffineScheme318
public section
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace OpenJAffineScheme318
open OpenJModel318
set_option maxHeartbeats 0

@[expose] def A (N : ℕ) : Base N := -3*jCoord N*inverseDenominator N
@[expose] def B (N : ℕ) : Base N := -2*jCoord N*inverseDenominator N
abbrev CoordinateRing (N : ℕ) := ShortAffineJacobian318.Ring (A N) (B N)

lemma actual_discriminant (N : ℕ) :
    -16*(4*(A N)^3+27*(B N)^2)=(integralModel N).Δ := by
  simp only [A,B,integralModel,curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

lemma discriminant_unit (N : ℕ) : IsUnit (-16*(4*(A N)^3+27*(B N)^2)) := by
  rw [actual_discriminant]
  exact (integralModel N).isUnit_Δ

instance coordinateRing_smooth (N : ℕ) : Algebra.Smooth (Base N) (CoordinateRing N) :=
  ShortAffineJacobian318.smooth (A N) (B N) (discriminant_unit N)

/-- The actual affine elliptic-family scheme over the literal open j-line base. -/
@[expose] def affineScheme (N : ℕ) : Scheme := ShortAffineScheme318.scheme (A N) (B N)
@[expose] def baseScheme (N : ℕ) : Scheme := Spec (CommRingCat.of (Base N))
@[expose] def structureMap (N : ℕ) : affineScheme N ⟶ baseScheme N :=
  ShortAffineScheme318.structureMap (A N) (B N)

/-- No smoothness hypothesis remains for the literal family over OpenJModel.Base N. -/
instance structureMap_smooth (N : ℕ) : Smooth (structureMap N) :=
  ShortAffineScheme318.structureMap_smooth (A N) (B N) (discriminant_unit N)

/-- Its actual closed immersion in the affine plane over the same base. -/
@[expose] def embedding (N : ℕ) : affineScheme N ⟶ ShortAffineScheme318.plane (R := Base N) :=
  ShortAffineScheme318.embedding (A N) (B N)

instance embedding_closed (N : ℕ) : IsClosedImmersion (embedding N) :=
  ShortAffineScheme318.embedding_closed (A N) (B N)

/-- The literal equation holds inside the actual coordinate ring. -/
theorem actual_equation (N : ℕ) :
    (ShortAffineJacobian318.y (A N) (B N))^2=
      (ShortAffineJacobian318.x (A N) (B N))^3+
        algebraMap (Base N) (CoordinateRing N) (A N)*ShortAffineJacobian318.x (A N) (B N)+
        algebraMap (Base N) (CoordinateRing N) (B N) := by
  linear_combination ShortAffineJacobian318.relation (A N) (B N)

/-- Every actual base-changed literal coefficient model remains smooth. -/
theorem changed_model_smooth {R : Type*} [CommRing R] (N : ℕ) (φ : Base N →+* R) :
    Smooth (ShortAffineScheme318.structureMap (φ (A N)) (φ (B N))) := by
  apply ShortAffineScheme318.structureMap_smooth
  simpa only [map_neg,map_mul,map_add,map_pow,map_ofNat] using (discriminant_unit N).map φ

end OpenJAffineScheme318
