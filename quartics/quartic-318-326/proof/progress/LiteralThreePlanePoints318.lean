module
public import LiteralThreeBaseEvaluation318
public section
noncomputable section
namespace LiteralThreePlanePoints318
open Polynomial OpenJModel318 OpenJAffineScheme318 ArithmeticPointTopology318
open ModularCoordinateProper318 ModularArithmeticCoordinates318 LiteralThreeBaseEvaluation318
set_option maxHeartbeats 0

/-- The literal plane locus, with its existing subspace topology. -/
abbrev Plane := {p : JOpen × ℂ // Q p.1.val p.2=0}

lemma point_base (N : ℕ) [NeZero N] (p : Points N) :
    p.hom.comp (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N))=
      evaluation N (jValue N p) := by
  apply LiteralThreeBaseEvaluation318.hom_ext
  rw [evaluation_j]
  rfl

@[expose] def pointXHom (N : ℕ) [NeZero N] (p : Points N) :
    letI : Algebra (Base N) ℂ := (evaluation N (jValue N p)).toAlgebra
    ThreeTorsionAlgebra318.XRing (A N) (B N) →ₐ[Base N] ℂ := by
  letI : Algebra (Base N) ℂ := (evaluation N (jValue N p)).toAlgebra
  let f : LiteralThreeXComparison318.Fixed N →ₐ[Base N] ℂ :=
    { __ := p.hom
      commutes' := fun r => RingHom.congr_fun (point_base N p) r }
  exact f.comp (ThreeTorsionSignQuotient318.signQuotientEquiv
    (A N) (B N) (discriminant_unit N)).toAlgHom

lemma pointXHom_root (N : ℕ) [NeZero N] (p : Points N) :
    pointXHom N p (AdjoinRoot.root (ShortThreeTorsion318.polynomial (A N) (B N)))=
      p.hom (xGenerator N) := rfl

/-- Every actual fixed-algebra point satisfies the literal cleared quartic. -/
lemma point_equation (N : ℕ) [NeZero N] (p : Points N) :
    Q (jValue N p).val (p.hom (xGenerator N))=0 := by
  letI : Algebra (Base N) ℂ := (evaluation N (jValue N p)).toAlgebra
  have h := (ThreeXAlgebraPoints318.toRoot (A N) (B N) (pointXHom N p)).property
  change (ThreeTorsionIdentity318.divisionPolynomial
    (evaluation N (jValue N p) (A N)) (evaluation N (jValue N p) (B N))).eval
      (p.hom (xGenerator N))=0 at h
  exact (division_zero_iff N (jValue N p) _).mp h

@[expose] def toPlane (N : ℕ) [NeZero N] (p : Points N) : Plane :=
  ⟨pointCoordinates N p,point_equation N p⟩

@[expose] def fromPlaneAlgHom (N : ℕ) [NeZero N] (p : Plane) :
    letI : Algebra (Base N) ℂ := (evaluation N p.val.1).toAlgebra
    LiteralThreeXComparison318.Fixed N →ₐ[Base N] ℂ := by
  letI : Algebra (Base N) ℂ := (evaluation N p.val.1).toAlgebra
  let x : ThreeRootScaling318.Roots (algebraMap (Base N) ℂ (A N))
      (algebraMap (Base N) ℂ (B N)) :=
    ⟨p.val.2,(division_zero_iff N p.val.1 p.val.2).mpr p.property⟩
  exact (ThreeXAlgebraPoints318.toHom (A N) (B N) x).comp
    (ThreeTorsionSignQuotient318.signQuotientEquiv
      (A N) (B N) (discriminant_unit N)).symm.toAlgHom

/-- The inverse map is built by the actual localization and root universal
properties, not selected from a point count or analytic surjectivity. -/
@[expose] def fromPlane (N : ℕ) [NeZero N] (p : Plane) : Points N := by
  letI : Algebra (Base N) ℂ := (evaluation N p.val.1).toAlgebra
  exact ⟨(fromPlaneAlgHom N p).toRingHom⟩

lemma fromPlane_base (N : ℕ) [NeZero N] (p : Plane) (r : Base N) :
    (fromPlane N p).hom (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) r)=
      evaluation N p.val.1 r := by
  letI : Algebra (Base N) ℂ := (evaluation N p.val.1).toAlgebra
  exact (fromPlaneAlgHom N p).commutes r

lemma fromPlane_x (N : ℕ) [NeZero N] (p : Plane) :
    (fromPlane N p).hom (xGenerator N)=p.val.2 := by
  letI : Algebra (Base N) ℂ := (evaluation N p.val.1).toAlgebra
  change (ThreeXAlgebraPoints318.toHom (A N) (B N) _)
    ((ThreeTorsionSignQuotient318.signQuotientEquiv
      (A N) (B N) (discriminant_unit N)).symm
      ((ThreeTorsionSignQuotient318.signQuotientEquiv
        (A N) (B N) (discriminant_unit N)) _))=p.val.2
  rw [AlgEquiv.symm_apply_apply]
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

lemma fromPlane_coordinates (N : ℕ) [NeZero N] (p : Plane) :
    pointCoordinates N (fromPlane N p)=p.val := by
  apply Prod.ext
  · apply Subtype.ext
    change (fromPlane N p).hom
      (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) (jCoord N))=p.val.1.val
    rw [fromPlane_base,evaluation_j]
  · exact fromPlane_x N p

/-- The actual j,x map is a bijection with the literal quartic plane locus. -/
@[expose] def pointEquiv (N : ℕ) [NeZero N] : Points N ≃ Plane where
  toFun := toPlane N
  invFun := fromPlane N
  left_inv p := by
    apply pointCoordinates_injective N
    exact fromPlane_coordinates N (toPlane N p)
  right_inv p := by
    apply Subtype.ext
    exact fromPlane_coordinates N p

lemma toPlane_continuous (N : ℕ) [NeZero N] : Continuous (toPlane N) :=
  (pointCoordinates_embedding N).continuous.subtype_mk _

lemma fromPlane_continuous (N : ℕ) [NeZero N] : Continuous (fromPlane N) := by
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def,fromPlane_coordinates] using
    (continuous_subtype_val : Continuous (fun p : Plane => p.val))

/-- This is the actual coordinate topology on both sides, with explicit
forward and inverse algebra maps. No analytification is assumed. -/
@[expose] def pointHomeomorph (N : ℕ) [NeZero N] : Points N ≃ₜ Plane where
  toEquiv := pointEquiv N
  continuous_toFun := toPlane_continuous N
  continuous_invFun := fromPlane_continuous N

end LiteralThreePlanePoints318
