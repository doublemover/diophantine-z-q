module
public import SelectedPrimitiveOrdinateUnit318
public section
noncomputable section
open Polynomial
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318

namespace SelectedPrimitiveTwistPoint318
variable (n : ℕ) (I : Ideal (D n))
variable (τ : (D n ⧸ I) →ₐ[R n] (D n ⧸ I)) (hτ : τ.comp (q n I) = (q n I).comp (sign n))
variable (hY : IsUnit (ybar n I))

include hτ in
theorem y_anti : τ (ybar n I) = -ybar n I := by
  simpa only [AlgHom.comp_apply,ChartNegation318.affineNeg_y,map_neg] using
    DFunLike.congr_fun hτ (SelectedPrimitiveAffineSign318.Y n)

include hτ in
private theorem fix_square_unit : Units.map τ.toMonoidHom (hY.unit^2) = hY.unit^2 := by
  apply Units.ext
  have h : (↑(hY.unit^2) : D n ⧸ I) = (ybar n I)^2 := by
    rw [Units.val_pow_eq_pow_val,hY.unit_spec]
  change τ (↑(hY.unit^2) : D n ⧸ I) = (↑(hY.unit^2) : D n ⧸ I)
  rw [h,map_pow,y_anti n I τ hτ]
  ring

/-- The actual fixed twisting parameter is the square of the primitive
ordinate. Its inverse is fixed as well, not assumed to descend. -/
@[expose] def twistUnit : (fixed n I τ)ˣ where
  val := ⟨(↑(hY.unit^2):(D n ⧸ I)),by exact congrArg (fun u : (D n ⧸ I)ˣ => (u:(D n ⧸ I))) (fix_square_unit n I τ hτ hY)⟩
  inv := ⟨(↑((hY.unit^2)⁻¹):(D n ⧸ I)),by
    have h : Units.map τ.toMonoidHom (hY.unit^2)⁻¹ = (hY.unit^2)⁻¹ := by
      rw [map_inv,fix_square_unit n I τ hτ hY]
    exact congrArg (fun u : (D n ⧸ I)ˣ => (u:(D n ⧸ I))) h⟩
  val_inv := Subtype.ext (Units.mul_inv (hY.unit^2))
  inv_val := Subtype.ext (Units.inv_mul (hY.unit^2))


theorem twistUnit_value : ((fixed n I τ).val ((twistUnit n I τ hτ hY):(fixed n I τ)) : (D n ⧸ I)) = (ybar n I)^2 := by
  change (↑(hY.unit^2):(D n ⧸ I)) = _
  rw [Units.val_pow_eq_pow_val,hY.unit_spec]

@[expose] def fixedX : (fixed n I τ) :=
  ⟨xbar n I,(fixed_iff_polynomial n I τ hτ (xbar n I)).mpr ⟨X,aeval_X _⟩⟩


abbrev twistA := (↑(twistUnit n I τ hτ hY) : ↥(fixed n I τ))^2*algebraMap (R n) (fixed n I τ) (A n)
abbrev twistB := (↑(twistUnit n I τ hτ hY) : ↥(fixed n I τ))^3*algebraMap (R n) (fixed n I τ) (B n)
abbrev markX := (↑(twistUnit n I τ hτ hY) : ↥(fixed n I τ))*(fixedX n I τ hτ)
abbrev markY := (↑(twistUnit n I τ hτ hY) : ↥(fixed n I τ))^2

private theorem discriminant_scale {P S : Type*} [CommRing P] [CommRing S]
    (f : P →+* S) (u : Sˣ) (a b : P)
    (h : IsUnit (-16*(4*a^3+27*b^2))) :
    IsUnit (-16*(4*((u:S)^2*f a)^3+27*((u:S)^3*f b)^2)) := by
  have he : -16*(4*((u:S)^2*f a)^3+27*((u:S)^3*f b)^2) =
      (u:S)^6 * f (-16*(4*a^3+27*b^2)) := by
    simp only [map_neg,map_mul,map_add,map_pow,map_ofNat]
    ring
  rw [he]
  exact (u.isUnit.pow 6).mul (h.map f)

theorem disc_unit : IsUnit
    (-16*(4*(twistA n I τ hτ hY)^3+27*(twistB n I τ hτ hY)^2)) :=
  @discriminant_scale (R n) ↥(fixed n I τ) inferInstance
    (@Subalgebra.toCommRing (R n) (D n ⧸ I) inferInstance inferInstance inferInstance (fixed n I τ))
    (algebraMap (R n) (fixed n I τ)) (twistUnit n I τ hτ hY) (A n) (B n)
    (OpenJAffineScheme318.discriminant_unit n)

/-- The same canonical coefficient map into the actual quotient,
spelled as a shallow ring-hom composition. -/
abbrev ambientCoeff : R n →+* (D n ⧸ I) :=
  (q n I).toRingHom.comp (algebraMap (R n) (D n))

private theorem literal_relation :
    (ybar n I)^2-(xbar n I)^3-ambientCoeff n I (A n)*xbar n I-ambientCoeff n I (B n)=0 := by
  have h := congrArg (q n I) (ShortAffineJacobian318.relation (A n) (B n))
  simpa only [map_sub,map_mul,map_pow,map_zero,ambientCoeff,RingHom.comp_apply,AlgHom.toRingHom_eq_coe] using h

/-- Exact marked point on the globally normalized twisted short equation.
No locally selected square root appears in either coordinate over (fixed n I τ). -/
theorem actual_equation :
    (markY n I τ hτ hY)^2-(markX n I τ hτ hY)^3-
      twistA n I τ hτ hY*markX n I τ hτ hY-twistB n I τ hτ hY=0 := by
  apply Subtype.val_injective
  change (fixed n I τ).val (((↑(twistUnit n I τ hτ hY) : ↥(fixed n I τ))^2)^2-((↑(twistUnit n I τ hτ hY) : ↥(fixed n I τ))*(fixedX n I τ hτ))^3-((↑(twistUnit n I τ hτ hY) : ↥(fixed n I τ))^2*algebraMap (R n) (fixed n I τ) (A n))*((↑(twistUnit n I τ hτ hY) : ↥(fixed n I τ))*(fixedX n I τ hτ))-(↑(twistUnit n I τ hτ hY) : ↥(fixed n I τ))^3*algebraMap (R n) (fixed n I τ) (B n)) = (fixed n I τ).val 0
  simp only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes,twistUnit_value]
  change (((ybar n I)^2)^2)^2-((ybar n I)^2*xbar n I)^3-
    (((ybar n I)^2)^2*ambientCoeff n I (A n))*((ybar n I)^2*xbar n I)-
      ((ybar n I)^2)^3*ambientCoeff n I (B n)=0
  linear_combination (ybar n I)^6*literal_relation n I

/-- The ordinary exact point evaluation, built at an abstract ring
so the same canonical subtype operations are not re-synthesized. -/
@[expose] def equationEvaluation {S : Type*} [CommRing S] (a b x y : S)
    (h : y^2-x^3-a*x-b=0) : ShortAffineJacobian318.Ring a b →ₐ[S] S :=
  AffineEquationFunctor318.toHom (R:=S) (S:=S) a b ⟨(x,y),by
    simpa only [Algebra.algebraMap_self,RingHom.id_apply] using h⟩

/-- The literal induced algebra map of the genuine marked affine point. -/
@[expose] def markEvaluation : ShortAffineJacobian318.Ring
    (twistA n I τ hτ hY) (twistB n I τ hτ hY) →ₐ[fixed n I τ] (fixed n I τ) :=
  @equationEvaluation ↥(fixed n I τ)
    (@Subalgebra.toCommRing (R n) (D n ⧸ I) inferInstance inferInstance inferInstance (fixed n I τ))
    (twistA n I τ hτ hY) (twistB n I τ hτ hY) (markX n I τ hτ hY) (markY n I τ hτ hY)
    (by exact actual_equation n I τ hτ hY)

theorem over_original_chart :
    (fixed n I τ).val (twistA n I τ hτ hY) = (hY.unit:(D n ⧸ I))^4*ambientCoeff n I (A n) ∧
    (fixed n I τ).val (twistB n I τ hτ hY) = (hY.unit:(D n ⧸ I))^6*ambientCoeff n I (B n) ∧
    (fixed n I τ).val (markX n I τ hτ hY) = (hY.unit:(D n ⧸ I))^2*xbar n I ∧
    (fixed n I τ).val (markY n I τ hτ hY) = (hY.unit:(D n ⧸ I))^3*ybar n I := by
  constructor
  · simp only [twistA,map_mul,map_pow,AlgHom.commutes,twistUnit_value,hY.unit_spec] <;> ring
  constructor
  · simp only [twistB,map_mul,map_pow,AlgHom.commutes,twistUnit_value,hY.unit_spec] <;> ring
  constructor
  · simp only [markX,map_mul,twistUnit_value,hY.unit_spec] <;> rfl
  · simp only [markY,map_pow,twistUnit_value,hY.unit_spec] <;> ring

end SelectedPrimitiveTwistPoint318

#print axioms SelectedPrimitiveTwistPoint318.markEvaluation
#print axioms SelectedPrimitiveTwistPoint318.over_original_chart
