module
public import SelectedPrimitiveOrdinateUnit318
public section
noncomputable section
open Polynomial
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318

namespace SelectedPrimitiveTwistPoint318
variable (n : ℕ) (I : Ideal (D n))
local notation "R" => SelectedPrimitiveAffineSign318.R n
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q) (hτ : τ.comp (q n I) = (q n I).comp (sign n))
local notation "F" => fixed n I τ
variable (hY : IsUnit (ybar n I))
local notation "Y" => hY.unit

include hτ in
theorem y_anti : τ (ybar n I) = -ybar n I := by
  simpa only [AlgHom.comp_apply,ChartNegation318.affineNeg_y,map_neg] using
    DFunLike.congr_fun hτ (SelectedPrimitiveAffineSign318.Y n)

include hτ in
private theorem fix_square_unit : Units.map τ.toMonoidHom (Y^2) = Y^2 := by
  have h : Units.map τ.toMonoidHom Y = -Y := by
    apply Units.ext
    change τ (Y:Q) = -(Y:Q)
    rw [hY.unit_spec,y_anti n I τ hτ]
  rw [map_pow,h]
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val,Units.val_neg] <;> ring

/-- The actual fixed twisting parameter is the square of the primitive
ordinate. Its inverse is fixed as well, not assumed to descend. -/
@[expose] def twistUnit : Fˣ where
  val := ⟨(↑(Y^2):Q),by exact congrArg (fun u : Qˣ => (u:Q)) (fix_square_unit n I τ hτ hY)⟩
  inv := ⟨(↑((Y^2)⁻¹):Q),by
    have h : Units.map τ.toMonoidHom (Y^2)⁻¹ = (Y^2)⁻¹ := by
      rw [map_inv,fix_square_unit n I τ hτ hY]
    exact congrArg (fun u : Qˣ => (u:Q)) h⟩
  val_inv := Subtype.ext (Units.mul_inv (Y^2))
  inv_val := Subtype.ext (Units.inv_mul (Y^2))

local notation "d" => (twistUnit n I τ hτ hY : Fˣ)

theorem twistUnit_value : (F.val (d:F) : Q) = (ybar n I)^2 := by
  change (↑(Y^2):Q) = _
  rw [Units.val_pow_eq_pow_val,hY.unit_spec]

@[expose] def fixedX : F :=
  ⟨xbar n I,(fixed_iff_polynomial n I τ hτ (xbar n I)).mpr ⟨X,aeval_X _⟩⟩

local notation "x₀" => fixedX n I τ hτ
local notation "a" => algebraMap R F
local notation "s" => (d:F)

abbrev twistA := s^2*a (A n)
abbrev twistB := s^3*a (B n)
abbrev markX := s*x₀
abbrev markY := s^2

theorem disc_unit : IsUnit
    (-16*(4*(twistA n I τ hτ hY)^3+27*(twistB n I τ hτ hY)^2)) := by
  have he : -16*(4*(s^2*a (A n))^3+27*(s^3*a (B n))^2) =
      s^6 * a (-16*(4*(A n)^3+27*(B n)^2)) := by
    simp only [map_neg,map_mul,map_add,map_pow,map_ofNat]
    ring
  change IsUnit (-16*(4*(s^2*a (A n))^3+27*(s^3*a (B n))^2))
  rw [he]
  exact (d.isUnit.pow 6).mul ((OpenJAffineScheme318.discriminant_unit n).map a)

private theorem literal_relation :
    (ybar n I)^2-(xbar n I)^3-algebraMap R Q (A n)*xbar n I-algebraMap R Q (B n)=0 := by
  have h := congrArg (q n I) (ShortAffineJacobian318.relation (A n) (B n))
  simpa only [map_sub,map_mul,map_pow,map_zero,AlgHom.commutes] using h

/-- Exact marked point on the globally normalized twisted short equation.
No locally selected square root appears in either coordinate over F. -/
theorem actual_equation :
    (markY n I τ hτ hY)^2-(markX n I τ hτ hY)^3-
      twistA n I τ hτ hY*markX n I τ hτ hY-twistB n I τ hτ hY=0 := by
  apply Subtype.val_injective
  change F.val ((s^2)^2-(s*x₀)^3-(s^2*a (A n))*(s*x₀)-s^3*a (B n)) = F.val 0
  simp only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes,twistUnit_value]
  change (((ybar n I)^2)^2)^2-((ybar n I)^2*xbar n I)^3-
    (((ybar n I)^2)^2*algebraMap R Q (A n))*((ybar n I)^2*xbar n I)-
      ((ybar n I)^2)^3*algebraMap R Q (B n)=0
  linear_combination (ybar n I)^6*literal_relation n I

/-- The literal induced algebra map of the genuine marked affine point. -/
@[expose] def markEvaluation : ShortAffineJacobian318.Ring
    (twistA n I τ hτ hY) (twistB n I τ hτ hY) →ₐ[F] F :=
  AffineEquationFunctor318.toHom _ _ ⟨(markX n I τ hτ hY,markY n I τ hτ hY),by
    simpa only [Algebra.algebraMap_self,RingHom.id_apply] using actual_equation n I τ hτ hY⟩

theorem over_original_chart :
    F.val (twistA n I τ hτ hY) = (Y:Q)^4*algebraMap R Q (A n) ∧
    F.val (twistB n I τ hτ hY) = (Y:Q)^6*algebraMap R Q (B n) ∧
    F.val (markX n I τ hτ hY) = (Y:Q)^2*xbar n I ∧
    F.val (markY n I τ hτ hY) = (Y:Q)^3*ybar n I := by
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
