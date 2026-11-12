module
public import ActualTwoDescentFieldAlgebraicClosureHalving318
public section
noncomputable section
namespace ActualTwoDescentFieldGaloisPointAction318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticFieldCoordinates318
open ActualTwoDescentFieldAlgebraicClosureHalving318
local instance : DecidableEq Qbar := Classical.decEq _

lemma galois_negY (σ : GalQ) (n : F) (x y : Qbar) :
    (curve (algebraMap F Qbar n)).toAffine.negY (σ x) (σ y)=σ ((curve (algebraMap F Qbar n)).toAffine.negY x y) := by
  simpa only [σ.commutes n] using actual_negY_map σ.toRingHom (algebraMap F Qbar n) x y

lemma galois_slope (σ : GalQ) (n : F) (x₁ x₂ y₁ y₂ : Qbar) :
    (curve (algebraMap F Qbar n)).toAffine.slope (σ x₁) (σ x₂) (σ y₁) (σ y₂)=
      σ ((curve (algebraMap F Qbar n)).toAffine.slope x₁ x₂ y₁ y₂) := by
  simpa only [σ.commutes n] using actual_slope_map σ.toRingHom (algebraMap F Qbar n) x₁ x₂ y₁ y₂

lemma galois_addX (σ : GalQ) (n : F) (x₁ x₂ l : Qbar) :
    (curve (algebraMap F Qbar n)).toAffine.addX (σ x₁) (σ x₂) (σ l)=
      σ ((curve (algebraMap F Qbar n)).toAffine.addX x₁ x₂ l) := by
  simpa only [σ.commutes n] using actual_addX_map σ.toRingHom (algebraMap F Qbar n) x₁ x₂ l

lemma galois_addY (σ : GalQ) (n : F) (x₁ x₂ y₁ l : Qbar) :
    (curve (algebraMap F Qbar n)).toAffine.addY (σ x₁) (σ x₂) (σ y₁) (σ l)=
      σ ((curve (algebraMap F Qbar n)).toAffine.addY x₁ x₂ y₁ l) := by
  simpa only [σ.commutes n] using actual_addY_map σ.toRingHom (algebraMap F Qbar n) x₁ x₂ y₁ l

def galoisPoint (σ : GalQ) (n : F) (hn : n ≠ 0) : Point (algebraMap F Qbar n) → Point (algebraMap F Qbar n)
  | .zero => .zero
  | .some x y h => point _ (σ x) (σ y) (rational_parameter_ne n hn) (by
      simpa only [σ.commutes n] using actual_curve_equation_map σ.toRingHom _ x y ((curve_equation _ x y).mp h.left))

lemma actual_galois_point_add (σ : GalQ) (n : F) (hn : n ≠ 0) (P Q : Point (algebraMap F Qbar n)) :
    galoisPoint σ n hn (P+Q)=galoisPoint σ n hn P+galoisPoint σ n hn Q := by
  cases P with
  | zero => simp only [zero_add,galoisPoint]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => simp only [add_zero,galoisPoint]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁=x₂ ∧ y₁=(curve (algebraMap F Qbar n)).toAffine.negY x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        dsimp [galoisPoint,point]
        symm
        apply WeierstrassCurve.Affine.Point.add_of_Y_eq (congrArg σ hxy.1)
        rw [galois_negY,hxy.2]
      · have hfxy : ¬(σ x₁=σ x₂ ∧ σ y₁=(curve (algebraMap F Qbar n)).toAffine.negY (σ x₂) (σ y₂)) := by
          rintro ⟨hx,hy⟩
          rw [galois_negY] at hy
          exact hxy ⟨σ.injective hx,σ.injective hy⟩
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        dsimp [galoisPoint,point]
        rw [WeierstrassCurve.Affine.Point.add_some hfxy]
        congr 1
        · rw [galois_slope,galois_addX]
        · rw [galois_slope,galois_addY]

def galoisPointHom (σ : GalQ) (n : F) (hn : n ≠ 0) : Point (algebraMap F Qbar n) →+ Point (algebraMap F Qbar n) where
  toFun := galoisPoint σ n hn
  map_zero' := rfl
  map_add' := actual_galois_point_add σ n hn

lemma actual_galois_one (n : F) (hn : n ≠ 0) (P : Point (algebraMap F Qbar n)) :
    galoisPointHom 1 n hn P=P := by cases P <;> rfl

lemma actual_galois_mul (σ τ : GalQ) (n : F) (hn : n ≠ 0) (P : Point (algebraMap F Qbar n)) :
    galoisPointHom (σ*τ) n hn P=galoisPointHom σ n hn (galoisPointHom τ n hn P) := by cases P <;> rfl

end ActualTwoDescentFieldGaloisPointAction318
