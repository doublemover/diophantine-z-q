module
public import OriginalRCSupportWeightIdentity318
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
public section

namespace OriginalRC47TraceMatrix318
open OriginalRCSupportWeightIdentity318

variable {R : Type*} [CommRing R]

/-- Actual 2×2 Frobenius matrix computation, with both the diagonal
shift and the determinant normalized at q. -/
theorem det_shift (F : Matrix (Fin 2) (Fin 2) R) (x q : R) :
    (x • F - q • (1 : Matrix (Fin 2) (Fin 2) R)).det =
      x^2 * F.det - q*x*F.trace + q^2 := by
  have h01 : (0:Fin 2) ≠ 1 := by decide
  have h10 : (1:Fin 2) ≠ 0 := by decide
  simp only [Matrix.det_fin_two,Matrix.trace_fin_two,Matrix.sub_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.one_apply,eq_self_iff_true,h01,h10,if_true,if_false,
    mul_one,mul_zero,sub_zero]
  ring

/-- The two conjugate placed matrices give the old `q^4·l_q` and
not a second root-of-unity or extra Frobenius factor. -/
theorem two_place_det (F : Matrix (Fin 2) (Fin 2) R) (Q z : Rˣ)
    (hF : F.det = (Q:R)) :
    ((z:R) • F - (Q:R) • (1 : Matrix (Fin 2) (Fin 2) R)).det *
      ((↑z⁻¹:R) • F - (Q:R) • (1 : Matrix (Fin 2) (Fin 2) R)).det =
      (Q:R)^4 * euler F.trace Q z := by
  have hu : (Q:R) * (↑Q⁻¹:R) = 1 := Units.mul_inv Q
  have hs : (Q:R)^4 * (↑Q⁻¹:R)^2 = (Q:R)^2 := by
    calc
      _ = (Q:R)^2 * ((Q:R)^2 * (↑Q⁻¹:R)^2) := by ring
      _ = _ := by rw [←mul_pow,hu,one_pow,mul_one]
  rw [det_shift,det_shift,hF,euler,
    ←mul_assoc ((Q:R)^4) ((↑Q⁻¹:R)^2),hs]
  ring

/-- At the two actually transported places the Frobenius matrices can
be different. Their own trace/determinant equality gives the same token. -/
theorem two_place_det_transported (F₁ F₂ : Matrix (Fin 2) (Fin 2) R)
    (Q z : Rˣ) (h₁ : F₁.det = (Q:R)) (h₂ : F₂.det = (Q:R))
    (htr : F₂.trace = F₁.trace) :
    ((z:R) • F₁ - (Q:R) • (1 : Matrix (Fin 2) (Fin 2) R)).det *
      ((↑z⁻¹:R) • F₂ - (Q:R) • (1 : Matrix (Fin 2) (Fin 2) R)).det =
      (Q:R)^4 * euler F₁.trace Q z := by
  have h := two_place_det F₁ Q z h₁
  rw [det_shift,det_shift,h₁,h₂,htr]
  simpa only [det_shift,h₁] using h

/-- The literal rank-four singular quotient, with the two oriented
places in the stipulated order. -/
@[expose] def quotientMatrix (F₁ F₂ : Matrix (Fin 2) (Fin 2) R)
    (Q z : Rˣ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks ((z:R) • F₁ - (Q:R) • (1 : Matrix (Fin 2) (Fin 2) R))
    0 0 ((↑z⁻¹:R) • F₂ - (Q:R) • (1 : Matrix (Fin 2) (Fin 2) R))

theorem quotient_block_det (F₁ F₂ : Matrix (Fin 2) (Fin 2) R) (Q z : Rˣ)
    (h₁ : F₁.det = (Q:R)) (h₂ : F₂.det = (Q:R)) (htr : F₂.trace = F₁.trace) :
    (quotientMatrix F₁ F₂ Q z).det = (Q:R)^4 * euler F₁.trace Q z := by
  rw [quotientMatrix,Matrix.det_fromBlocks_zero₂₁]
  exact two_place_det_transported F₁ F₂ Q z h₁ h₂ htr

/-- On the actual appended-basis block the extension entries do not
contribute a second determinant factor. -/
theorem split_support_block_det {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I R) (T : Matrix I (Fin 2 ⊕ Fin 2) R)
    (F₁ F₂ : Matrix (Fin 2) (Fin 2) R) (Q z : Rˣ)
    (h₁ : F₁.det = (Q:R)) (h₂ : F₂.det = (Q:R)) (htr : F₂.trace = F₁.trace) :
    (Matrix.fromBlocks P T 0 (quotientMatrix F₁ F₂ Q z)).det =
      P.det * ((Q:R)^4 * euler F₁.trace Q z) := by
  rw [Matrix.det_fromBlocks_zero₂₁,quotient_block_det F₁ F₂ Q z h₁ h₂ htr]

/-- The actual based support token κ is not invented here. This is its
genuine re-normalization as a unit already over the coefficient ring. -/
@[expose] def epsilon47 (Q κ : Rˣ) : Rˣ := Q⁻¹ ^ 4 * κ

/-- Restore the exact determinant convention of (4.7) without
canceling the norm scalar or evaluating it at the center. -/
theorem support_unit_identity (F₁ F₂ : Matrix (Fin 2) (Fin 2) R) (Q z κ : Rˣ)
    (h₁ : F₁.det = (Q:R)) (h₂ : F₂.det = (Q:R)) (htr : F₂.trace = F₁.trace) (uRel uPrim : R)
    (hPair :
      (quotientMatrix F₁ F₂ Q z).det * uRel =
        denominator F₁.trace z * (κ:R) * uPrim) :
    euler F₁.trace Q z * uRel = denominator F₁.trace z * (epsilon47 Q κ:R) * uPrim := by
  have hu : (↑Q⁻¹:R)^4 * (Q:R)^4 = 1 := by
    rw [←mul_pow,Units.inv_mul,one_pow]
  rw [quotient_block_det F₁ F₂ Q z h₁ h₂ htr] at hPair
  calc
    _ = (↑Q⁻¹:R)^4 * ((Q:R)^4 * euler F₁.trace Q z * uRel) := by
      rw [←mul_assoc (↑Q⁻¹:R)^4 ((Q:R)^4 * euler F₁.trace Q z),
        ←mul_assoc (↑Q⁻¹:R)^4 ((Q:R)^4),hu,one_mul]
    _ = _ := by
      rw [hPair]
      simp only [epsilon47,Units.val_mul,Units.val_pow_eq_pow_val]
      ring

end OriginalRC47TraceMatrix318

#print axioms OriginalRC47TraceMatrix318.two_place_det
#print axioms OriginalRC47TraceMatrix318.support_unit_identity
