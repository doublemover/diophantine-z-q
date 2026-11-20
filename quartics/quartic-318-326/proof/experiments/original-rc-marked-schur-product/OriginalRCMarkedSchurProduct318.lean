module
public import OriginalRCActualSchurBlock318
import Mathlib.Tactic.Ring
public section

namespace OriginalRCMarkedSchurProduct318
open Matrix OriginalRCActualSchurBlock318

variable {R I J : Type*} [CommRing R]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The H¹ coordinate of the actual marked column after incoming
cancellation. Outgoing cancellation leaves this coordinate of the
projection unchanged. -/
@[expose] def firstRead (Ai : Matrix I I R) (C : Matrix (Fin 1) I R)
    (zB : Matrix I (Fin 1) R) (zH : Matrix (Fin 1) (Fin 1) R) : R :=
  (zH - C * Ai * zB) 0 0

/-- The actual regular functional on the H² survivor inclusion after
outgoing cancellation. No arbitrary dual functional is supplied. -/
@[expose] def pairedRead (Ai : Matrix J J R) (B : Matrix J (Fin 1) R)
    (muE : Matrix (Fin 1) J R) (muH : Matrix (Fin 1) (Fin 1) R) : R :=
  (muH - muE * Ai * B) 0 0

@[expose] def clearFirst (A : Matrix I I R) (C : Matrix (Fin 1) I R)
    (zB : Matrix I (Fin 1) R) (zH : Matrix (Fin 1) (Fin 1) R) : R :=
  (A.det • zH - C * A.adjugate * zB) 0 0

@[expose] def clearPaired (A : Matrix J J R) (B : Matrix J (Fin 1) R)
    (muE : Matrix (Fin 1) J R) (muH : Matrix (Fin 1) (Fin 1) R) : R :=
  (A.det • muH - muE * A.adjugate * B) 0 0

theorem clearFirst_spec (A Ai : Matrix I I R) (hi : A * Ai = 1)
    (C : Matrix (Fin 1) I R) (zB : Matrix I (Fin 1) R) (zH : Matrix (Fin 1) (Fin 1) R) :
    clearFirst A C zB zH = A.det * firstRead Ai C zB zH := by
  unfold clearFirst firstRead
  rw [adjugate_of_right_inverse A Ai hi,Matrix.mul_smul,Matrix.smul_mul,←smul_sub] <;> rfl

theorem clearPaired_spec (A Ai : Matrix J J R) (hi : A * Ai = 1)
    (B : Matrix J (Fin 1) R) (muE : Matrix (Fin 1) J R) (muH : Matrix (Fin 1) (Fin 1) R) :
    clearPaired A B muE muH = A.det * pairedRead Ai B muE muH := by
  unfold clearPaired pairedRead
  rw [adjugate_of_right_inverse A Ai hi,Matrix.mul_smul,Matrix.smul_mul,←smul_sub] <;> rfl

/-- In the actual *constant* Smith bases the B→H incoming block
has zero constant. Evaluate the same marked projection; it is then
the genuine integral H¹ coordinate, without a resetting denominator. -/
theorem firstRead_at_vanishing_cross {K : Type*} [CommRing K] (σ : R →+* K)
    (Ai : Matrix I I R) (C : Matrix (Fin 1) I R)
    (zB : Matrix I (Fin 1) R) (zH : Matrix (Fin 1) (Fin 1) R)
    (hC : C.map σ = 0) :
    σ (firstRead Ai C zB zH) = σ (zH 0 0) := by
  have h : (C * Ai * zB).map σ = 0 := by
    simp only [Matrix.map_mul,hC,Matrix.zero_mul]
  have he : σ ((C * Ai * zB) 0 0) = 0 :=
    congrArg (fun T : Matrix (Fin 1) (Fin 1) K => T 0 0) h
  simp only [firstRead,Matrix.sub_apply,map_sub,he,sub_zero]

/-- Scalar clearing identity with the actual powers Δ³ and Δ⁴,
using exactly the degree-0/2 positive and degree-1 negative signs. -/
theorem three_disk_product (d₀ d₂ ε κ η α β : R) (d₁ a : Rˣ) :
    let Δ := d₀ * (d₁:R) * d₂
    let T := ε * d₀ * (↑d₁⁻¹:R) * d₂
    let Q := κ * (Δ*α) * (Δ*β) * (ε*(d₀*d₂)^2)
    (a:R)*Δ^4 * (η*(κ*α*((↑a⁻¹:R)*β)*T)) = η*Δ*Q := by
  dsimp only
  calc
    _ = ((a:R)*(↑a⁻¹:R))*((d₁:R)*(↑d₁⁻¹:R)) *
         (η*(d₀*(d₁:R)*d₂) *
          (κ*((d₀*(d₁:R)*d₂)*α)*((d₀*(d₁:R)*d₂)*β)*(ε*(d₀*d₂)^2))) := by ring
    _ = _ := by rw [Units.mul_inv a,Units.mul_inv d₁,one_mul,one_mul]

/-- One finite chart for the literal marked pair. The cleared factors
use the actual adjugate matrices; the incoming and outgoing reads
use their actual inverses. The middle pivot determinant is already
the specified unit in this chart, not a change to the original Δ. -/
theorem actual_chart_product {K : Type*} [Fintype K] [DecidableEq K]
    (A₀ Ai₀ : Matrix I I R) (A₁ : Matrix K K R) (A₂ Ai₂ : Matrix J J R)
    (h₀ : A₀ * Ai₀ = 1) (h₂ : A₂ * Ai₂ = 1)
    (C : Matrix (Fin 1) I R) (B : Matrix J (Fin 1) R)
    (zB : Matrix I (Fin 1) R) (zH : Matrix (Fin 1) (Fin 1) R)
    (muE : Matrix (Fin 1) J R) (muH : Matrix (Fin 1) (Fin 1) R)
    (ε κ η : R) (a₀ : ℕ) (d₁ a : Rˣ)
    (hm : (d₁:R) = A₁.det) (ha : (a:R) = (2:R)^a₀) :
    let δ₀ := A₀.det
    let δ₁ := A₁.det
    let δ₂ := A₂.det
    let Δ := δ₀ * δ₁ * δ₂
    let T := ε * δ₀ * (↑d₁⁻¹:R) * δ₂
    let Z := δ₁*δ₂*clearFirst A₀ C zB zH
    let W := δ₀*δ₁*clearPaired A₂ B muE muH
    let Q := κ*Z*W*(ε*(δ₀*δ₂)^2)
    let f := (2:R)^a₀*Δ^4
    let d := η*Δ*Q
    f * (η*(κ*firstRead Ai₀ C zB zH*((↑a⁻¹:R)*pairedRead Ai₂ B muE muH)*T)) = d := by
  dsimp only
  rw [←hm,←ha,clearFirst_spec A₀ Ai₀ h₀,clearPaired_spec A₂ Ai₂ h₂]
  have h := three_disk_product A₀.det A₂.det ε κ η
    (firstRead Ai₀ C zB zH) (pairedRead Ai₂ B muE muH) d₁ a
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

end OriginalRCMarkedSchurProduct318

#print axioms OriginalRCMarkedSchurProduct318.actual_chart_product
