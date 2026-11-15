module
public import IntegerResidueBoxCount318
public section
noncomputable section
namespace TriangularLatticeBoxCount318
open IntegerResidueBoxCount318 TernaryQuadraticLineCover318 TriangularTernaryBasis318
open scoped BigOperators
set_option maxHeartbeats 1000000

@[expose] def Box (B : ℕ) := Interval B×Interval B×Interval B
@[expose] def coordinates {B : ℕ} (v : Box B) : Vector ℤ := (v.1.1,v.2.1.1,v.2.2.1)
@[expose] def LatticeBox (B q r : ℕ) (A D : ℤ) :=
  {v : Box B // Conditions (q:ℤ) (r:ℤ) A D (coordinates v)}

/-- Exact fibers in the ORIGINAL coordinate box. The residue shifts may
depend on x; the uniform one-dimensional bound allows that dependence. -/
@[expose] def fibers (B q r : ℕ) (A D : ℤ) : LatticeBox B q r A D ≃
    (Σ x : ResidueBox B r 0, ResidueBox B q (A*x.1.1)×ResidueBox B (q*r) (D*x.1.1)) where
  toFun v := ⟨⟨v.1.1,by simpa only [sub_zero] using v.2.1⟩,
    ⟨v.1.2.1,v.2.2.1⟩,⟨v.1.2.2,by simpa only [Nat.cast_mul] using v.2.2.2⟩⟩
  invFun v := ⟨(v.1.1,v.2.1.1,v.2.2.1),
    ⟨by simpa only [sub_zero] using v.1.2,v.2.1.2,by simpa only [Nat.cast_mul] using v.2.2.2⟩⟩
  left_inv v := rfl
  right_inv v := rfl

/-- Uniform exact residue-box upper bound for the actual triangular lattice. -/
theorem product_bound (B q r : ℕ) (hq : 0<q) (hr : 0<r) (A D : ℤ) :
    Nat.card (LatticeBox B q r A D)≤(2*B/r+1)*(2*B/q+1)*(2*B/(q*r)+1) := by
  classical
  have hc : Nat.card (LatticeBox B q r A D)=
      ∑ x : ResidueBox B r 0, Nat.card (ResidueBox B q (A*x.1.1))*
        Nat.card (ResidueBox B (q*r) (D*x.1.1)) := by
    rw [Nat.card_congr (fibers B q r A D)]
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_prod]
  rw [hc]
  calc
    ∑ x : ResidueBox B r 0, Nat.card (ResidueBox B q (A*x.1.1))*
        Nat.card (ResidueBox B (q*r) (D*x.1.1))≤
      ∑ _x : ResidueBox B r 0, (2*B/q+1)*(2*B/(q*r)+1) := by
      apply Finset.sum_le_sum
      intro x hx
      exact Nat.mul_le_mul (residue_box_card B q hq _) (residue_box_card B (q*r) (mul_pos hq hr) _)
    _ = Nat.card (ResidueBox B r 0)*((2*B/q+1)*(2*B/(q*r)+1)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ (2*B/r+1)*((2*B/q+1)*(2*B/(q*r)+1)) :=
      Nat.mul_le_mul_right _ (residue_box_card B r hr 0)
    _ = (2*B/r+1)*(2*B/q+1)*(2*B/(q*r)+1) := by ring

lemma interval_scaled (B d : ℕ) (hdB : d≤B) : (2*B/d+1)*d≤3*B := by
  have hh := Nat.div_mul_le_self (2*B) d
  nlinarith

/-- An actual uniform 27*B³/M² count when B>=M, not an unsupported
inference from determinant or a purported reduced basis. -/
theorem scaled_count (B q r : ℕ) (hq : 0<q) (hr : 0<r) (hM : q*r≤B) (A D : ℤ) :
    Nat.card (LatticeBox B q r A D)*(q*r)^2≤27*B^3 := by
  have hqB : q≤B := by have hh : 1≤r := hr; nlinarith
  have hrB : r≤B := by have hh : 1≤q := hq; nlinarith
  have hR := interval_scaled B r hrB
  have hQ := interval_scaled B q hqB
  have hM' := interval_scaled B (q*r) hM
  have hh := Nat.mul_le_mul (Nat.mul_le_mul hR hQ) hM'
  calc
    Nat.card (LatticeBox B q r A D)*(q*r)^2≤
      ((2*B/r+1)*(2*B/q+1)*(2*B/(q*r)+1))*(q*r)^2 :=
      Nat.mul_le_mul_right _ (product_bound B q r hq hr A D)
    _ = (((2*B/r+1)*r)*((2*B/q+1)*q))*((2*B/(q*r)+1)*(q*r)) := by ring
    _ ≤ (3*B*(3*B))*(3*B) := hh
    _ = 27*B^3 := by ring

end TriangularLatticeBoxCount318
