module
public import ActualTwoDescentLocalIdentityAvoidance318
public section
noncomputable section
namespace ActualTwoDescentLocalCosetNonexceptional318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentLocalIdentityAvoidance318 ActualTwoDescentGoodPrimeValuations318
open ActualTwoDescentFinitePointCardinality318
variable {p : ℕ} [Fact p.Prime]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Every actual local Kummer class has a non-two-torsion representative on the SAME curve. -/
theorem actual_local_coset_nonexceptional (n : ℕ) (hn : n ≠ 0) (P : Point (n : ℚ_[p])) :
    ∃ Q : LocalPoint (p:=p) n, kummerClass (n : ℚ_[p]) (Nat.cast_ne_zero.mpr hn)
      (point (n : ℚ_[p]) Q.x Q.y (Nat.cast_ne_zero.mpr hn) Q.curve)=
      kummerClass (n : ℚ_[p]) (Nat.cast_ne_zero.mpr hn) P := by
  let hnq : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn
  let S : Finset (Point (n : ℚ_[p])) := Finset.univ.image (fun i : Fin 4 => fourTorsion (n : ℚ_[p]) hnq i-P)
  obtain ⟨R,hR,hclass⟩ := actual_identity_class_avoids_finite (p:=p) n hn S
  have havoid : ∀ i : Fin 4, P+R ≠ fourTorsion (n : ℚ_[p]) hnq i := by
    intro i he
    apply hR
    apply Finset.mem_image.mpr
    refine ⟨i,Finset.mem_univ _,?_⟩
    apply (sub_eq_iff_eq_add).mpr
    simpa only [add_comm] using he.symm
  have hdouble : (P+R)+(P+R) ≠ 0 := by
    intro he
    obtain ⟨i,hi⟩ := actual_two_torsion_exhaustion (n : ℚ_[p]) hnq (P+R) he
    exact havoid i hi
  have hsame : kummerClass (n : ℚ_[p]) hnq (P+R)=kummerClass (n : ℚ_[p]) hnq P := by
    rw [kummer_class_add,hclass,mul_one]
  generalize hsum : P+R=T at hdouble hsame
  cases T with
  | zero => exact False.elim (hdouble (zero_add _))
  | some x y h =>
    have hy : y ≠ 0 := by
      intro he
      apply hdouble
      apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      rw [curve_negY,he,neg_zero]
    have hc := (curve_equation (n : ℚ_[p]) x y).mp h.left
    have hprod : x*(x-(n : ℚ_[p]))*(x+3*(n : ℚ_[p])) ≠ 0 := by rw [←hc]; exact pow_ne_zero _ hy
    have hA := (mul_ne_zero_iff.mp hprod).2
    have hx := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1).1
    have hB := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1).2
    exact ⟨⟨x,y,hx,hB,hA,hc⟩,hsame⟩

end ActualTwoDescentLocalCosetNonexceptional318
