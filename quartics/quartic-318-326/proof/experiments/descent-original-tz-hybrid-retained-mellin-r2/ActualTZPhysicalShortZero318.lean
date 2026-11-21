module
public import ActualTZLiteralWrapClipping318
public import ActualTZExactZeroIntegerGrid318
import all ActualTZExactZeroIntegerGrid318
public section
noncomputable section
namespace ActualTZPhysicalShortZero318
open scoped BigOperators
open ActualTZLiteralWrapClipping318 ActualTZExactZeroIntegerGrid318

variable {dAxes : ℕ} {R J : Type*} [Fintype R] [Fintype J]

/-- One native exact strip estimate on the actual integer digit
grid. The finite wrap table and distinct physical pair polynomials
are supplied by the literal extraction, with no modulo-p
condition or independence after selection. -/
theorem lost_key_mass (L : Fin dAxes→ℕ) (s : Fin dAxes→ℤ) (M d n : ℕ)
    (hM : 0<M) (hL : ∀ i,M≤L i) (hn : 0<n)
    (len : Grid L→R→ℕ) (hlen : ∀ z r,len z r≤n)
    (D : R→J→MvPolynomial (Fin dAxes) ℤ)
    (hD : ∀ r i,D r i≠0) (hDeg : ∀ r i,(D r i).totalDegree≤d) :
    let zero (z : Grid L) (r : R) (i : J) := MvPolynomial.eval (point L s z) (D r i)=0
    (∑ _z : Grid L,(uniform L:ℝ)*(∑ r : R,
      (wrapMass n len _z r-kept n ((n:ℝ)^((3:ℝ)/4)) len zero _z r)))≤
      (Fintype.card R:ℝ)*((n:ℝ)^(-(1:ℝ)/4)+
        (Fintype.card J:ℝ)*((dAxes:ℝ)*((d:ℝ)/M))) := by
  intro zero
  have hm : 0≤(uniform L:ℝ) := by positivity
  have hNormal : (∑ _ : Grid L,(uniform L:ℝ))=1 := by
    exact_mod_cast uniform_one L (fun i=>hM.trans_le (hL i))
  have hZero (r : R) (i : J) :
      (∑ z : Grid L,(uniform L:ℝ)*(if zero z r i then 1 else 0))≤(dAxes:ℝ)*((d:ℝ)/M) := by
    have H := integer_zero_le L s (D r i) (hD r i) M d hM hL (hDeg r i)
    have H' : (∑ z : Grid L,if zero z r i then (uniform L:ℝ) else 0)≤
        (dAxes:ℝ)*((d:ℝ)/M) := by exact_mod_cast H
    refine le_trans ?_ H'
    apply Finset.sum_le_sum
    intro z _
    by_cases h : zero z r i <;> simp [h]
  have H := lost_mass n hn ((n:ℝ)^((3:ℝ)/4)) (Real.rpow_nonneg (by positivity) _)
    len hlen zero (fun _=>(uniform L:ℝ)) (fun _=>hm) hNormal _ hZero
  have hp : 0<(n:ℝ) := by exact_mod_cast hn
  have hExp : (n:ℝ)^((3:ℝ)/4)/(n:ℝ)=(n:ℝ)^(-(1:ℝ)/4) := by
    calc
      _ = (n:ℝ)^((3:ℝ)/4)/(n:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_sub hp]; congr 1 <;> ring
  rw [hExp] at H
  exact H

end ActualTZPhysicalShortZero318
