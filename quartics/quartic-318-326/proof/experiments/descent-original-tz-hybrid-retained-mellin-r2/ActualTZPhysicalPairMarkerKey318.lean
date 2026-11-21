module
public import ActualTZActualPhysicalProbeHeight318
public import ActualTZProbeExceptionalWheel318
public section
noncomputable section
namespace ActualTZPhysicalPairMarkerKey318
open scoped BigOperators
open ActualTZActualPhysicalProbeHeight318 ActualTZProbeExceptionalWheel318
open ActualTZRelabelPhysicalGrid318 ActualTZLiteralTerminalLift318
open ActualTZJointPolynomialForms318 ActualTZLiteralOffsetMajorants318

variable {m a b j : ℕ} {J : Type*} [Fintype J]

/-- One actual fixed exceptional prime product, uniform over all
genuine wraps. Surviving primes feed the signed-grid marginal
directly; the same typed bound feeds the numerical exceptional
tail. D,B are fixed finite source coefficient heights, not y,N. -/
theorem key_exists (S : Terminal m a b) (y D₀ : ℕ) (hy : 1≤y)
    (G : GoodTerminal S (primorial y)) (u v : J→Site a b j)
    (hDiff : ∀ i,u i≠v i) (A T B : ℤ) (hB : 0≤B)
    (Bnd : Bounds S A T) (hT : T≤A) (hA : A≤B*(primorial y:ℤ)^D₀) :
    ∃ K : ℕ,0<K ∧
      Real.log K≤(Fintype.card J:ℝ)*
        (Real.log (max (1:ℝ) (16*(cap m a:ℝ)*(B:ℝ)))+((D₀+1:ℕ):ℝ)*Real.log 4)*(y:ℝ) ∧
      ∀ p,¬p∣K→∀ i n (r r' : ℤ),
        MvPolynomial.map (Int.castRingHom (ZMod p))
          (py (physicalP S (primorial y) n r r' (u i) (v i)))≠0 := by
  classical
  have hW := primorial_pos y
  have hh (i : J) :=
    probe_height S (primorial y) hW G (u i) (v i) (hDiff i) A T Bnd hT
  choose x κ hc hSize hWrap using hh
  let K := exceptionalKey κ
  let B₀ := max (1:ℝ) (16*(cap m a:ℝ)*(B:ℝ))
  have hB₀ : 1≤B₀ := le_max_left _ _
  have hSize' (i : J) : ((κ i).natAbs:ℝ)≤B₀*(primorial y:ℝ)^(D₀+1) := by
    have h0 : 0≤(primorial y:ℤ) := by positivity
    have hL := mul_le_mul_of_nonneg_left hA
      (show (0:ℤ)≤16*(primorial y:ℤ)*(cap m a:ℤ) by positivity)
    have h := (hSize i).trans hL
    have h' : ((κ i).natAbs:ℝ)≤(16*(cap m a:ℝ)*(B:ℝ))*(primorial y:ℝ)^(D₀+1) := by
      have e : |κ i|≤(16*(cap m a:ℤ)*B)*(primorial y:ℤ)^(D₀+1) := by
        rw [pow_succ]
        nlinarith only [h]
      rw [←Int.natCast_natAbs] at e
      exact_mod_cast e
    exact h'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  refine ⟨K,exceptional_pos κ hc,log_key_with_wheel y (D₀+1) hy B₀ hB₀ κ hc hSize',?_⟩
  intro p hp i n r r'
  apply nonzero_from_probe p _ (x i) 0
  rw [hWrap i n r r']
  exact survives κ p hp i

end ActualTZPhysicalPairMarkerKey318
