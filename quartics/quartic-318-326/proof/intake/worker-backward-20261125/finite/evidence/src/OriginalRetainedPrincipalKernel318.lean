module

public import OriginalRetainedOriginalOrderGenerator318

@[expose] public section
noncomputable section

namespace OriginalRetainedPrincipalKernel318
open AlgebraicGeometry CategoryTheory
open OriginalLiteralMarkedRealPeriodColumns318
open OriginalRetainedF33ExponentialQuotient318
open OriginalRetainedOriginalOrderGenerator318
open scoped Matrix CategoryTheory.Obj CategoryTheory.MonObj

variable (α β : ℝ) (τ : ℂ) (ha : α^2=210) (hb : β^2=5) (hy : 0<τ.im)
variable {A₃₃ Y₃₃ : Scheme} (a₃₃ : A₃₃⟶Y₃₃) [GrpObj (Over.mk a₃₃)]
  {E : Type} [Field E] (σ : E→+*ℂ) (P : Spec (CommRingCat.of E)⟶Y₃₃)
local notation "M" => Additive (Points a₃₃ σ P)
variable (exp : Tangent→+M)
variable (riemann : Tangent →ₗ[ℝ] Tangent →ₗ[ℝ] ℝ)

abbrev column (i : Fin 4) : Tangent :=
  integerPeriods α β ha hb τ hy (Pi.single i 1)

abbrev entry (i : Fin 4) (z : Tangent) : ℝ :=
  riemann (column α β τ ha hb hy i) z

variable (integral :
  ∀ i (z : exp.ker), ∃ n : ℤ, (n:ℝ)=entry α β τ ha hb hy riemann i z.val)

variable (gram : ∀ r : Fin 4→ℝ,
  let z := actualColumns α β ha hb τ hy r
  entry α β τ ha hb hy riemann 0 z=2*r 1+r 3 ∧
  entry α β τ ha hb hy riemann 1 z= -2*r 0-r 2 ∧
  entry α β τ ha hb hy riemann 2 z=r 1 ∧
  entry α β τ ha hb hy riemann 3 z= -r 0)

include integral gram in
/-- The original polarization's integral pairing with the four actual
columns detects membership in the whole candidate integral lattice.
A finite-index superlattice cannot pass this test. -/
theorem every_actual_kernel_period (z : exp.ker) :
    ∃ n : IntegralLabels, integerPeriods α β ha hb τ hy n=z.val := by
  let e := actualColumns α β ha hb τ hy
  let r := e.symm z.val
  have same : e r=z.val := e.apply_symm_apply _
  obtain ⟨n₀,h₀⟩ := integral 0 z
  obtain ⟨n₁,h₁⟩ := integral 1 z
  obtain ⟨n₂,h₂⟩ := integral 2 z
  obtain ⟨n₃,h₃⟩ := integral 3 z
  have rr := gram r
  change entry α β τ ha hb hy riemann 0 (e r)=2*r 1+r 3 ∧
    entry α β τ ha hb hy riemann 1 (e r)= -2*r 0-r 2 ∧
    entry α β τ ha hb hy riemann 2 (e r)=r 1 ∧
    entry α β τ ha hb hy riemann 3 (e r)= -r 0 at rr
  rw [same] at rr
  obtain ⟨r₀,r₁,r₂,r₃⟩ := rr
  rw [←h₀] at r₀
  rw [←h₁] at r₁
  rw [←h₂] at r₂
  rw [←h₃] at r₃
  let n : IntegralLabels := ![-n₃,n₂,2*n₃-n₁,n₀-2*n₂]
  have rn : (fun i : Fin 4 => ((n i:ℤ):ℝ))=r := by
    funext i
    fin_cases i
    · change ((-n₃:ℤ):ℝ)=r 0
      push_cast
      linarith only [r₃]
    · exact r₂
    · change ((2*n₃-n₁:ℤ):ℝ)=r 2
      push_cast
      linarith only [r₁,r₃]
    · change ((n₀-2*n₂:ℤ):ℝ)=r 3
      push_cast
      linarith only [r₀,r₂]
  refine ⟨n,?_⟩
  change e (fun i => ((n i:ℤ):ℝ))=z.val
  rw [rn]
  exact same

variable (onPts : Fin 4→(M→+M))
variable (period : exp (normalizedGenerator τ)=0)
variable (natural : ∀ i z, exp (labelLieAction α β i z)=onPts i (exp z))

include period natural integral gram in
/-- Generate the true kernel of the *one* original marked exponential.
The transported Riemann pairing and one actual killed period replace a
whole-lattice equality assumption, not merely a covolume comparison. -/
def actualFrame : IntegralLabels ≃+ exp.ker :=
  frameFromActualGenerator α β τ ha hb hy a₃₃ σ P exp onPts period natural (by
    intro z
    obtain ⟨n,hn⟩ := every_actual_kernel_period α β τ ha hb hy
      a₃₃ σ P exp riemann integral gram z
    exact ⟨n,(DFunLike.congr_fun (whole_word_eq_columns α β τ ha hb hy) n).trans hn⟩)

include period natural integral gram in
theorem actualFrame_columns (i : Fin 4) :
    (actualFrame α β τ ha hb hy a₃₃ σ P exp riemann integral gram onPts period natural
      (Pi.single i 1)).val=column α β τ ha hb hy i := by
  unfold actualFrame
  apply frameFromActualGenerator_label

end OriginalRetainedPrincipalKernel318
