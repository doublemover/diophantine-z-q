module
public import ActualTZBoundedQuadraticProbe318
public import ActualTZRelabelPhysicalGrid318
public import ActualTZPeeledWheelWindow318
import all ActualTZRelabelPhysicalGrid318
import all ActualTZLiteralProbeSpecialization318
public section
noncomputable section
namespace ActualTZActualPhysicalProbeHeight318
open ActualTZBoundedQuadraticProbe318 ActualTZRelabelPhysicalGrid318
open ActualTZLiteralTerminalLift318 ActualTZLiteralNonlinearDistinct318 ActualTZFixedWrapMarkers318
open ActualTZPeeledWheelWindow318 ActualTZLiteralOffsetMajorants318 ActualTZLiteralProbeSpecialization318
open ActualTZJointPolynomialForms318
open scoped BigOperators

variable {m a b j : ℕ}

private theorem eval_cap (S : Terminal m a b) (u : Site a b j)
    (A T : ℤ) (hT : T≤A) (B : Bounds S A T) (x : Fin (D m a j)→ℤ)
    (hx : ∀ i,|x i|≤1) :
    |MvPolynomial.eval x (py (siteP S u))|≤(cap m a:ℤ)*(4*A) := by
  let F := x ∘ finAxis m a j
  let h (i : Fin m) := F (.inl i)
  let k (q : Bool) (i : Fin a) := F (.inr (.inl (q,i)))
  let c (v : Fin j) := F (.inr (.inr v))
  have hF : x ∘ finAxis m a j=rawGrid h k c := by
    funext t
    rcases t with h'|⟨e,i⟩|v <;> rfl
  rw [py_eval,hF,eval_raw]
  exact probe_offset_bound S u A T B hT h k c
    (fun i=>(hx _).trans (by norm_num)) (fun q i=>(hx _).trans (by norm_num))
    (fun i=>(hx _).trans (by norm_num))

/-- Same nonzero integer diagnostic mark on every physical wrap,
with an actual effective source coefficient norm. There is no
coefficient-choice height oracle or assumption of positivity of
the polynomial on its sample support. -/
theorem probe_height (S : Terminal m a b) (W : ℕ) (hW : 0<W) (G : GoodTerminal S W)
    (u v : Site a b j) (huv : u≠v) (A T : ℤ) (B : Bounds S A T) (hT : T≤A) :
    ∃ x : Fin (D m a j)→ℤ,∃ κ : ℤ, κ≠0 ∧ |κ|≤16*(W:ℤ)*(cap m a:ℤ)*A ∧
      ∀ n (r r' : ℤ),
        MvPolynomial.eval x (py (physicalP S W n r r' u v))-
          MvPolynomial.eval 0 (py (physicalP S W n r r' u v))=κ := by
  let P := py (siteP S u-siteP S v)
  have hDeg : P.totalDegree≤2 := (py_degree _).trans
    (ActualTZDegreeTwoAlgebra318.subD _ _ 2 (siteD S u) (siteD S v))
  have hChange : ∃ x y : Fin (D m a j)→ℤ,MvPolynomial.eval x P≠MvPolynomial.eval y P := by
    obtain ⟨x,y,h⟩ := different_sites G u v huv
    refine ⟨x ∘ (finAxis m a j).symm,y ∘ (finAxis m a j).symm,?_⟩
    have hx : (x ∘ (finAxis m a j).symm) ∘ finAxis m a j=x := by
      funext i
      simp only [Function.comp_apply,Equiv.symm_apply_apply]
    have hy : (y ∘ (finAxis m a j).symm) ∘ finAxis m a j=y := by
      funext i
      simp only [Function.comp_apply,Equiv.symm_apply_apply]
    simpa only [P,py_eval,hx,hy] using h
  obtain ⟨x,hx,hxNe⟩ := bounded_probe P hDeg hChange
  let g := MvPolynomial.eval x P-MvPolynomial.eval 0 P
  let κ := (W:ℤ)*g
  have hWG : (W:ℤ)≠0 := by exact_mod_cast hW.ne'
  have hg : g≠0 := sub_ne_zero.mpr hxNe
  have Hₓ (z : Fin (D m a j)→ℤ) (hz : ∀ i,|z i|≤1) :
      |MvPolynomial.eval z P|≤2*((cap m a:ℤ)*(4*A)) := by
    have H := abs_sub_le (MvPolynomial.eval z (py (siteP S u))) (MvPolynomial.eval z (py (siteP S v)))
    simp only [P,py_eval,map_sub] at H ⊢
    have H₁ := eval_cap S u A T hT B z hz
    have H₂ := eval_cap S v A T hT B z hz
    simp only [py_eval] at H₁ H₂
    linarith only [H,H₁,H₂]
  have hG : |g|≤4*((cap m a:ℤ)*(4*A)) := by
    have hS := abs_sub_le (MvPolynomial.eval x P) (MvPolynomial.eval 0 P)
    have H₁ := Hₓ x hx
    have H₂ := Hₓ 0 (fun _=>by simp)
    change |MvPolynomial.eval x P-MvPolynomial.eval 0 P|≤_
    linarith only [hS,H₁,H₂]
  have hK : |κ|≤16*(W:ℤ)*(cap m a:ℤ)*A := by
    dsimp only [κ]
    rw [abs_mul,abs_of_nonneg (by positivity : (0:ℤ)≤W)]
    exact (mul_le_mul_of_nonneg_left hG (by positivity)).trans_eq (by ring)
  refine ⟨x,κ,mul_ne_zero hWG hg,hK,?_⟩
  intro n r r'
  simp only [py_eval,physical_eval S W n 0,P,g,κ,map_sub]
  ring

end ActualTZActualPhysicalProbeHeight318
