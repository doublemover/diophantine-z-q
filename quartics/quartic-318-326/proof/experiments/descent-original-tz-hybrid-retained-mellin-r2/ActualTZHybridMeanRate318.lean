module
public import ActualTZHybridMeanFiniteBound318
public import ActualTZOrdinaryCollisionCutoffRate318
public import ActualTZOrdinaryBoundaryDecay318
public import ActualTZLiteralWindowEventual318
public import ActualTZActualFixedCutoffRate318
import all ActualTZHybridMeanCorrection318
import all ActualTZHybridMeanAverage318
import all ActualTZHybridCanonicalWrap318
public section
noncomputable section
namespace ActualTZHybridMeanRate318
open scoped BigOperators Topology
open Filter MeasureTheory
open ActualTZHybridCanonicalWrap318
open ActualTZHybridGrid318 (dim)
open ActualTZHybridCanonicalWrap318.Context (Pair)
open ActualTZHybridMeanAverage318 ActualTZHybridMeanCorrection318
open ActualTZHybridMeanFiniteBound318
open ActualTZLiteralSchwartz318 ActualTZLiteralOrdinaryBound318 ActualTZActualFixedCutoffRate318
open ActualTZOrdinaryNumericDensity318 ActualTZOrdinaryCollisionCutoffRate318 ActualTZOrdinaryLeadingDecay318
open ActualTZOrdinaryBoundaryScalar318 ActualTZOrdinaryBoundaryDecay318 ActualTZLiteralWindowEventual318
open ActualTZPhysicalCorrectionBound318 ActualTZPhysicalEulerSplit318
open ActualTZCollisionPrimePartition318 ActualTZWeightedPrimePrefix318
open ActualTZCanonicalWrapFibres318

variable {I : Type*} [Fintype I] [DecidableEq I] {a t s : ℕ}

@[expose] def keyC (I : Type*) [Fintype I] (c : ℕ) : ℝ :=
  ((2*c+1)^Fintype.card I : ℕ)

@[expose] def pairC (I : Type*) [Fintype I] [DecidableEq I] (a t s : ℕ) : ℝ :=
  (Fintype.card (Pair I):ℝ)*(dim a t s:ℝ)*2

@[expose] def totalC (I : Type*) [Fintype I] [DecidableEq I] (a t s c : ℕ) : ℝ :=
  keyC I c * ((2:ℝ)^(dim a t s)*pairC I a t s)

@[expose] def scales (X : Context a t s I) (y N : ℕ) (ell : ℝ) : Prop :=
  X.y=y ∧ X.N=N ∧ X.n=N/primorial y ∧ ell*(N:ℝ)^((1:ℝ)/2)≤X.minLen

private theorem key_eq (X : Context a t s I) (c : ℕ) (hc : X.cap=c) :
    (Fintype.card X.Keys:ℝ)=keyC I c := by
  unfold keyC
  rw [←hc]
  exact_mod_cast card_wrap (I:=I) X.cap

theorem budget_rate (X : Context a t s I) (y N P : ℕ) (ell : ℝ) (h : scales X y N ell) (c : ℕ) (hc : X.cap=c) :
    budget X P =
      let G := goodConst (Fintype.card I)*(∑ q∈offWheel (primorial y) P,(1/(q:ℝ))^2)+
        badConst (Fintype.card I)*extra (primorial y) P X.keyPrime
      (Real.exp G-1)+Real.exp G*(∑ q∈regular y N X.keyPrime,
        prefixWeight (badConst (Fintype.card I)) q*(totalC I a t s c*(1/(q:ℝ)+1/(X.minLen:ℝ)))) := by
  obtain ⟨hY,hN,_,_⟩ := h
  unfold budget density
  rw [hY,hN,key_eq X c hc]
  have HE : keyC I c*(Fintype.card (Pair I):ℝ)*((2:ℝ)^(dim a t s)*(dim a t s:ℝ)*2)=totalC I a t s c := by
    unfold totalC pairC
    ring
  rw [HE]

theorem three_errors (X : Context a t s I) (y N : ℕ) (ell σ α B : ℝ)
    (hd : 0<ell) (h : scales X y N ell) (c : ℕ) (hc : X.cap=c) (hR : 1<(X.n:ℝ)^σ) (ha : 0≤α) (ha' : α≤1) (hB : 0≤B) :
    envelope (Fintype.card I) ((X.n:ℝ)^σ) B*lostBound X+
      intervalError X α ((X.n:ℝ)^σ) B+lostBound X≤
      remainder (Fintype.card I) σ B (keyC I c*(1+pairC I a t s/ell)) (X.n:ℝ) := by
  obtain ⟨hY,hN,hn,hM⟩ := h
  have h1 : (1:ℝ)≤X.n := by exact_mod_cast X.hn
  have hnN : X.n≤N := by rw [hn]; exact Nat.div_le_self _ _
  have hScale := (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
    (by positivity : (0:ℝ)≤X.n) (by exact_mod_cast hnN)
    (show (0:ℝ)≤1/2 by norm_num)) hd.le).trans hM
  have hLost : lostBound X≤(keyC I c*(1+pairC I a t s/ell))*short (X.n:ℝ) := by
    unfold lostBound
    rw [key_eq X c hc]
    have H := lost_scalar (X.n:ℝ) X.minLen ell (keyC I c) (pairC I a t s)
      h1 hd hScale (by unfold keyC; positivity) (by unfold pairC; positivity)
    calc
      _ = keyC I c*(short (X.n:ℝ)+pairC I a t s/(X.minLen:ℝ)) := by
        simp only [short,neg_div,pairC,div_eq_mul_inv]
        ring
      _ ≤ _ := H
  exact total_le _ σ B _ _ _ _ h1 hR hLost (interval_scalar _ α _ B _ h1 hR ha ha' hB)

/-- For a fixed actual hybrid slot type, old fine dimension and wrap cap,
choose the N threshold before the actual signed context and
Euler reference are presented. -/
theorem mask_rate (C : Cutoff) (hχ : (∫ t in (0:ℝ)..1,|deriv C.χ t|^2)=1)
    (B σ : ℝ) (hB : ∀ t,|C.χ t|≤B) (hσ : 0<σ) (D c : ℕ)
    (hsmall : 8*(Fintype.card I:ℝ)*σ<1) :
    ∃ e : ℕ→ℝ,Tendsto e atTop (𝓝 0) ∧ (∀ y,0≤e y) ∧
    ∃ y₀ : ℕ,∀ y≥y₀,∀ ε>0,∀ ell>0,∃ N₀ : ℕ,∀ N≥N₀,
      ∀ (X : Context a t s I),scales X y N ell→X.cap=c→X.q≤(primorial y)^D→
      |original X (α (primorial y)) ((X.n:ℝ)^σ) C.χ-1|≤e y+ε := by
  let k := Fintype.card I
  let L := totalC I a t s c
  let Z := kernelSize C I
  have hZ : 0≤Z := kernel_nonneg C
  let A : ℝ := ((D+1:ℕ):ℝ)*Real.log 4
  let e (y : ℕ) := Z*|leading k A L y|
  have hLeading : Tendsto (leading k A L) atTop (𝓝 0) := leading_tendsto _ _ _
  have he : Tendsto e atTop (𝓝 0) := by
    have H := (tendsto_const_nhds : Tendsto (fun _ : ℕ=>Z) atTop (𝓝 Z)).mul hLeading.abs
    simpa only [e,abs_zero,mul_zero] using H
  have hL : 0≤L := by unfold L totalC keyC pairC; positivity
  obtain ⟨y₀,_,hy₀⟩ := fixed_cutoff k A L hL
  refine ⟨e,he,fun _=>mul_nonneg hZ (abs_nonneg _),y₀,?_⟩
  intro y hy ε hε ell hd
  have hW : 0<primorial y := primorial_pos _
  have hε₃ : 0<ε/3 := by positivity
  have hεZ : 0<ε/(3*(1+Z)) := by positivity
  obtain ⟨N₁,hN₁⟩ := hy₀ y hy _ hεZ ell hd
  obtain ⟨L₀,hLone,hLit⟩ := finite_bound (I:=I) C hχ B hB y (ε/3) hε₃
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp ((logarithmic_growth (primorial y) hW σ hσ).eventually_ge_atTop L₀)
  let Q := keyC I c*(1+pairC I a t s/ell)
  have hNat := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ=>(n:ℝ)) atTop atTop).comp
    (natural_growth (primorial y) hW)
  have hD := (total_tendsto k σ B Q hsmall).comp hNat
  obtain ⟨N₃,hN₃⟩ := eventually_atTop.mp (hD.eventually (gt_mem_nhds hε₃))
  refine ⟨max (max N₁ N₂) N₃,?_⟩
  intro N hN X hX hc hq
  have hNA : N₁≤N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNB : N₂≤N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNC : N₃≤N := (le_max_right _ _).trans hN
  let R := (X.n:ℝ)^σ
  have hlog : L₀≤Real.log R := by unfold R; rw [hX.2.2.1]; exact hN₂ _ hNB
  have hR : 1<R := by
    by_contra hr
    have hr' : R≤1 := le_of_not_gt hr
    have hR₀ : (0:ℝ)<R := Real.rpow_pos_of_pos (by exact_mod_cast X.hn) _
    have hh : Real.log R≤0 := by simpa only [Real.log_one] using Real.log_le_log hR₀ hr'
    linarith only [hlog,hLone,hh]
  obtain ⟨P,_,_,_,H⟩ := hLit X hX.1 R hR hlog
  have hq' : X.q≤(primorial X.y)^D := hX.1.symm ▸ hq
  obtain ⟨hKpos,hKlog⟩ := log_marker X.y D X.q X.hq hq'
  have hMarker : Real.log (X.keyPrime:ℝ)≤A*(y:ℝ) := by
    simpa only [ActualTZHybridCanonicalWrap318.Context.keyPrime,hX.1,A] using hKlog
  have hCorrection := hN₁ N hNA (primorial y) (P+1) X.keyPrime hKpos
    (fun q hp hy=>hp.dvd_primorial_iff.2 hy) hMarker (X.minLen:ℝ) hX.2.2.2
  have hEuler : budget X (P+1)≤leading k A L y+ε/(3*(1+Z)) := by
    rw [budget_rate X y N (P+1) ell hX c hc]
    exact hCorrection
  have hα := α_bounds (primorial y) hW
  have hB₀ := (abs_nonneg _).trans (hB 0)
  have hBoundary : envelope k R B*lostBound X+
      intervalError X (α (primorial y)) R B+lostBound X≤remainder k σ B Q (X.n:ℝ) :=
    three_errors X y N ell σ (α (primorial y)) B hd hX c hc hR hα.1 hα.2 hB₀
  have hSmall : remainder k σ B Q (X.n:ℝ)≤ε/3 := by
    rw [hX.2.2.1]
    exact (hN₃ N hNC).le
  have hEuler' := mul_le_mul_of_nonneg_left hEuler hZ
  have hTail : Z*(ε/(3*(1+Z)))≤ε/3 := by
    have hp : 0<1+Z := by positivity
    have hu : Z/(1+Z)≤1 := (div_le_one hp).2 (by linarith)
    have H := mul_le_mul_of_nonneg_right hu (show 0≤ε/3 by positivity)
    calc
      _ = (Z/(1+Z))*(ε/3) := by field_simp [hp.ne'] <;> ring
      _ ≤ _ := by simpa only [one_mul] using H
  have hAbs := mul_le_mul_of_nonneg_left (le_abs_self (leading k A L y)) hZ
  change |original X (α (primorial y)) R C.χ-1|≤_
  change _ ≤ envelope k R B*lostBound X+intervalError X (α (primorial y)) R B+
    Z*budget X (P+1)+ε/3+lostBound X at H
  change _ ≤ Z*|leading k A L y|+ε
  nlinarith only [H,hBoundary,hSmall,hEuler',hTail,hAbs]

end ActualTZHybridMeanRate318
