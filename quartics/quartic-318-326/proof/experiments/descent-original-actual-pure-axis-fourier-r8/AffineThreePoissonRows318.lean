module
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Tactic
public section
noncomputable section
namespace AffineThreePoissonRows318
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

abbrev Cube := ℝ → ℝ → ℝ → ℂ

@[expose] def node (H c : ℝ) (n : ℤ) : ℝ := c+H*(n:ℝ)
@[expose] def freq (H : ℝ) (n : ℤ) : ℝ := (n:ℝ)/H
@[expose] def phase (x : ℝ) : ℂ := (Real.fourierChar x : ℂ)
@[expose] def coefficient (H c : ℝ) (n : ℤ) : ℂ :=
  ((H⁻¹:ℝ):ℂ)*phase (freq H n*c)

lemma phase_add (a b : ℝ) : phase (a+b)=phase a*phase b := by
  simp only [phase,AddChar.map_add_eq_mul,Circle.coe_mul]

lemma circle_phase (H c : ℝ) (n : ℤ) :
    fourier n ((c/H:ℝ):UnitAddCircle)=phase (freq H n*c) := by
  have htwo : ((2 : ℝ) : ℂ) = 2 := by
    simpa only [Nat.cast_ofNat] using (Complex.ofReal_natCast 2)
  rw [fourier_coe_apply,phase,Real.fourierChar_apply]
  simp only [freq,Complex.ofReal_one,div_one,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_intCast,htwo]
  congr 1
  ring

lemma node_offset (H c : ℝ) (hH : H≠0) (n : ℤ) :
    H*(c/H+(n:ℝ))=node H c n := by
  dsimp [node]
  field_simp [hH] <;> ring

lemma fourier_dilation (f : ℝ → ℂ) {H : ℝ} (hH : 0<H) (ξ : ℝ) :
    𝓕 (fun t => f (H*t)) ξ = ((H⁻¹:ℝ):ℂ)*𝓕 f (ξ/H) := by
  let g : ℝ → ℂ := fun u => Real.fourierChar (-(u*(ξ/H))) • f u
  calc
    _ = ∫ t : ℝ,g (H*t) := by
      rw [Real.fourier_real_eq]
      apply integral_congr_ae
      filter_upwards [] with t
      have he : -(H*t*(ξ/H))= -(t*ξ) := by field_simp [hH.ne'] <;> ring
      simp only [g,he]
    _ = _ := by
      rw [Measure.integral_comp_mul_left g H,abs_of_pos (inv_pos.mpr hH),Real.fourier_real_eq]
      simp only [g,Complex.real_smul]

def scaleEquiv (H : ℝ) (hH : H≠0) : ℝ ≃L[ℝ] ℝ :=
  (Units.mk0 H hH) • ContinuousLinearEquiv.refl ℝ ℝ

lemma scaleEquiv_apply (H : ℝ) (hH : H≠0) (t : ℝ) :
    scaleEquiv H hH t=H*t := by
  simp only [scaleEquiv,ContinuousLinearEquiv.smul_apply,ContinuousLinearEquiv.refl_apply,
    Units.val_mk0,smul_eq_mul]

/-- One true use of pinned Schwartz Poisson, including the positive phase
and the exact real Haar dilation, without any chart or project imports. -/
theorem affine_one (s : 𝓢(ℝ,ℂ)) {H : ℝ} (hH : 0<H) (c : ℝ) :
    (∑' n : ℤ,s (node H c n)) =
      ∑' k : ℤ, coefficient H c k * 𝓕 (s : ℝ → ℂ) (freq H k) := by
  let g : 𝓢(ℝ,ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleEquiv H hH.ne') s
  have hg (t : ℝ) : g t=s (H*t) := by
    simp only [g,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,scaleEquiv_apply]
  have hfun : (g : ℝ → ℂ) = fun t => s (H*t) := funext hg
  calc
    _ = ∑' n : ℤ,g (c/H+n) := by
      apply tsum_congr
      intro n
      rw [hg,node_offset H c hH.ne']
    _ = ∑' k : ℤ, 𝓕 g k*fourier k ((c/H:ℝ):UnitAddCircle) :=
      SchwartzMap.tsum_eq_tsum_fourier g (c/H)
    _ = _ := by
      apply tsum_congr
      intro k
      rw [SchwartzMap.fourier_coe,hfun,fourier_dilation _ hH,circle_phase]
      dsimp [coefficient,freq]
      ring

@[expose] def F₁ (W : Cube) : Cube := fun ξ y z => 𝓕 (fun x => W x y z) ξ
@[expose] def F₂ (W : Cube) : Cube := fun ξ η z => 𝓕 (fun y => F₁ W ξ y z) η
@[expose] def F₃ (W : Cube) : Cube := fun ξ η ζ => 𝓕 (fun z => F₂ W ξ η z) ζ

/-- Three ACTUAL partial transforms, not free row-wise outputs. A future
producer must construct these particular sampled Schwartz rows. -/
structure Rows (W : Cube) (H c₁ c₂ c₃ : ℝ) where
  row₁ : ℤ → ℤ → 𝓢(ℝ,ℂ)
  row₁_val : ∀ j k, (row₁ j k : ℝ → ℂ) = fun x => W x (node H c₂ j) (node H c₃ k)
  row₂ : ℤ → ℤ → 𝓢(ℝ,ℂ)
  row₂_val : ∀ i k, (row₂ i k : ℝ → ℂ) = fun y => F₁ W (freq H i) y (node H c₃ k)
  row₃ : ℤ → ℤ → 𝓢(ℝ,ℂ)
  row₃_val : ∀ i j, (row₃ i j : ℝ → ℂ) = fun z => F₂ W (freq H i) (freq H j) z

/-- Producer adapter: compact smooth one-variable sections suffice. This
does not assert compact smoothness of any partial integral without proof. -/
def Rows.ofCompact {W : Cube} {H c₁ c₂ c₃ : ℝ}
    (h₁ : ∀ j k, HasCompactSupport (fun x => W x (node H c₂ j) (node H c₃ k)) ∧
      ContDiff ℝ ∞ (fun x => W x (node H c₂ j) (node H c₃ k)))
    (h₂ : ∀ i k, HasCompactSupport (fun y => F₁ W (freq H i) y (node H c₃ k)) ∧
      ContDiff ℝ ∞ (fun y => F₁ W (freq H i) y (node H c₃ k)))
    (h₃ : ∀ i j, HasCompactSupport (fun z => F₂ W (freq H i) (freq H j) z) ∧
      ContDiff ℝ ∞ (fun z => F₂ W (freq H i) (freq H j) z)) :
    Rows W H c₁ c₂ c₃ where
  row₁ j k := (h₁ j k).1.toSchwartzMap (h₁ j k).2
  row₁_val _ _ := rfl
  row₂ i k := (h₂ i k).1.toSchwartzMap (h₂ i k).2
  row₂_val _ _ := rfl
  row₃ i j := (h₃ i j).1.toSchwartzMap (h₃ i j).2
  row₃_val _ _ := rfl

/-- Integrability of sampled rows is not an uncontrolled Fourier default:
it follows from each actual equality to a Schwartz function. -/
theorem rows_integrable {W : Cube} {H c₁ c₂ c₃ : ℝ} (S : Rows W H c₁ c₂ c₃) :
    (∀ j k, Integrable (fun x => W x (node H c₂ j) (node H c₃ k))) ∧
    (∀ i k, Integrable (fun y => F₁ W (freq H i) y (node H c₃ k))) ∧
    (∀ i j, Integrable (fun z => F₂ W (freq H i) (freq H j) z)) := by
  refine ⟨?_,?_,?_⟩
  · intro j k
    rw [←S.row₁_val]
    exact (S.row₁ j k).integrable
  · intro i k
    rw [←S.row₂_val]
    exact (S.row₂ i k).integrable
  · intro i j
    rw [←S.row₃_val]
    exact (S.row₃ i j).integrable

@[expose] def A₀ (W : Cube) (H c₁ c₂ c₃ : ℝ) (i j k : ℤ) : ℂ :=
  W (node H c₁ i) (node H c₂ j) (node H c₃ k)
@[expose] def A₁ (W : Cube) (H c₁ c₂ c₃ : ℝ) (i j k : ℤ) : ℂ :=
  coefficient H c₁ i * F₁ W (freq H i) (node H c₂ j) (node H c₃ k)
@[expose] def A₂ (W : Cube) (H c₁ c₂ c₃ : ℝ) (i j k : ℤ) : ℂ :=
  coefficient H c₁ i * coefficient H c₂ j * F₂ W (freq H i) (freq H j) (node H c₃ k)
@[expose] def A₃ (W : Cube) (H c₁ c₂ c₃ : ℝ) (i j k : ℤ) : ℂ :=
  coefficient H c₁ i * coefficient H c₂ j * coefficient H c₃ k *
    F₃ W (freq H i) (freq H j) (freq H k)

private theorem swap_tsum (f : ℤ → ℤ → ℂ)
    (h : Summable (fun p : ℤ×ℤ => f p.1 p.2)) :
    (∑' i : ℤ,∑' j : ℤ,f i j) = ∑' j : ℤ,∑' i : ℤ,f i j := by
  change Summable (Function.uncurry f) at h
  have h₁ (i : ℤ) : Summable (f i) :=
    h.comp_injective (show Function.Injective (fun j : ℤ => (i,j)) from
      fun _ _ he => congrArg Prod.snd he)
  have h₂ (j : ℤ) : Summable (fun i => f i j) :=
    h.comp_injective (show Function.Injective (fun i : ℤ => (i,j)) from
      fun _ _ he => congrArg Prod.fst he)
  exact (h.tsum_comm' h₁ h₂).symm

/-- Exact hybrid summability needed to move an unsummed primal variable
past one completed frequency, at the three specific swap sites. -/
structure SwapSums (W : Cube) (H c₁ c₂ c₃ : ℝ) : Prop where
  first : ∀ k, Summable (fun p : ℤ×ℤ => A₁ W H c₁ c₂ c₃ p.1 p.2 k)
  second : Summable (fun p : ℤ×ℤ => ∑' j : ℤ,A₂ W H c₁ c₂ c₃ p.1 j p.2)
  third : ∀ i, Summable (fun p : ℤ×ℤ => A₂ W H c₁ c₂ c₃ i p.1 p.2)

/-- Three direct applications of the pinned 1D theorem (no tensor padding,
no assumed three-dimensional Poisson identity). -/
theorem affine_three {W : Cube} {H c₁ c₂ c₃ : ℝ} (hH : 0<H)
    (S : Rows W H c₁ c₂ c₃) (U : SwapSums W H c₁ c₂ c₃) :
    (∑' k : ℤ,∑' j : ℤ,∑' i : ℤ,A₀ W H c₁ c₂ c₃ i j k) =
      ∑' i : ℤ,∑' j : ℤ,∑' k : ℤ,A₃ W H c₁ c₂ c₃ i j k := by
  have e₁ (j k : ℤ) :
      (∑' i : ℤ,A₀ W H c₁ c₂ c₃ i j k)=∑' i : ℤ,A₁ W H c₁ c₂ c₃ i j k := by
    simpa only [A₀,A₁,F₁,S.row₁_val j k] using affine_one (S.row₁ j k) hH c₁
  have e₂ (i k : ℤ) :
      (∑' j : ℤ,A₁ W H c₁ c₂ c₃ i j k)=∑' j : ℤ,A₂ W H c₁ c₂ c₃ i j k := by
    have h := congrArg (fun z : ℂ => coefficient H c₁ i*z) (affine_one (S.row₂ i k) hH c₂)
    simpa only [A₁,A₂,F₂,S.row₂_val i k,←tsum_mul_left,←mul_assoc] using h
  have e₃ (i j : ℤ) :
      (∑' k : ℤ,A₂ W H c₁ c₂ c₃ i j k)=∑' k : ℤ,A₃ W H c₁ c₂ c₃ i j k := by
    have h := congrArg (fun z : ℂ => (coefficient H c₁ i*coefficient H c₂ j)*z)
      (affine_one (S.row₃ i j) hH c₃)
    simpa only [A₂,A₃,F₃,S.row₃_val i j,←tsum_mul_left,←mul_assoc] using h
  calc
    _ = ∑' k : ℤ,∑' i : ℤ,∑' j : ℤ,A₁ W H c₁ c₂ c₃ i j k := by
      apply tsum_congr
      intro k
      simp_rw [e₁]
      exact (swap_tsum _ (U.first k)).symm
    _ = ∑' k : ℤ,∑' i : ℤ,∑' j : ℤ,A₂ W H c₁ c₂ c₃ i j k := by simp_rw [e₂]
    _ = ∑' i : ℤ,∑' k : ℤ,∑' j : ℤ,A₂ W H c₁ c₂ c₃ i j k :=
      (swap_tsum _ U.second).symm
    _ = ∑' i : ℤ,∑' j : ℤ,∑' k : ℤ,A₂ W H c₁ c₂ c₃ i j k := by
      apply tsum_congr
      intro i
      exact (swap_tsum _ (U.third i)).symm
    _ = _ := by simp_rw [e₃]

/-- Product of the three affine coefficients, with positive offset phase. -/
theorem coefficient_product (H c₁ c₂ c₃ : ℝ) (i j k : ℤ) :
    coefficient H c₁ i*coefficient H c₂ j*coefficient H c₃ k =
      (((H^3)⁻¹:ℝ):ℂ)*phase (((i:ℝ)*c₁+(j:ℝ)*c₂+(k:ℝ)*c₃)/H) := by
  have hp : (((H⁻¹:ℝ):ℂ)^3)=(((H^3)⁻¹:ℝ):ℂ) := by
    rw [←Complex.ofReal_pow,inv_pow]
  have hs : (freq H i*c₁+freq H j*c₂)+freq H k*c₃ =
      ((i:ℝ)*c₁+(j:ℝ)*c₂+(k:ℝ)*c₃)/H := by
    simp only [freq,div_eq_mul_inv]
    ring
  calc
    _ = (((H⁻¹:ℝ):ℂ)^3)*((phase (freq H i*c₁)*phase (freq H j*c₂))*phase (freq H k*c₃)) := by
      simp only [coefficient]
      ring
    _ = _ := by rw [hp,←phase_add,←phase_add,hs]

/-- The exact chart offset c=(b+M j₀)/B and H=Mq/B. The common
physical phase and rational residue phase separate before averaging. -/
theorem chart_phase (B M q b₁ b₂ b₃ j₁ j₂ j₃ : ℝ)
    (hB : B≠0) (hM : M≠0) (hq : q≠0) (i j k : ℤ) :
    phase (((i:ℝ)*((b₁+M*j₁)/B)+(j:ℝ)*((b₂+M*j₂)/B)+
      (k:ℝ)*((b₃+M*j₃)/B))/(M*q/B)) =
    phase (((i:ℝ)*b₁+(j:ℝ)*b₂+(k:ℝ)*b₃)/(M*q)) *
      phase (((i:ℝ)*j₁+(j:ℝ)*j₂+(k:ℝ)*j₃)/q) := by
  rw [←phase_add]
  congr 1
  field_simp [hB,hM,hq] <;> ring

/-- This is the SAME positive character used by the finite conductor
calculation, with the integer representative allowed to be negative. -/
lemma rational_phase (q : ℕ) [NeZero q] (a : ℤ) :
    phase ((a:ℝ)/q)=ZMod.stdAddChar (a:ZMod q) := by
  rw [phase,Real.fourierChar_apply,ZMod.stdAddChar_coe]
  congr 1
  push_cast <;> ring

theorem chart_phase_mod (B M : ℝ) (q : ℕ) [NeZero q] (b₁ b₂ b₃ : ℝ)
    (j₁ j₂ j₃ : ℤ) (hB : B≠0) (hM : M≠0) (i j k : ℤ) :
    phase (((i:ℝ)*((b₁+M*(j₁:ℝ))/B)+(j:ℝ)*((b₂+M*(j₂:ℝ))/B)+
      (k:ℝ)*((b₃+M*(j₃:ℝ))/B))/(M*(q:ℝ)/B)) =
    phase (((i:ℝ)*b₁+(j:ℝ)*b₂+(k:ℝ)*b₃)/(M*(q:ℝ))) *
      ZMod.stdAddChar ((i*j₁+j*j₂+k*j₃ : ℤ):ZMod q) := by
  have hq : (q:ℝ)≠0 := by exact_mod_cast (NeZero.ne q)
  rw [chart_phase _ _ _ _ _ _ _ _ _ hB hM hq]
  congr 1
  simpa only [Int.cast_add,Int.cast_mul] using rational_phase q (i*j₁+j*j₂+k*j₃)

end AffineThreePoissonRows318
