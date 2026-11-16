module
public import OriginalNineChartAccess318
public section
noncomputable section
namespace LocalIndexRegularity318
open scoped Topology
set_option maxHeartbeats 1000000

/-- Neighborhood access along the actual nested integer residue classes.
The positive modulus precedes every later signed multiplier. -/
@[expose] def Regular {F : Type*} [TopologicalSpace F] (h₀ : ℤ) (f : ℤ → F) : Prop :=
  ∀ U : Set F, U∈𝓝 (f h₀) → ∃ L : ℕ, 0<L ∧ ∀ m : ℤ, f (h₀+(L:ℤ)*m)∈U

lemma refine_index (E N : ℕ) (hEN : E≤N) (h₀ m : ℤ) :
    h₀+4*(6:ℤ)^N*m=h₀+4*6^E*(6^(N-E)*m) := by
  have he := ActualFiniteOrbitAccess318.factor_power E N hEN 1 m
  simpa only [one_mul,mul_one] using congrArg (h₀+·) he

lemma constRegular {F : Type*} [TopologicalSpace F] (h₀ : ℤ) (x : F) :
    Regular h₀ (fun _ => x) := by
  intro U hU
  exact ⟨1,by norm_num,fun _ => mem_of_mem_nhds hU⟩

lemma comp {F G : Type*} [TopologicalSpace F] [TopologicalSpace G]
    {h₀ : ℤ} {f : ℤ → F} {g : F → G} (hf : Regular h₀ f) (hg : ContinuousAt g (f h₀)) :
    Regular h₀ (fun h => g (f h)) := by
  intro U hU
  obtain ⟨L,hL,haccess⟩ := hf (g ⁻¹' U) (hg hU)
  exact ⟨L,hL,haccess⟩

lemma pair {F G : Type*} [PseudoMetricSpace F] [PseudoMetricSpace G]
    {h₀ : ℤ} {f : ℤ → F} {g : ℤ → G} (hf : Regular h₀ f) (hg : Regular h₀ g) :
    Regular h₀ (fun h => (f h,g h)) := by
  intro U hU
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨Lf,hLf,hf'⟩ := hf (Metric.ball (f h₀) ε) (Metric.ball_mem_nhds _ hε)
  obtain ⟨Lg,hLg,hg'⟩ := hg (Metric.ball (g h₀) ε) (Metric.ball_mem_nhds _ hε)
  refine ⟨Lf*Lg,Nat.mul_pos hLf hLg,fun m => hball ?_⟩
  have hfm := hf' ((Lg:ℤ)*m)
  have hgm := hg' ((Lf:ℤ)*m)
  have hfi : h₀+(Lf:ℤ)*((Lg:ℤ)*m)=h₀+((Lf*Lg:ℕ):ℤ)*m := by push_cast; ring
  have hgi : h₀+(Lg:ℤ)*((Lf:ℤ)*m)=h₀+((Lf*Lg:ℕ):ℤ)*m := by push_cast; ring
  rw [hfi] at hfm
  rw [hgi] at hgm
  simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hfm hgm

lemma finite {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    {h₀ : ℤ} {f : ι → ℤ → F} (hf : ∀ i, Regular h₀ (f i)) :
    Regular h₀ (fun h i => f i h) := by
  classical
  intro U hU
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  have he : ∀ i, ∃ L : ℕ, 0<L ∧ ∀ m : ℤ, f i (h₀+(L:ℤ)*m)∈Metric.ball (f i h₀) ε :=
    fun i => hf i _ (Metric.ball_mem_nhds _ hε)
  choose L hL haccess using he
  let N := ∏ i, L i
  have hN : 0<N := Finset.prod_pos (fun i _ => hL i)
  have hdvd (i : ι) : L i∣N := Finset.dvd_prod_of_mem L (Finset.mem_univ i)
  refine ⟨N,hN,fun m => hball ?_⟩
  rw [Metric.mem_ball,dist_eq_norm]
  apply (pi_norm_lt_iff hε).mpr
  intro i
  obtain ⟨k,hk⟩ := hdvd i
  have hm := haccess i ((k:ℤ)*m)
  have hi : h₀+(L i:ℤ)*((k:ℤ)*m)=h₀+(N:ℤ)*m := by rw [hk]; push_cast; ring
  rw [hi] at hm
  simpa only [Metric.mem_ball,dist_eq_norm,Pi.sub_apply] using hm

section Field
variable {F : Type*} [NormedField F] {h₀ : ℤ} {f g : ℤ → F}
lemma add (hf : Regular h₀ f) (hg : Regular h₀ g) : Regular h₀ (fun h => f h+g h) :=
  comp (pair hf hg) (by fun_prop)
lemma sub (hf : Regular h₀ f) (hg : Regular h₀ g) : Regular h₀ (fun h => f h-g h) :=
  comp (pair hf hg) (by fun_prop)
lemma mul (hf : Regular h₀ f) (hg : Regular h₀ g) : Regular h₀ (fun h => f h*g h) :=
  comp (pair hf hg) (by fun_prop)
lemma neg (hf : Regular h₀ f) : Regular h₀ (fun h => -f h) := comp hf (by fun_prop)
lemma pow (hf : Regular h₀ f) (n : ℕ) : Regular h₀ (fun h => f h^n) := comp hf (by fun_prop)
lemma inv (hf : Regular h₀ f) (hn : f h₀≠0) : Regular h₀ (fun h => (f h)⁻¹) :=
  comp hf (continuousAt_inv₀ hn)
lemma div (hf : Regular h₀ f) (hg : Regular h₀ g) (hn : g h₀≠0) :
    Regular h₀ (fun h => f h/g h) := by
  simpa only [div_eq_mul_inv] using mul hf (inv hg hn)
end Field

/-- Every actual affine chart-index function has this regularity at2/3,
using the constructed local modulus rather than a caller-supplied premise. -/
lemma actual_chart (p : ℕ) [Fact p.Prime]
    (hb : ∀ e : ℕ, ∀ m : ℤ, ‖ActualOrbitLocalFilter318.error p (4*6^e*m)‖≤((p:ℝ)⁻¹)^e)
    (a b h₀ : ℤ) : Regular h₀ (fun h => ActualOrbitLocalFilter318.error p (a+b*h)) := by
  intro U hU
  obtain ⟨V,hVU,hV,hcenter⟩ := mem_nhds_iff.mp hU
  obtain ⟨E,hE⟩ := ActualOrbitTranslatedAccess318.access p hb (a+b*h₀) V hV hcenter
  refine ⟨4*6^E,by positivity,fun m => hVU ?_⟩
  have hm := hE (b*m)
  have hi : a+b*(h₀+((4*6^E:ℕ):ℤ)*m)=a+b*h₀+4*(6:ℤ)^E*(b*m) := by
    push_cast
    ring
  rw [hi]
  exact hm

lemma nat_progression {F : Type*} [TopologicalSpace F] {h₀ : ℕ} {f : ℤ → F}
    (hf : Regular (h₀:ℤ) f) (U : Set F) (hU : U∈𝓝 (f (h₀:ℤ))) :
    ∃ L : ℕ, 0<L ∧ ∀ h : ℕ, Nat.ModEq L h h₀ → f (h:ℤ)∈U := by
  obtain ⟨L,hL,haccess⟩ := hf U hU
  refine ⟨L,hL,?_⟩
  intro h hh
  obtain ⟨m,hm⟩ := Nat.modEq_iff_dvd.mp hh.symm
  have hi : (h:ℤ)=(h₀:ℤ)+(L:ℤ)*m := by linarith
  rw [hi]
  exact haccess m

end LocalIndexRegularity318
