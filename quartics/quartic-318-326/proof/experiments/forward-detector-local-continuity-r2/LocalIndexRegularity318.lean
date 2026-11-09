module
public import OriginalNineChartAccess318
public section
noncomputable section
namespace LocalIndexRegularity318
open scoped Topology
set_option maxHeartbeats 1000000

/-- Neighborhood access along the actual nested integer residue classes.
The exponent precedes every later signed multiplier. -/
@[expose] def Regular {F : Type*} [TopologicalSpace F] (h₀ : ℤ) (f : ℤ → F) : Prop :=
  ∀ U : Set F, U∈𝓝 (f h₀) → ∃ E : ℕ, ∀ m : ℤ, f (h₀+4*6^E*m)∈U

lemma refine_index (E N : ℕ) (hEN : E≤N) (h₀ m : ℤ) :
    h₀+4*(6:ℤ)^N*m=h₀+4*6^E*(6^(N-E)*m) := by
  have he := ActualFiniteOrbitAccess318.factor_power E N hEN 1 m
  simpa only [one_mul,mul_one] using congrArg (h₀+·) he

lemma constRegular {F : Type*} [TopologicalSpace F] (h₀ : ℤ) (x : F) :
    Regular h₀ (fun _ => x) := by
  intro U hU
  exact ⟨0,fun _ => mem_of_mem_nhds hU⟩

lemma comp {F G : Type*} [TopologicalSpace F] [TopologicalSpace G]
    {h₀ : ℤ} {f : ℤ → F} {g : F → G} (hf : Regular h₀ f) (hg : ContinuousAt g (f h₀)) :
    Regular h₀ (fun h => g (f h)) := by
  intro U hU
  obtain ⟨E,hE⟩ := hf (g ⁻¹' U) (hg hU)
  exact ⟨E,hE⟩

lemma pair {F G : Type*} [PseudoMetricSpace F] [PseudoMetricSpace G]
    {h₀ : ℤ} {f : ℤ → F} {g : ℤ → G} (hf : Regular h₀ f) (hg : Regular h₀ g) :
    Regular h₀ (fun h => (f h,g h)) := by
  intro U hU
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨Ef,hEf⟩ := hf (Metric.ball (f h₀) ε) (Metric.ball_mem_nhds _ hε)
  obtain ⟨Eg,hEg⟩ := hg (Metric.ball (g h₀) ε) (Metric.ball_mem_nhds _ hε)
  refine ⟨Ef+Eg,fun m => hball ?_⟩
  have hfm := hEf ((6:ℤ)^((Ef+Eg)-Ef)*m)
  have hgm := hEg ((6:ℤ)^((Ef+Eg)-Eg)*m)
  rw [←refine_index Ef (Ef+Eg) (by omega)] at hfm
  rw [←refine_index Eg (Ef+Eg) (by omega)] at hgm
  simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hfm hgm

lemma finite {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    {h₀ : ℤ} {f : ι → ℤ → F} (hf : ∀ i, Regular h₀ (f i)) :
    Regular h₀ (fun h i => f i h) := by
  classical
  intro U hU
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  have he : ∀ i, ∃ E : ℕ, ∀ m : ℤ, f i (h₀+4*6^E*m)∈Metric.ball (f i h₀) ε :=
    fun i => hf i _ (Metric.ball_mem_nhds _ hε)
  choose E hE using he
  let N := ∑ i, E i
  have hEN (i : ι) : E i≤N :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨N,fun m => hball ?_⟩
  rw [Metric.mem_ball,dist_eq_norm]
  apply (pi_norm_lt_iff hε).mpr
  intro i
  have hm := hE i ((6:ℤ)^(N-E i)*m)
  rw [←refine_index (E i) N (hEN i)] at hm
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
  refine ⟨E,fun m => hVU ?_⟩
  have hm := hE (b*m)
  convert hm using 1 <;> congr 1 <;> ring

lemma nat_progression {F : Type*} [TopologicalSpace F] {h₀ : ℕ} {f : ℤ → F}
    (hf : Regular (h₀:ℤ) f) (U : Set F) (hU : U∈𝓝 (f (h₀:ℤ))) :
    ∃ E : ℕ, 0<4*6^E ∧ ∀ h : ℕ, Nat.ModEq (4*6^E) h h₀ → f (h:ℤ)∈U := by
  obtain ⟨E,hE⟩ := hf U hU
  refine ⟨E,by positivity,?_⟩
  intro h hh
  obtain ⟨m,hm⟩ := Nat.modEq_iff_dvd.mp hh.symm
  have hi : (h:ℤ)=(h₀:ℤ)+4*(6:ℤ)^E*m := by push_cast at hm; linarith
  rw [hi]
  exact hE m

end LocalIndexRegularity318
