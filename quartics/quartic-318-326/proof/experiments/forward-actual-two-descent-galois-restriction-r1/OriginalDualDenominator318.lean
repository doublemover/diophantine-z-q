module
public import OriginalEuclideanLattice318
public section
noncomputable section
namespace OriginalDualDenominator318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318
set_option maxHeartbeats 2500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def normalized (M : ℕ) (v : Vector ℤ) : E := (M:ℝ)⁻¹ • embed v

lemma normalized_inner (M : ℕ) (v u : Vector ℤ) :
    ⟪normalized M v,embed u⟫=(dot v u:ℝ)/(M:ℝ) := by
  rw [normalized,real_inner_smul_left,inner_embed]
  ring

lemma normalized_zero (M : ℕ) : normalized M 0=0 := by simp only [normalized,embed_zero,smul_zero]

lemma normalized_injective (M : ℕ) (hM : 0<M) : Function.Injective (normalized M) := by
  have hm : (M:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hM)
  intro v u he
  apply embed_injective
  have hh := congrArg (fun w : E => (M:ℝ) • w) he
  simpa only [normalized,smul_smul,mul_inv_cancel₀ hm,one_smul] using hh

/-- Exact denominator normalization in the STANDARD Euclidean metric.
The numerator is in the original integer coordinates, and M is unchanged. -/
theorem normalized_mem_dual_iff (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (v : Vector ℤ) :
    normalized (FixedSquarefreeCRT318.modulus p) v∈Dual p κ t ↔
      ∀ u : Vector ℤ, u∈literalLattice p κ t → (FixedSquarefreeCRT318.modulus p:ℤ)∣dot v u := by
  let M := FixedSquarefreeCRT318.modulus p
  have hM : (M:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (FixedSquarefreeCRT318.modulus_positive p hp))
  rw [dual_iff]
  constructor
  · intro h u hu
    obtain ⟨n,hn⟩ := h u hu
    rw [normalized_inner] at hn
    refine ⟨n,?_⟩
    have he : (dot v u:ℝ)=(M:ℝ)*(n:ℝ) := by
      have hh := (div_eq_iff hM).mp hn
      simpa only [mul_comm] using hh
    exact_mod_cast he
  · intro h u hu
    obtain ⟨n,hn⟩ := h u hu
    refine ⟨n,?_⟩
    rw [normalized_inner,hn,Int.cast_mul]
    change (M:ℝ)*(n:ℝ)/(M:ℝ)=(n:ℝ)
    field_simp [hM]

/-- Testing the actual modulus times each coordinate axis constructs
integer coordinates for M*w. This excludes hidden saturation/denominator
assumptions about the Euclidean dual. -/
theorem actual_dual_numerator (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (w : E) (hw : w∈Dual p κ t) :
    ∃ v : Vector ℤ, normalized (FixedSquarefreeCRT318.modulus p) v=w := by
  let M := FixedSquarefreeCRT318.modulus p
  have hm : (M:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (FixedSquarefreeCRT318.modulus_positive p hp))
  have h := (dual_iff p κ t w).mp hw
  have hx := modulus_multiple_mem p κ t (1,0,0)
  have hz := modulus_multiple_mem p κ t (0,1,0)
  have hw' := modulus_multiple_mem p κ t (0,0,1)
  obtain ⟨a,ha⟩ := h _ hx
  obtain ⟨b,hb⟩ := h _ hz
  obtain ⟨c,hc⟩ := h _ hw'
  have ha' : w 0*(M:ℝ)=(a:ℝ) := by simpa [inner_embed_right,M] using ha
  have hb' : w 1*(M:ℝ)=(b:ℝ) := by simpa [inner_embed_right,M] using hb
  have hc' : w 2*(M:ℝ)=(c:ℝ) := by simpa [inner_embed_right,M] using hc
  refine ⟨(a,b,c),?_⟩
  ext i
  fin_cases i
  · change (M:ℝ)⁻¹*(a:ℝ)=w 0
    rw [←ha']
    field_simp [hm]
  · change (M:ℝ)⁻¹*(b:ℝ)=w 1
    rw [←hb']
    field_simp [hm]
  · change (M:ℝ)⁻¹*(c:ℝ)=w 2
    rw [←hc']
    field_simp [hm]

/-- Exact parameterization of the WHOLE actual Euclidean dual, not just
one direction of an embedding. -/
theorem actual_dual_iff (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (w : E) :
    w∈Dual p κ t ↔ ∃ v : Vector ℤ,
      (∀ u : Vector ℤ, u∈literalLattice p κ t → (FixedSquarefreeCRT318.modulus p:ℤ)∣dot v u) ∧
      normalized (FixedSquarefreeCRT318.modulus p) v=w := by
  constructor
  · intro hw
    obtain ⟨v,hv⟩ := actual_dual_numerator p hp κ t w hw
    refine ⟨v,?_,hv⟩
    apply (normalized_mem_dual_iff p hp κ t v).mp
    rwa [hv]
  · rintro ⟨v,hv,rfl⟩
    exact (normalized_mem_dual_iff p hp κ t v).mpr hv

end OriginalDualDenominator318
