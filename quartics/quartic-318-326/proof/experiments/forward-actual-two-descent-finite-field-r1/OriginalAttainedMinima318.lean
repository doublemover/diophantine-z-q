module
public import OriginalIntegerSquaredNorm318
public section
noncomputable section
namespace OriginalAttainedMinima318
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalDualDenominator318 OriginalIntegerSquaredNorm318
set_option maxHeartbeats 3000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A genuine shortest nonzero vector of the ACTUAL full Euclidean dual.
The construction minimizes an integer squared numerator length; it does
not ask the caller for an attained minimum. -/
theorem actual_shortest_dual (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    ∃ w : E, w∈Dual p κ t ∧ w≠0 ∧
      ∀ z : E, z∈Dual p κ t → z≠0 → ‖w‖≤‖z‖ := by
  classical
  let M := FixedSquarefreeCRT318.modulus p
  have hM := FixedSquarefreeCRT318.modulus_positive p hp
  let P : ℕ → Prop := fun n => ∃ v : Vector ℤ,
    v≠0 ∧ normalized M v∈Dual p κ t ∧ squaredLength v=n
  have hex : ∃ n, P n := by
    let v := multipleAxis M 0
    have hv : v≠0 := by
      intro hz
      have hh := congrArg Prod.fst hz
      have hh' : (M:ℤ)=0 := by simpa [v,multipleAxis,axis] using hh
      have : M=0 := by exact_mod_cast hh'
      omega
    have hd : normalized M v∈Dual p κ t := by
      apply (normalized_mem_dual_iff p hp κ t v).mpr
      intro u hu
      refine ⟨u.1,?_⟩
      simp [v,multipleAxis,axis,dot,M]
    exact ⟨squaredLength v,v,hv,hd,rfl⟩
  obtain ⟨v,hv,hmem,hscore⟩ := Nat.find_spec hex
  have hne : normalized M v≠0 := by
    intro hz
    apply hv
    apply normalized_injective M hM
    rwa [normalized_zero]
  refine ⟨normalized M v,hmem,hne,?_⟩
  intro z hz hzne
  obtain ⟨u,hu⟩ := actual_dual_numerator p hp κ t z hz
  have hune : u≠0 := by
    intro he
    apply hzne
    rw [←hu,he,normalized_zero]
  have humem : normalized M u∈Dual p κ t := by rwa [hu]
  have hlen : squaredLength v≤squaredLength u := by
    rw [hscore]
    exact Nat.find_min' hex ⟨u,hune,humem,rfl⟩
  rw [←hu]
  simp only [normalized,norm_smul]
  exact mul_le_mul_of_nonneg_left ((length_le_norm_iff v u).mp hlen) (norm_nonneg _)

/-- Original independent triples in the SAME standard Euclidean space. -/
@[expose] def IndependentTriple (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (v : Fin 3 → Vector ℤ) : Prop :=
  (∀ i, v i∈literalLattice p κ t) ∧ LinearIndependent ℝ (fun i => embed (v i))

lemma actual_independent_axes (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    IndependentTriple p κ t (multipleAxis (FixedSquarefreeCRT318.modulus p)) := by
  refine ⟨?_,multiple_axes_independent _ (FixedSquarefreeCRT318.modulus_positive p hp)⟩
  intro i
  exact modulus_multiple_mem p κ t (axis i)

/-- Construct the actual attained third Euclidean minimum together with
an attaining triple. Its universal minimality ranges over ALL original
independent triples, not a finite sample or a selected basis. -/
theorem actual_third_minimum (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    ∃ λ : ℝ, 0<λ ∧ ∃ v : Fin 3 → Vector ℤ,
      IndependentTriple p κ t v ∧ (∀ i, ‖embed (v i)‖≤λ) ∧
      ∀ u : Fin 3 → Vector ℤ, IndependentTriple p κ t u →
        ∀ r : ℝ, 0≤r → (∀ i, ‖embed (u i)‖≤r) → λ≤r := by
  classical
  let P : ℕ → Prop := fun n => ∃ v : Fin 3 → Vector ℤ,
    IndependentTriple p κ t v ∧ tripleScore v=n
  have hex : ∃ n, P n := ⟨_,_,actual_independent_axes p hp κ t,rfl⟩
  obtain ⟨v,hv,hscore⟩ := Nat.find_spec hex
  have hv0 : v 0≠0 := by
    intro hz
    apply hv.2.ne_zero 0
    rw [hz,embed_zero]
  have hlen : 0<squaredLength (v 0) :=
    Nat.pos_of_ne_zero (fun hz => hv0 ((squaredLength_zero_iff (v 0)).mp hz))
  have hscorepos : 0<tripleScore v := hlen.trans_le (length_le_score v 0)
  refine ⟨Real.sqrt (tripleScore v:ℝ),Real.sqrt_pos.mpr (by exact_mod_cast hscorepos),
    v,hv,norm_le_sqrt_score v,?_⟩
  intro u hu r hr hur
  have hmin : tripleScore v≤tripleScore u := by
    rw [hscore]
    exact Nat.find_min' hex ⟨u,hu,rfl⟩
  have hminR : (tripleScore v:ℝ)≤(tripleScore u:ℝ) := by exact_mod_cast hmin
  have hub := score_bound u r hr hur
  have hs := Real.sq_sqrt (show (0:ℝ)≤tripleScore v by positivity)
  nlinarith [Real.sqrt_nonneg (tripleScore v:ℝ)]

end OriginalAttainedMinima318
