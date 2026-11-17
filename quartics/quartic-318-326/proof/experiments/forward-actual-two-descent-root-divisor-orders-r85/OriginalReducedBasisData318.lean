module
public import OriginalGlobalBadSource318
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace OriginalReducedBasisData318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalFullEuclideanLattice318 OriginalIntegerSquaredNorm318 OriginalAttainedMinima318
set_option maxHeartbeats 3500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open OriginalSequentialMinima318

/-- Construct an ACTUAL shortest nonzero first vector, shortest second
outside its line, and shortest third outside their plane. The pair has
the explicit reduction inequality needed by the actual rounding bound.
No reduced basis or successive-minimum witness is supplied by the caller. -/
theorem actual_full_sequential_data (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    ∃ u v w : Vector ℤ,
      IndependentTriple p κ t ![u,v,w] ∧
      ‖embed u‖≤‖embed v‖ ∧ ‖embed v‖≤‖embed w‖ ∧
      |⟪embed u,embed v⟫|≤‖embed u‖^2/2 ∧
      embed v∉Submodule.span ℝ (Set.range (fun _ : Fin 1 => embed u)) ∧
      embed w∉Submodule.span ℝ (Set.range ![embed u,embed v]) ∧
      (∀ z : Vector ℤ, z∈literalLattice p κ t → embed z≠0 → ‖embed u‖≤‖embed z‖) ∧
      (∀ z : Vector ℤ, z∈literalLattice p κ t →
        embed z∉Submodule.span ℝ (Set.range (fun _ : Fin 1 => embed u)) → ‖embed v‖≤‖embed z‖) ∧
      ∀ z : Vector ℤ, z∈literalLattice p κ t →
        embed z∉Submodule.span ℝ (Set.range ![embed u,embed v]) → ‖embed w‖≤‖embed z‖ := by
  classical
  obtain ⟨u,hu,hun,humin⟩ := shortest_outside p hp κ t ⊥ bot_ne_top
  have hu0 : embed u≠0 := by simpa only [Submodule.mem_bot] using hun
  let S1 : Submodule ℝ E := Submodule.span ℝ (Set.range (fun _ : Fin 1 => embed u))
  obtain ⟨v,hv,hvn,hvmin⟩ := shortest_outside p hp κ t S1
    (short_range_proper (fun _ : Fin 1 => embed u) (by decide))
  have huS : embed u∈S1 := Submodule.subset_span ⟨0,rfl⟩
  have hv0 : embed v≠0 := by intro hz; apply hvn; rw [hz]; exact S1.zero_mem
  have huv := humin v hv (by simpa only [Submodule.mem_bot] using hv0)
  have hpair : LinearIndependent ℝ ![embed u,embed v] := by
    apply (LinearIndependent.pair_iff' hu0).mpr
    intro a ha
    apply hvn
    rw [←ha]
    exact S1.smul_mem a huS
  let S2 : Submodule ℝ E := Submodule.span ℝ (Set.range ![embed u,embed v])
  obtain ⟨w,hw,hwn,hwmin⟩ := shortest_outside p hp κ t S2
    (short_range_proper ![embed u,embed v] (by decide))
  have h12 : S1≤S2 := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact Submodule.subset_span ⟨0,rfl⟩
  have hw1 : embed w∉S1 := fun h => hwn (h12 h)
  have hvw := hvmin w hw hw1
  have hplus : embed (v+u)∉S1 := by
    intro h
    apply hvn
    have he : embed (v+u)=embed v+embed u := embedHom.map_add v u
    rw [he] at h
    simpa only [add_sub_cancel_right] using S1.sub_mem h huS
  have hminus : embed (v-u)∉S1 := by
    intro h
    apply hvn
    have he : embed (v-u)=embed v-embed u := embedHom.map_sub v u
    rw [he] at h
    simpa only [sub_add_cancel] using S1.add_mem h huS
  have hp' := hvmin (v+u) ((literalLattice p κ t).add_mem hv hu) hplus
  have hm' := hvmin (v-u) ((literalLattice p κ t).sub_mem hv hu) hminus
  have hpSq := pow_le_pow_left₀ (norm_nonneg _) hp' 2
  have hmSq := pow_le_pow_left₀ (norm_nonneg _) hm' 2
  have heplus : embed (v+u)=embed v+embed u := embedHom.map_add v u
  have heminus : embed (v-u)=embed v-embed u := embedHom.map_sub v u
  rw [heplus,norm_add_sq_real,real_inner_comm (embed v) (embed u)] at hpSq
  rw [heminus,norm_sub_sq_real,real_inner_comm (embed v) (embed u)] at hmSq
  have hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hind : LinearIndependent ℝ ![embed u,embed v,embed w] := by
    have hh := hpair.finSnoc hwn
    convert hh using 1
    ext i
    fin_cases i <;> rfl
  refine ⟨u,v,w,⟨?_,?_⟩,huv,hvw,hip,hvn,hwn,(fun z hz hzn => humin z hz (by simpa only [Submodule.mem_bot] using hzn)),hvmin,hwmin⟩
  · intro i
    fin_cases i
    · exact hu
    · exact hv
    · exact hw
  · convert hind using 1
    ext i
    fin_cases i <;> rfl

end OriginalReducedBasisData318
