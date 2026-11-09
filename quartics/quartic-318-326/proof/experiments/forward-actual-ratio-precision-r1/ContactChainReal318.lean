module
public import ContactChainLimits318
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Rat
public section
noncomputable section
namespace ContactChainReal318
open CircuitReplay
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The exact146 stored rational source inputs, after their actual real cast.
No independent scalar replacement is used in the application theorem. -/
abbrev Coeff := Fin 146 → ℝ
@[expose] def project (w : Assignment) : Coeff := fun i => (w i.val : ℝ)
@[expose] def view (w : Coeff) (q x z : ℝ) : ℕ → ℝ := fun i =>
  if i=151 then q else if i=156 then x else if i=158 then z else
  if hi : i<146 then w ⟨i,hi⟩ else 0

lemma view_continuous :
    Continuous (fun p : Coeff × (ℝ × ℝ × ℝ) => view p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply continuous_pi
  intro i
  unfold view
  split_ifs <;> fun_prop

@[expose] def value159 (w : ℕ → ℝ) : ℝ := -((-1) + (-1 * w 126 * w 156))

@[fun_prop] lemma value159_continuous : Continuous value159 := by
  unfold value159
  fun_prop

lemma value159_cast (w : Assignment) (q x z : ℚ) :
    value159 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value159 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value159,ContactChainWitness318.value159]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value159_zero (w : Coeff) : value159 (view w 0 0 0)=1 := by
  simp only [value159]
  norm_num [view]

@[expose] def value160 (w : ℕ → ℝ) : ℝ := -((-1 * w 125 * w 151) + (-1 * (value159 w) * (value159 w)))

@[fun_prop] lemma value160_continuous : Continuous value160 := by
  unfold value160
  fun_prop

lemma value160_cast (w : Assignment) (q x z : ℚ) :
    value160 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value160 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value160,ContactChainWitness318.value160,value159_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value160_zero (w : Coeff) : value160 (view w 0 0 0)=1 := by
  simp only [value160,value159_zero]
  norm_num [view]

@[expose] def value161 (w : ℕ → ℝ) : ℝ := -((-1 * w 58 * w 151) + (-1 * (value160 w) * (value160 w)))

@[fun_prop] lemma value161_continuous : Continuous value161 := by
  unfold value161
  fun_prop

lemma value161_cast (w : Assignment) (q x z : ℚ) :
    value161 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value161 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value161,ContactChainWitness318.value161,value159_cast,value160_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value161_zero (w : Coeff) : value161 (view w 0 0 0)=1 := by
  simp only [value161,value159_zero,value160_zero]
  norm_num [view]

@[expose] def value162 (w : ℕ → ℝ) : ℝ := -((-2 * w 59 * w 151))

@[fun_prop] lemma value162_continuous : Continuous value162 := by
  unfold value162
  fun_prop

lemma value162_cast (w : Assignment) (q x z : ℚ) :
    value162 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value162 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value162,ContactChainWitness318.value162,value159_cast,value160_cast,value161_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value162_zero (w : Coeff) : value162 (view w 0 0 0)=0 := by
  simp only [value162,value159_zero,value160_zero,value161_zero]
  norm_num [view]

@[expose] def value163 (w : ℕ → ℝ) : ℝ := -((-1 * w 60 * w 151) + (-1 * (value161 w) * (value161 w)) + (-2 * (value162 w) * (value162 w)))

@[fun_prop] lemma value163_continuous : Continuous value163 := by
  unfold value163
  fun_prop

lemma value163_cast (w : Assignment) (q x z : ℚ) :
    value163 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value163 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value163,ContactChainWitness318.value163,value159_cast,value160_cast,value161_cast,value162_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value163_zero (w : Coeff) : value163 (view w 0 0 0)=1 := by
  simp only [value163,value159_zero,value160_zero,value161_zero,value162_zero]
  norm_num [view]

@[expose] def value164 (w : ℕ → ℝ) : ℝ := -((-2 * w 61 * w 151) + (-2 * (value161 w) * (value162 w)))

@[fun_prop] lemma value164_continuous : Continuous value164 := by
  unfold value164
  fun_prop

lemma value164_cast (w : Assignment) (q x z : ℚ) :
    value164 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value164 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value164,ContactChainWitness318.value164,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value164_zero (w : Coeff) : value164 (view w 0 0 0)=0 := by
  simp only [value164,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero]
  norm_num [view]

@[expose] def value165 (w : ℕ → ℝ) : ℝ := -((-2 * w 62 * w 151) + (-1 * (value163 w) * (value163 w)) + (-2 * (value164 w) * (value164 w)))

@[fun_prop] lemma value165_continuous : Continuous value165 := by
  unfold value165
  fun_prop

lemma value165_cast (w : Assignment) (q x z : ℚ) :
    value165 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value165 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value165,ContactChainWitness318.value165,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value165_zero (w : Coeff) : value165 (view w 0 0 0)=1 := by
  simp only [value165,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero]
  norm_num [view]

@[expose] def value166 (w : ℕ → ℝ) : ℝ := -((-2 * w 63 * w 151) + (-2 * (value163 w) * (value164 w)))

@[fun_prop] lemma value166_continuous : Continuous value166 := by
  unfold value166
  fun_prop

lemma value166_cast (w : Assignment) (q x z : ℚ) :
    value166 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value166 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value166,ContactChainWitness318.value166,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value166_zero (w : Coeff) : value166 (view w 0 0 0)=0 := by
  simp only [value166,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero]
  norm_num [view]

@[expose] def value167 (w : ℕ → ℝ) : ℝ := -((-1 * w 64 * w 151) + (-1 * (value165 w) * (value165 w)) + (-2 * (value166 w) * (value166 w)))

@[fun_prop] lemma value167_continuous : Continuous value167 := by
  unfold value167
  fun_prop

lemma value167_cast (w : Assignment) (q x z : ℚ) :
    value167 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value167 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value167,ContactChainWitness318.value167,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value167_zero (w : Coeff) : value167 (view w 0 0 0)=1 := by
  simp only [value167,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero]
  norm_num [view]

@[expose] def value168 (w : ℕ → ℝ) : ℝ := -((-2 * w 65 * w 151) + (-2 * (value165 w) * (value166 w)))

@[fun_prop] lemma value168_continuous : Continuous value168 := by
  unfold value168
  fun_prop

lemma value168_cast (w : Assignment) (q x z : ℚ) :
    value168 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value168 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value168,ContactChainWitness318.value168,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value168_zero (w : Coeff) : value168 (view w 0 0 0)=0 := by
  simp only [value168,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero]
  norm_num [view]

@[expose] def value169 (w : ℕ → ℝ) : ℝ := -((-1 * w 19 * w 151) + (1 * w 151) + (-1 * (value167 w) * (value167 w)) + (-2 * (value168 w) * (value168 w)))

@[fun_prop] lemma value169_continuous : Continuous value169 := by
  unfold value169
  fun_prop

lemma value169_cast (w : Assignment) (q x z : ℚ) :
    value169 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value169 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value169,ContactChainWitness318.value169,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value169_zero (w : Coeff) : value169 (view w 0 0 0)=1 := by
  simp only [value169,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero]
  norm_num [view]

@[expose] def value170 (w : ℕ → ℝ) : ℝ := -((1 * w 20 * w 151) + (-2 * (value167 w) * (value168 w)))

@[fun_prop] lemma value170_continuous : Continuous value170 := by
  unfold value170
  fun_prop

lemma value170_cast (w : Assignment) (q x z : ℚ) :
    value170 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value170 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value170,ContactChainWitness318.value170,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value170_zero (w : Coeff) : value170 (view w 0 0 0)=0 := by
  simp only [value170,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero]
  norm_num [view]

@[expose] def value171 (w : ℕ → ℝ) : ℝ := -((-1 * w 23 * w 151) + (1 * w 151) + (-1 * (value169 w) * (value169 w)) + (-2 * (value170 w) * (value170 w)))

@[fun_prop] lemma value171_continuous : Continuous value171 := by
  unfold value171
  fun_prop

lemma value171_cast (w : Assignment) (q x z : ℚ) :
    value171 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value171 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value171,ContactChainWitness318.value171,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value171_zero (w : Coeff) : value171 (view w 0 0 0)=1 := by
  simp only [value171,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero]
  norm_num [view]

@[expose] def value172 (w : ℕ → ℝ) : ℝ := -((1 * w 24 * w 151) + (-2 * (value169 w) * (value170 w)))

@[fun_prop] lemma value172_continuous : Continuous value172 := by
  unfold value172
  fun_prop

lemma value172_cast (w : Assignment) (q x z : ℚ) :
    value172 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value172 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value172,ContactChainWitness318.value172,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value172_zero (w : Coeff) : value172 (view w 0 0 0)=0 := by
  simp only [value172,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero]
  norm_num [view]

@[expose] def value173 (w : ℕ → ℝ) : ℝ := -((-1 * w 27 * w 151) + (1 * w 151) + (-1 * (value171 w) * (value171 w)) + (-2 * (value172 w) * (value172 w)))

@[fun_prop] lemma value173_continuous : Continuous value173 := by
  unfold value173
  fun_prop

lemma value173_cast (w : Assignment) (q x z : ℚ) :
    value173 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value173 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value173,ContactChainWitness318.value173,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value173_zero (w : Coeff) : value173 (view w 0 0 0)=1 := by
  simp only [value173,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero]
  norm_num [view]

@[expose] def value174 (w : ℕ → ℝ) : ℝ := -((1 * w 28 * w 151) + (-2 * (value171 w) * (value172 w)))

@[fun_prop] lemma value174_continuous : Continuous value174 := by
  unfold value174
  fun_prop

lemma value174_cast (w : Assignment) (q x z : ℚ) :
    value174 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value174 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value174,ContactChainWitness318.value174,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value174_zero (w : Coeff) : value174 (view w 0 0 0)=0 := by
  simp only [value174,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero]
  norm_num [view]

@[expose] def value175 (w : ℕ → ℝ) : ℝ := -((-1 * w 31 * w 151) + (1 * w 151) + (-1 * (value173 w) * (value173 w)) + (-2 * (value174 w) * (value174 w)))

@[fun_prop] lemma value175_continuous : Continuous value175 := by
  unfold value175
  fun_prop

lemma value175_cast (w : Assignment) (q x z : ℚ) :
    value175 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value175 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value175,ContactChainWitness318.value175,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value175_zero (w : Coeff) : value175 (view w 0 0 0)=1 := by
  simp only [value175,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero]
  norm_num [view]

@[expose] def value176 (w : ℕ → ℝ) : ℝ := -((1 * w 32 * w 151) + (-2 * (value173 w) * (value174 w)))

@[fun_prop] lemma value176_continuous : Continuous value176 := by
  unfold value176
  fun_prop

lemma value176_cast (w : Assignment) (q x z : ℚ) :
    value176 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value176 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value176,ContactChainWitness318.value176,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value176_zero (w : Coeff) : value176 (view w 0 0 0)=0 := by
  simp only [value176,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero]
  norm_num [view]

@[expose] def value177 (w : ℕ → ℝ) : ℝ := -((-1 * w 127 * w 156) + (-1 * (value175 w) * (value175 w)) + (-2 * (value176 w) * (value176 w)))

@[fun_prop] lemma value177_continuous : Continuous value177 := by
  unfold value177
  fun_prop

lemma value177_cast (w : Assignment) (q x z : ℚ) :
    value177 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value177 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value177,ContactChainWitness318.value177,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value177_zero (w : Coeff) : value177 (view w 0 0 0)=1 := by
  simp only [value177,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero]
  norm_num [view]

@[expose] def value178 (w : ℕ → ℝ) : ℝ := -((-2 * w 128 * w 156) + (-2 * (value175 w) * (value176 w)))

@[fun_prop] lemma value178_continuous : Continuous value178 := by
  unfold value178
  fun_prop

lemma value178_cast (w : Assignment) (q x z : ℚ) :
    value178 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value178 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value178,ContactChainWitness318.value178,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast,value177_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value178_zero (w : Coeff) : value178 (view w 0 0 0)=0 := by
  simp only [value178,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero]
  norm_num [view]

@[expose] def value179 (w : ℕ → ℝ) : ℝ := -((-1 * w 129 * w 158) + (-1 * (value177 w) * (value177 w)) + (-2 * (value178 w) * (value178 w)))

@[fun_prop] lemma value179_continuous : Continuous value179 := by
  unfold value179
  fun_prop

lemma value179_cast (w : Assignment) (q x z : ℚ) :
    value179 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value179 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value179,ContactChainWitness318.value179,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast,value177_cast,value178_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value179_zero (w : Coeff) : value179 (view w 0 0 0)=1 := by
  simp only [value179,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero]
  norm_num [view]

@[expose] def value180 (w : ℕ → ℝ) : ℝ := -((-2 * w 130 * w 158) + (-2 * (value177 w) * (value178 w)))

@[fun_prop] lemma value180_continuous : Continuous value180 := by
  unfold value180
  fun_prop

lemma value180_cast (w : Assignment) (q x z : ℚ) :
    value180 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value180 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value180,ContactChainWitness318.value180,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast,value177_cast,value178_cast,value179_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value180_zero (w : Coeff) : value180 (view w 0 0 0)=0 := by
  simp only [value180,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero]
  norm_num [view]

@[expose] def value181 (w : ℕ → ℝ) : ℝ := -((-1 * w 131 * w 158) + (-1 * (value179 w) * (value179 w)) + (-2 * (value180 w) * (value180 w)))

@[fun_prop] lemma value181_continuous : Continuous value181 := by
  unfold value181
  fun_prop

lemma value181_cast (w : Assignment) (q x z : ℚ) :
    value181 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value181 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value181,ContactChainWitness318.value181,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast,value177_cast,value178_cast,value179_cast,value180_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value181_zero (w : Coeff) : value181 (view w 0 0 0)=1 := by
  simp only [value181,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero]
  norm_num [view]

@[expose] def value182 (w : ℕ → ℝ) : ℝ := -((-2 * w 132 * w 158) + (-2 * (value179 w) * (value180 w)))

@[fun_prop] lemma value182_continuous : Continuous value182 := by
  unfold value182
  fun_prop

lemma value182_cast (w : Assignment) (q x z : ℚ) :
    value182 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value182 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value182,ContactChainWitness318.value182,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast,value177_cast,value178_cast,value179_cast,value180_cast,value181_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value182_zero (w : Coeff) : value182 (view w 0 0 0)=0 := by
  simp only [value182,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero]
  norm_num [view]

@[expose] def value183 (w : ℕ → ℝ) : ℝ := -((-1 * w 133 * w 158) + (-1 * (value181 w) * (value181 w)) + (-2 * (value182 w) * (value182 w)))

@[fun_prop] lemma value183_continuous : Continuous value183 := by
  unfold value183
  fun_prop

lemma value183_cast (w : Assignment) (q x z : ℚ) :
    value183 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value183 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value183,ContactChainWitness318.value183,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast,value177_cast,value178_cast,value179_cast,value180_cast,value181_cast,value182_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value183_zero (w : Coeff) : value183 (view w 0 0 0)=1 := by
  simp only [value183,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero]
  norm_num [view]

@[expose] def value184 (w : ℕ → ℝ) : ℝ := -((-2 * w 134 * w 158) + (-2 * (value181 w) * (value182 w)))

@[fun_prop] lemma value184_continuous : Continuous value184 := by
  unfold value184
  fun_prop

lemma value184_cast (w : Assignment) (q x z : ℚ) :
    value184 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value184 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value184,ContactChainWitness318.value184,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast,value177_cast,value178_cast,value179_cast,value180_cast,value181_cast,value182_cast,value183_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value184_zero (w : Coeff) : value184 (view w 0 0 0)=0 := by
  simp only [value184,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero,value183_zero]
  norm_num [view]

@[expose] def value185 (w : ℕ → ℝ) : ℝ := -((-110885832 * w 0 * w 156) + (7446 * w 102 * w 156) + (-110885832 * w 118 * w 156) + (-221771664 * w 135 * w 156) + (-13860729 * w 156) + (-1 * (value183 w) * (value183 w)) + (-2 * (value184 w) * (value184 w)))

@[fun_prop] lemma value185_continuous : Continuous value185 := by
  unfold value185
  fun_prop

lemma value185_cast (w : Assignment) (q x z : ℚ) :
    value185 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value185 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value185,ContactChainWitness318.value185,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast,value177_cast,value178_cast,value179_cast,value180_cast,value181_cast,value182_cast,value183_cast,value184_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value185_zero (w : Coeff) : value185 (view w 0 0 0)=1 := by
  simp only [value185,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero,value183_zero,value184_zero]
  norm_num [view]

@[expose] def value186 (w : ℕ → ℝ) : ℝ := -((7446 * w 103 * w 156) + (29784 * w 136 * w 156) + (-2 * (value183 w) * (value184 w)))

@[fun_prop] lemma value186_continuous : Continuous value186 := by
  unfold value186
  fun_prop

lemma value186_cast (w : Assignment) (q x z : ℚ) :
    value186 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value186 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value186,ContactChainWitness318.value186,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast,value177_cast,value178_cast,value179_cast,value180_cast,value181_cast,value182_cast,value183_cast,value184_cast,value185_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value186_zero (w : Coeff) : value186 (view w 0 0 0)=0 := by
  simp only [value186,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero,value183_zero,value184_zero,value185_zero]
  norm_num [view]

@[expose] def value187 (w : ℕ → ℝ) : ℝ := -((2 * w 123 * w 158) + (-1 * w 137 * w 158) + (-1 * w 158) + (-1 * (value185 w) * (value185 w)) + (-2 * (value186 w) * (value186 w)))

@[fun_prop] lemma value187_continuous : Continuous value187 := by
  unfold value187
  fun_prop

lemma value187_cast (w : Assignment) (q x z : ℚ) :
    value187 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value187 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value187,ContactChainWitness318.value187,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast,value177_cast,value178_cast,value179_cast,value180_cast,value181_cast,value182_cast,value183_cast,value184_cast,value185_cast,value186_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value187_zero (w : Coeff) : value187 (view w 0 0 0)=1 := by
  simp only [value187,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero,value183_zero,value184_zero,value185_zero,value186_zero]
  norm_num [view]

@[expose] def value188 (w : ℕ → ℝ) : ℝ := -((4 * w 124 * w 158) + (-4 * w 138 * w 158) + (-2 * (value185 w) * (value186 w)))

@[fun_prop] lemma value188_continuous : Continuous value188 := by
  unfold value188
  fun_prop

lemma value188_cast (w : Assignment) (q x z : ℚ) :
    value188 (view (project w) (q:ℝ) (x:ℝ) (z:ℝ))=
      (ContactChainWitness318.value188 (ContactChainLimits318.view w q x z) : ℝ) := by
  simp only [value188,ContactChainWitness318.value188,value159_cast,value160_cast,value161_cast,value162_cast,value163_cast,value164_cast,value165_cast,value166_cast,value167_cast,value168_cast,value169_cast,value170_cast,value171_cast,value172_cast,value173_cast,value174_cast,value175_cast,value176_cast,value177_cast,value178_cast,value179_cast,value180_cast,value181_cast,value182_cast,value183_cast,value184_cast,value185_cast,value186_cast,value187_cast]
  simp [view,project,ContactChainLimits318.view] <;> push_cast <;> ring

lemma value188_zero (w : Coeff) : value188 (view w 0 0 0)=0 := by
  simp only [value188,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero,value183_zero,value184_zero,value185_zero,value186_zero,value187_zero]
  norm_num [view]

@[expose] def chain (p : Coeff × (ℝ × ℝ × ℝ)) : ℝ × ℝ :=
  (value187 (view p.1 p.2.1 p.2.2.1 p.2.2.2),value188 (view p.1 p.2.1 p.2.2.1 p.2.2.2))

lemma chain_continuous : Continuous chain :=
  (value187_continuous.comp view_continuous).prodMk (value188_continuous.comp view_continuous)

lemma chain_zero (w : Coeff) : chain (w,(0,0,0))=(1,0) := by
  simp [chain,value187_zero,value188_zero]

/-- The real polynomial extension evaluates to the cast of the actual chain
for every stored rational assignment and its genuine source weights. -/
theorem chain_actual (w : Assignment) (t : ℚ) :
    chain (project w,((ContactWeightWitness318.weight t:ℝ),
      (((ContactWeightWitness318.weight t)^7*(t-1)^18:ℚ):ℝ),
      (((ContactWeightWitness318.weight t)^25*(t-1)^72:ℚ):ℝ)))=
      ((PoleInputWitness318.realChain w t:ℝ),(PoleInputWitness318.imagChain w t:ℝ)) := by
  simp only [chain,value187_cast,value188_cast]
  rw [←ContactChainLimits318.value187_view,←ContactChainLimits318.value188_view]
  rfl

end ContactChainReal318
