module
public import ContactWeightLimits318
public import PoleInputWitness318
public section
noncomputable section
namespace ContactChainLimits318
open Filter CircuitReplay ContactWeightWitness318 ContactChainWitness318 PoleInputWitness318
open scoped Topology
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The chain reads just these three vanishing weights, all other inputs
being held fixed. This is an actual coordinate-dependence statement. -/
@[expose] def view (w : Assignment) (q x z : ℚ) : Assignment := fun i =>
  if i=151 then q else if i=156 then x else if i=158 then z else w i

lemma view_continuous (w : Assignment) :
    Continuous (fun p : ℚ × ℚ × ℚ => view w p.1 p.2.1 p.2.2) := by
  apply continuous_pi
  intro i
  unfold view
  split_ifs <;> fun_prop

@[fun_prop] lemma value159_continuous : Continuous ContactChainWitness318.value159 := by
  unfold ContactChainWitness318.value159
  fun_prop

lemma value159_view (w : Assignment) (t : ℚ) :
    value159 (ContactWeightWitness318.fill w t)=
      value159 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value159]
  simp [ContactWeightWitness318.fill,view]

lemma value159_zero (w : Assignment) : value159 (view w 0 0 0)=1 := by
  norm_num [value159,view]

@[fun_prop] lemma value160_continuous : Continuous ContactChainWitness318.value160 := by
  unfold ContactChainWitness318.value160
  fun_prop

lemma value160_view (w : Assignment) (t : ℚ) :
    value160 (ContactWeightWitness318.fill w t)=
      value160 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value160,value159_view]
  simp [ContactWeightWitness318.fill,view]

lemma value160_zero (w : Assignment) : value160 (view w 0 0 0)=1 := by
  simp only [value160,value159_zero]
  norm_num [view]

@[fun_prop] lemma value161_continuous : Continuous ContactChainWitness318.value161 := by
  unfold ContactChainWitness318.value161
  fun_prop

lemma value161_view (w : Assignment) (t : ℚ) :
    value161 (ContactWeightWitness318.fill w t)=
      value161 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value161,value159_view,value160_view]
  simp [ContactWeightWitness318.fill,view]

lemma value161_zero (w : Assignment) : value161 (view w 0 0 0)=1 := by
  simp only [value161,value159_zero,value160_zero]
  norm_num [view]

@[fun_prop] lemma value162_continuous : Continuous ContactChainWitness318.value162 := by
  unfold ContactChainWitness318.value162
  fun_prop

lemma value162_view (w : Assignment) (t : ℚ) :
    value162 (ContactWeightWitness318.fill w t)=
      value162 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value162,value159_view,value160_view,value161_view]
  simp [ContactWeightWitness318.fill,view]

lemma value162_zero (w : Assignment) : value162 (view w 0 0 0)=0 := by
  simp only [value162,value159_zero,value160_zero,value161_zero]
  norm_num [view]

@[fun_prop] lemma value163_continuous : Continuous ContactChainWitness318.value163 := by
  unfold ContactChainWitness318.value163
  fun_prop

lemma value163_view (w : Assignment) (t : ℚ) :
    value163 (ContactWeightWitness318.fill w t)=
      value163 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value163,value159_view,value160_view,value161_view,value162_view]
  simp [ContactWeightWitness318.fill,view]

lemma value163_zero (w : Assignment) : value163 (view w 0 0 0)=1 := by
  simp only [value163,value159_zero,value160_zero,value161_zero,value162_zero]
  norm_num [view]

@[fun_prop] lemma value164_continuous : Continuous ContactChainWitness318.value164 := by
  unfold ContactChainWitness318.value164
  fun_prop

lemma value164_view (w : Assignment) (t : ℚ) :
    value164 (ContactWeightWitness318.fill w t)=
      value164 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value164,value159_view,value160_view,value161_view,value162_view,value163_view]
  simp [ContactWeightWitness318.fill,view]

lemma value164_zero (w : Assignment) : value164 (view w 0 0 0)=0 := by
  simp only [value164,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero]
  norm_num [view]

@[fun_prop] lemma value165_continuous : Continuous ContactChainWitness318.value165 := by
  unfold ContactChainWitness318.value165
  fun_prop

lemma value165_view (w : Assignment) (t : ℚ) :
    value165 (ContactWeightWitness318.fill w t)=
      value165 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value165,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view]
  simp [ContactWeightWitness318.fill,view]

lemma value165_zero (w : Assignment) : value165 (view w 0 0 0)=1 := by
  simp only [value165,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero]
  norm_num [view]

@[fun_prop] lemma value166_continuous : Continuous ContactChainWitness318.value166 := by
  unfold ContactChainWitness318.value166
  fun_prop

lemma value166_view (w : Assignment) (t : ℚ) :
    value166 (ContactWeightWitness318.fill w t)=
      value166 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value166,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view]
  simp [ContactWeightWitness318.fill,view]

lemma value166_zero (w : Assignment) : value166 (view w 0 0 0)=0 := by
  simp only [value166,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero]
  norm_num [view]

@[fun_prop] lemma value167_continuous : Continuous ContactChainWitness318.value167 := by
  unfold ContactChainWitness318.value167
  fun_prop

lemma value167_view (w : Assignment) (t : ℚ) :
    value167 (ContactWeightWitness318.fill w t)=
      value167 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value167,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view]
  simp [ContactWeightWitness318.fill,view]

lemma value167_zero (w : Assignment) : value167 (view w 0 0 0)=1 := by
  simp only [value167,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero]
  norm_num [view]

@[fun_prop] lemma value168_continuous : Continuous ContactChainWitness318.value168 := by
  unfold ContactChainWitness318.value168
  fun_prop

lemma value168_view (w : Assignment) (t : ℚ) :
    value168 (ContactWeightWitness318.fill w t)=
      value168 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value168,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view]
  simp [ContactWeightWitness318.fill,view]

lemma value168_zero (w : Assignment) : value168 (view w 0 0 0)=0 := by
  simp only [value168,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero]
  norm_num [view]

@[fun_prop] lemma value169_continuous : Continuous ContactChainWitness318.value169 := by
  unfold ContactChainWitness318.value169
  fun_prop

lemma value169_view (w : Assignment) (t : ℚ) :
    value169 (ContactWeightWitness318.fill w t)=
      value169 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value169,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view]
  simp [ContactWeightWitness318.fill,view]

lemma value169_zero (w : Assignment) : value169 (view w 0 0 0)=1 := by
  simp only [value169,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero]
  norm_num [view]

@[fun_prop] lemma value170_continuous : Continuous ContactChainWitness318.value170 := by
  unfold ContactChainWitness318.value170
  fun_prop

lemma value170_view (w : Assignment) (t : ℚ) :
    value170 (ContactWeightWitness318.fill w t)=
      value170 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value170,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view]
  simp [ContactWeightWitness318.fill,view]

lemma value170_zero (w : Assignment) : value170 (view w 0 0 0)=0 := by
  simp only [value170,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero]
  norm_num [view]

@[fun_prop] lemma value171_continuous : Continuous ContactChainWitness318.value171 := by
  unfold ContactChainWitness318.value171
  fun_prop

lemma value171_view (w : Assignment) (t : ℚ) :
    value171 (ContactWeightWitness318.fill w t)=
      value171 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value171,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view]
  simp [ContactWeightWitness318.fill,view]

lemma value171_zero (w : Assignment) : value171 (view w 0 0 0)=1 := by
  simp only [value171,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero]
  norm_num [view]

@[fun_prop] lemma value172_continuous : Continuous ContactChainWitness318.value172 := by
  unfold ContactChainWitness318.value172
  fun_prop

lemma value172_view (w : Assignment) (t : ℚ) :
    value172 (ContactWeightWitness318.fill w t)=
      value172 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value172,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view]
  simp [ContactWeightWitness318.fill,view]

lemma value172_zero (w : Assignment) : value172 (view w 0 0 0)=0 := by
  simp only [value172,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero]
  norm_num [view]

@[fun_prop] lemma value173_continuous : Continuous ContactChainWitness318.value173 := by
  unfold ContactChainWitness318.value173
  fun_prop

lemma value173_view (w : Assignment) (t : ℚ) :
    value173 (ContactWeightWitness318.fill w t)=
      value173 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value173,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view]
  simp [ContactWeightWitness318.fill,view]

lemma value173_zero (w : Assignment) : value173 (view w 0 0 0)=1 := by
  simp only [value173,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero]
  norm_num [view]

@[fun_prop] lemma value174_continuous : Continuous ContactChainWitness318.value174 := by
  unfold ContactChainWitness318.value174
  fun_prop

lemma value174_view (w : Assignment) (t : ℚ) :
    value174 (ContactWeightWitness318.fill w t)=
      value174 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value174,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view]
  simp [ContactWeightWitness318.fill,view]

lemma value174_zero (w : Assignment) : value174 (view w 0 0 0)=0 := by
  simp only [value174,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero]
  norm_num [view]

@[fun_prop] lemma value175_continuous : Continuous ContactChainWitness318.value175 := by
  unfold ContactChainWitness318.value175
  fun_prop

lemma value175_view (w : Assignment) (t : ℚ) :
    value175 (ContactWeightWitness318.fill w t)=
      value175 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value175,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view]
  simp [ContactWeightWitness318.fill,view]

lemma value175_zero (w : Assignment) : value175 (view w 0 0 0)=1 := by
  simp only [value175,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero]
  norm_num [view]

@[fun_prop] lemma value176_continuous : Continuous ContactChainWitness318.value176 := by
  unfold ContactChainWitness318.value176
  fun_prop

lemma value176_view (w : Assignment) (t : ℚ) :
    value176 (ContactWeightWitness318.fill w t)=
      value176 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value176,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view]
  simp [ContactWeightWitness318.fill,view]

lemma value176_zero (w : Assignment) : value176 (view w 0 0 0)=0 := by
  simp only [value176,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero]
  norm_num [view]

@[fun_prop] lemma value177_continuous : Continuous ContactChainWitness318.value177 := by
  unfold ContactChainWitness318.value177
  fun_prop

lemma value177_view (w : Assignment) (t : ℚ) :
    value177 (ContactWeightWitness318.fill w t)=
      value177 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value177,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view]
  simp [ContactWeightWitness318.fill,view]

lemma value177_zero (w : Assignment) : value177 (view w 0 0 0)=1 := by
  simp only [value177,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero]
  norm_num [view]

@[fun_prop] lemma value178_continuous : Continuous ContactChainWitness318.value178 := by
  unfold ContactChainWitness318.value178
  fun_prop

lemma value178_view (w : Assignment) (t : ℚ) :
    value178 (ContactWeightWitness318.fill w t)=
      value178 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value178,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view,value177_view]
  simp [ContactWeightWitness318.fill,view]

lemma value178_zero (w : Assignment) : value178 (view w 0 0 0)=0 := by
  simp only [value178,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero]
  norm_num [view]

@[fun_prop] lemma value179_continuous : Continuous ContactChainWitness318.value179 := by
  unfold ContactChainWitness318.value179
  fun_prop

lemma value179_view (w : Assignment) (t : ℚ) :
    value179 (ContactWeightWitness318.fill w t)=
      value179 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value179,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view,value177_view,value178_view]
  simp [ContactWeightWitness318.fill,view]

lemma value179_zero (w : Assignment) : value179 (view w 0 0 0)=1 := by
  simp only [value179,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero]
  norm_num [view]

@[fun_prop] lemma value180_continuous : Continuous ContactChainWitness318.value180 := by
  unfold ContactChainWitness318.value180
  fun_prop

lemma value180_view (w : Assignment) (t : ℚ) :
    value180 (ContactWeightWitness318.fill w t)=
      value180 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value180,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view,value177_view,value178_view,value179_view]
  simp [ContactWeightWitness318.fill,view]

lemma value180_zero (w : Assignment) : value180 (view w 0 0 0)=0 := by
  simp only [value180,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero]
  norm_num [view]

@[fun_prop] lemma value181_continuous : Continuous ContactChainWitness318.value181 := by
  unfold ContactChainWitness318.value181
  fun_prop

lemma value181_view (w : Assignment) (t : ℚ) :
    value181 (ContactWeightWitness318.fill w t)=
      value181 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value181,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view,value177_view,value178_view,value179_view,value180_view]
  simp [ContactWeightWitness318.fill,view]

lemma value181_zero (w : Assignment) : value181 (view w 0 0 0)=1 := by
  simp only [value181,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero]
  norm_num [view]

@[fun_prop] lemma value182_continuous : Continuous ContactChainWitness318.value182 := by
  unfold ContactChainWitness318.value182
  fun_prop

lemma value182_view (w : Assignment) (t : ℚ) :
    value182 (ContactWeightWitness318.fill w t)=
      value182 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value182,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view,value177_view,value178_view,value179_view,value180_view,value181_view]
  simp [ContactWeightWitness318.fill,view]

lemma value182_zero (w : Assignment) : value182 (view w 0 0 0)=0 := by
  simp only [value182,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero]
  norm_num [view]

@[fun_prop] lemma value183_continuous : Continuous ContactChainWitness318.value183 := by
  unfold ContactChainWitness318.value183
  fun_prop

lemma value183_view (w : Assignment) (t : ℚ) :
    value183 (ContactWeightWitness318.fill w t)=
      value183 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value183,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view,value177_view,value178_view,value179_view,value180_view,value181_view,value182_view]
  simp [ContactWeightWitness318.fill,view]

lemma value183_zero (w : Assignment) : value183 (view w 0 0 0)=1 := by
  simp only [value183,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero]
  norm_num [view]

@[fun_prop] lemma value184_continuous : Continuous ContactChainWitness318.value184 := by
  unfold ContactChainWitness318.value184
  fun_prop

lemma value184_view (w : Assignment) (t : ℚ) :
    value184 (ContactWeightWitness318.fill w t)=
      value184 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value184,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view,value177_view,value178_view,value179_view,value180_view,value181_view,value182_view,value183_view]
  simp [ContactWeightWitness318.fill,view]

lemma value184_zero (w : Assignment) : value184 (view w 0 0 0)=0 := by
  simp only [value184,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero,value183_zero]
  norm_num [view]

@[fun_prop] lemma value185_continuous : Continuous ContactChainWitness318.value185 := by
  unfold ContactChainWitness318.value185
  fun_prop

lemma value185_view (w : Assignment) (t : ℚ) :
    value185 (ContactWeightWitness318.fill w t)=
      value185 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value185,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view,value177_view,value178_view,value179_view,value180_view,value181_view,value182_view,value183_view,value184_view]
  simp [ContactWeightWitness318.fill,view]

lemma value185_zero (w : Assignment) : value185 (view w 0 0 0)=1 := by
  simp only [value185,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero,value183_zero,value184_zero]
  norm_num [view]

@[fun_prop] lemma value186_continuous : Continuous ContactChainWitness318.value186 := by
  unfold ContactChainWitness318.value186
  fun_prop

lemma value186_view (w : Assignment) (t : ℚ) :
    value186 (ContactWeightWitness318.fill w t)=
      value186 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value186,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view,value177_view,value178_view,value179_view,value180_view,value181_view,value182_view,value183_view,value184_view,value185_view]
  simp [ContactWeightWitness318.fill,view]

lemma value186_zero (w : Assignment) : value186 (view w 0 0 0)=0 := by
  simp only [value186,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero,value183_zero,value184_zero,value185_zero]
  norm_num [view]

@[fun_prop] lemma value187_continuous : Continuous ContactChainWitness318.value187 := by
  unfold ContactChainWitness318.value187
  fun_prop

lemma value187_view (w : Assignment) (t : ℚ) :
    value187 (ContactWeightWitness318.fill w t)=
      value187 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value187,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view,value177_view,value178_view,value179_view,value180_view,value181_view,value182_view,value183_view,value184_view,value185_view,value186_view]
  simp [ContactWeightWitness318.fill,view]

lemma value187_zero (w : Assignment) : value187 (view w 0 0 0)=1 := by
  simp only [value187,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero,value183_zero,value184_zero,value185_zero,value186_zero]
  norm_num [view]

@[fun_prop] lemma value188_continuous : Continuous ContactChainWitness318.value188 := by
  unfold ContactChainWitness318.value188
  fun_prop

lemma value188_view (w : Assignment) (t : ℚ) :
    value188 (ContactWeightWitness318.fill w t)=
      value188 (view w (weight t) ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72)) := by
  simp only [value188,value159_view,value160_view,value161_view,value162_view,value163_view,value164_view,value165_view,value166_view,value167_view,value168_view,value169_view,value170_view,value171_view,value172_view,value173_view,value174_view,value175_view,value176_view,value177_view,value178_view,value179_view,value180_view,value181_view,value182_view,value183_view,value184_view,value185_view,value186_view,value187_view]
  simp [ContactWeightWitness318.fill,view]

lemma value188_zero (w : Assignment) : value188 (view w 0 0 0)=0 := by
  simp only [value188,value159_zero,value160_zero,value161_zero,value162_zero,value163_zero,value164_zero,value165_zero,value166_zero,value167_zero,value168_zero,value169_zero,value170_zero,value171_zero,value172_zero,value173_zero,value174_zero,value175_zero,value176_zero,value177_zero,value178_zero,value179_zero,value180_zero,value181_zero,value182_zero,value183_zero,value184_zero,value185_zero,value186_zero,value187_zero]
  norm_num [view]

/-- For every fixed original assignment, the actual detector chain tends
to (1,0) as its free rational contact parameter tends to positive infinity. -/
theorem realChain_limit (w : Assignment) : Tendsto (realChain w) atTop (𝓝 1) := by
  have hc := value187_continuous.comp (view_continuous w)
  have ht := hc.continuousAt.tendsto.comp
    (ContactWeightLimits318.weight_limit.prodMk
      (ContactWeightLimits318.weight7_limit.prodMk ContactWeightLimits318.weight25_limit))
  change Tendsto (fun t => value187 (view w (weight t)
    ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72))) atTop
      (𝓝 (value187 (view w 0 0 0))) at ht
  rw [value187_zero] at ht
  convert ht using 1
  funext t
  exact value187_view w t

theorem imagChain_limit (w : Assignment) : Tendsto (imagChain w) atTop (𝓝 0) := by
  have hc := value188_continuous.comp (view_continuous w)
  have ht := hc.continuousAt.tendsto.comp
    (ContactWeightLimits318.weight_limit.prodMk
      (ContactWeightLimits318.weight7_limit.prodMk ContactWeightLimits318.weight25_limit))
  change Tendsto (fun t => value188 (view w (weight t)
    ((weight t)^7*(t-1)^18) ((weight t)^25*(t-1)^72))) atTop
      (𝓝 (value188 (view w 0 0 0))) at ht
  rw [value188_zero] at ht
  convert ht using 1
  funext t
  exact value188_view w t

theorem traceQuotient_limit (w : Assignment) : Tendsto (traceQuotient w) atTop (𝓝 (1/2)) := by
  have hn := ((realChain_limit w).pow 2).sub (((imagChain_limit w).pow 2).const_mul 2)
  have ht := hn.div ((realChain_limit w).const_mul 2) (by norm_num)
  simpa [traceQuotient] using ht

theorem poleInput_limit (w : Assignment) : Tendsto (poleInput w) atTop (𝓝 0) := by
  have ht := ((traceQuotient_limit w).pow 2).mul ContactWeightLimits318.inverse_ed_limit
  simpa [poleInput,mul_div_assoc] using ht

lemma contact_positive (t : ℚ) (ht : 2<t) : 0<contact t := by
  unfold contact
  have h0 : 0<t := by linarith
  have h1 : 0<t+1/2 := by linarith
  have h2 : 0<t+1 := by linarith
  have h3 : 0<t-1/2399 := by linarith
  have h4 : 0<t+32/407 := by linarith
  exact mul_pos (mul_pos (mul_pos (mul_pos h0 h1) h2) h3) h4

/-- The real part is nonzero and the actual pole parameter lies in (0,17)
for every sufficiently large rational t. This is per fixed assignment;
uniformity over a later orbit choice is deliberately not inferred. -/
theorem eventual_pole_domain (w : Assignment) :
    ∀ᶠ t : ℚ in atTop, 2<t ∧ realChain w t≠0 ∧ 0<poleInput w t ∧ poleInput w t<17 := by
  have hr := (realChain_limit w).eventually (Ioi_mem_nhds (by norm_num : (0:ℚ)<1))
  have hb := (poleInput_limit w).eventually (Iio_mem_nhds (by norm_num : (0:ℚ)<17))
  filter_upwards [eventually_gt_atTop (2:ℚ),hr,hb] with t ht hr hb
  have hn : realChain w t≠0 := ne_of_gt hr
  exact ⟨ht,hn,(pole_positive_iff w t hn (by linarith)).mpr (contact_positive t ht),hb⟩

end ContactChainLimits318
