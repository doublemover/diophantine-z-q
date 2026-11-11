module
public import Mathlib.Topology.VectorBundle.Basic
public section
noncomputable section
namespace LineCoreHomeomorphPullback318
open Set
variable {B C : Type*} [TopologicalSpace B] [TopologicalSpace C] {ι : Type*}

/-- Pull back an independently supplied complex line cocycle, retaining
its actual base sets, transition maps and selected trivializations. -/
@[expose] def core (H : VectorBundleCore ℂ C ℂ ι) (f : B → C) (hf : Continuous f) :
    VectorBundleCore ℂ B ℂ ι where
  baseSet i := f ⁻¹' H.baseSet i
  isOpen_baseSet i := (H.isOpen_baseSet i).preimage hf
  indexAt b := H.indexAt (f b)
  mem_baseSet_at b := H.mem_baseSet_at (f b)
  coordChange i j b := H.coordChange i j (f b)
  coordChange_self i b hb v := H.coordChange_self i (f b) hb v
  continuousOn_coordChange i j := (H.continuousOn_coordChange i j).comp hf.continuousOn
    (fun _ h => h)
  coordChange_comp i j k b hb v := H.coordChange_comp i j k (f b) hb v

@[expose] def forward (H : VectorBundleCore ℂ C ℂ ι) (h : B ≃ₜ C) :
    (core H h h.continuous).TotalSpace → H.TotalSpace := fun p => ⟨h p.1,p.2⟩
@[expose] def inverse (H : VectorBundleCore ℂ C ℂ ι) (h : B ≃ₜ C) :
    H.TotalSpace → (core H h h.continuous).TotalSpace := fun p => ⟨h.symm p.1,p.2⟩

lemma forward_continuous (H : VectorBundleCore ℂ C ℂ ι) (h : B ≃ₜ C) :
    Continuous (forward H h) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let K := core H h h.continuous
  let i := H.indexAt (h p.1)
  have hi : h p.1 ∈ H.baseSet i := H.mem_baseSet_at _
  have hk : p.1 ∈ K.baseSet i := hi
  have hb : ContinuousAt (fun q : K.TotalSpace => h q.1) p :=
    (h.continuous.comp K.continuous_proj).continuousAt
  apply (H.localTriv i).continuousAt_of_comp_left hb hi
  simpa only [forward,VectorBundleCore.localTriv_apply,core] using
    hb.prodMk (((K.localTriv i).continuousAt hk).snd)

lemma inverse_continuous (H : VectorBundleCore ℂ C ℂ ι) (h : B ≃ₜ C) :
    Continuous (inverse H h) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let K := core H h h.continuous
  let i := H.indexAt p.1
  have hi : p.1 ∈ H.baseSet i := H.mem_baseSet_at _
  have hk : h.symm p.1 ∈ K.baseSet i := by
    change h (h.symm p.1) ∈ H.baseSet i
    rwa [h.apply_symm_apply]
  have hb : ContinuousAt (fun q : H.TotalSpace => h.symm q.1) p :=
    (h.symm.continuous.comp H.continuous_proj).continuousAt
  apply (K.localTriv i).continuousAt_of_comp_left hb hk
  simpa only [inverse,VectorBundleCore.localTriv_apply,core,h.apply_symm_apply] using
    hb.prodMk (((H.localTriv i).continuousAt hi).snd)

/-- A base homeomorphism gives the genuine total-space homeomorphism of
its actual pulled-back line bundle. Both cocycle topologies are retained. -/
@[expose] def homeomorph (H : VectorBundleCore ℂ C ℂ ι) (h : B ≃ₜ C) :
    (core H h h.continuous).TotalSpace ≃ₜ H.TotalSpace where
  toFun := forward H h
  invFun := inverse H h
  left_inv := by rintro ⟨b,v⟩; change (⟨h.symm (h b),v⟩ : (core H h h.continuous).TotalSpace) = ⟨b,v⟩; rw [h.symm_apply_apply]
  right_inv := by rintro ⟨c,v⟩; change (⟨h (h.symm c),v⟩ : H.TotalSpace) = ⟨c,v⟩; rw [h.apply_symm_apply]
  continuous_toFun := forward_continuous H h
  continuous_invFun := inverse_continuous H h

lemma over_base (H : VectorBundleCore ℂ C ℂ ι) (h : B ≃ₜ C)
    (p : (core H h h.continuous).TotalSpace) : (homeomorph H h p).1 = h p.1 := rfl
lemma local_coordinate (H : VectorBundleCore ℂ C ℂ ι) (h : B ≃ₜ C)
    (i : ι) (p : (core H h h.continuous).TotalSpace) :
    (H.localTriv i (homeomorph H h p)).2 =
      ((core H h h.continuous).localTriv i p).2 := rfl
end LineCoreHomeomorphPullback318
