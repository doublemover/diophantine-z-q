module
public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public section
noncomputable section
namespace CharacteristicPartialEquiv318
attribute [local instance] Classical.propDecidable
open Set Metric
variable {E X : Type*} [NormedAddCommGroup E] [TopologicalSpace X]

/-- Package actual closed-disk characteristic data and an agreeing open-cell
homeomorphism as the PartialEquiv required by the classical CW interface.
The closed-disk map may identify boundary points. -/
@[expose] def cellMap (c : closedBall (0:E) 1 → X) (S : Set X)
    (h : ball (0:E) 1 ≃ₜ S)
    (agree : ∀ z : ball (0:E) 1, c ⟨z.val,z.property.le⟩=(h z).val) :
    PartialEquiv E X where
  toFun z := if hz : z∈closedBall (0:E) 1 then c ⟨z,hz⟩ else c ⟨0,by simp⟩
  invFun y := if hy : y∈S then (h.symm ⟨y,hy⟩).val else 0
  source := ball (0:E) 1
  target := S
  map_source' := by
    intro z hz
    simp only [dif_pos hz.le]
    rw [agree ⟨z,hz⟩]
    exact (h ⟨z,hz⟩).property
  map_target' := by
    intro y hy
    simp only [dif_pos hy]
    exact (h.symm ⟨y,hy⟩).property
  left_inv' := by
    intro z hz
    have hzc : z∈closedBall (0:E) 1 := hz.le
    simp only [dif_pos hzc]
    rw [agree ⟨z,hz⟩]
    simp only [dif_pos (h ⟨z,hz⟩).property]
    exact congrArg Subtype.val (h.symm_apply_apply ⟨z,hz⟩)
  right_inv' := by
    intro y hy
    simp only [dif_pos hy]
    have hz := (h.symm ⟨y,hy⟩).property
    simp only [dif_pos hz.le]
    rw [agree (h.symm ⟨y,hy⟩)]
    exact congrArg Subtype.val (h.apply_symm_apply ⟨y,hy⟩)

theorem source (c : closedBall (0:E) 1 → X) (S : Set X) (h : ball (0:E) 1 ≃ₜ S)
    (agree : ∀ z : ball (0:E) 1, c ⟨z.val,z.property.le⟩=(h z).val) :
    (cellMap c S h agree).source=ball (0:E) 1 := rfl

theorem target (c : closedBall (0:E) 1 → X) (S : Set X) (h : ball (0:E) 1 ≃ₜ S)
    (agree : ∀ z : ball (0:E) 1, c ⟨z.val,z.property.le⟩=(h z).val) :
    (cellMap c S h agree).target=S := rfl

theorem on_closed (c : closedBall (0:E) 1 → X) (S : Set X) (h : ball (0:E) 1 ≃ₜ S)
    (agree : ∀ z : ball (0:E) 1, c ⟨z.val,z.property.le⟩=(h z).val)
    (z : closedBall (0:E) 1) : cellMap c S h agree z.val=c z := by
  simp only [cellMap,dif_pos z.property]

theorem continuousOn_closed (c : closedBall (0:E) 1 → X) (hc : Continuous c)
    (S : Set X) (h : ball (0:E) 1 ≃ₜ S)
    (agree : ∀ z : ball (0:E) 1, c ⟨z.val,z.property.le⟩=(h z).val) :
    ContinuousOn (cellMap c S h agree) (closedBall (0:E) 1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have he : (fun z : closedBall (0:E) 1 => cellMap c S h agree z.val)=c :=
    funext (on_closed c S h agree)
  change Continuous (fun z : closedBall (0:E) 1 => cellMap c S h agree z.val)
  rw [he]
  exact hc

theorem continuousOn_inverse (c : closedBall (0:E) 1 → X) (S : Set X)
    (h : ball (0:E) 1 ≃ₜ S)
    (agree : ∀ z : ball (0:E) 1, c ⟨z.val,z.property.le⟩=(h z).val) :
    ContinuousOn (cellMap c S h agree).symm S := by
  apply continuousOn_iff_continuous_restrict.mpr
  have he : (fun y : S => (cellMap c S h agree).symm y.val)=
      (fun y : S => (h.symm y).val) := by
    funext y
    simp only [cellMap,PartialEquiv.symm,dif_pos y.property]
  change Continuous (fun y : S => (cellMap c S h agree).symm y.val)
  rw [he]
  exact continuous_subtype_val.comp h.symm.continuous

theorem open_image (c : closedBall (0:E) 1 → X) (S : Set X) (h : ball (0:E) 1 ≃ₜ S)
    (agree : ∀ z : ball (0:E) 1, c ⟨z.val,z.property.le⟩=(h z).val) :
    cellMap c S h agree '' ball (0:E) 1=S := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (cellMap c S h agree).map_source hx
  · intro hy
    let z := h.symm ⟨y,hy⟩
    refine ⟨z.val,z.property,?_⟩
    rw [on_closed c S h agree ⟨z.val,z.property.le⟩,agree z]
    exact congrArg Subtype.val (h.apply_symm_apply ⟨y,hy⟩)

theorem closed_image (c : closedBall (0:E) 1 → X) (S : Set X) (h : ball (0:E) 1 ≃ₜ S)
    (agree : ∀ z : ball (0:E) 1, c ⟨z.val,z.property.le⟩=(h z).val) :
    cellMap c S h agree '' closedBall (0:E) 1=Set.range c := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,(on_closed c S h agree ⟨x,hx⟩).symm⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x.val,x.property,on_closed c S h agree x⟩
end CharacteristicPartialEquiv318
