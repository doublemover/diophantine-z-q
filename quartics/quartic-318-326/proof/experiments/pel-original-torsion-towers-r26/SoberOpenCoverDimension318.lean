module
public import Mathlib.Topology.KrullDimension
public section
noncomputable section
namespace SoberOpenCoverDimension318
open TopologicalSpace Topology Order
attribute [local instance] specializationOrder
variable {X : Type*} [TopologicalSpace X] [T0Space X] [QuasiSober X]
lemma dimension_points : topologicalKrullDim X=Order.krullDim X :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
/-- A genuine open cover bounds the native Krull dimension of a sober
space through ALL points and their coheights, not only closed points. -/
lemma dimension_le {ι : Type*} (Y : ι→Type*) [∀ i,TopologicalSpace (Y i)]
    [∀ i,T0Space (Y i)] [∀ i,QuasiSober (Y i)]
    (f : ∀ i,Y i→X) (hf : ∀ i,IsOpenEmbedding (f i))
    (hcover : ∀ x,∃ i y,f i y=x) (d : WithBot ℕ∞)
    (hd : ∀ i,topologicalKrullDim (Y i)≤d) : topologicalKrullDim X≤d := by
  rw [dimension_points,Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨i,y,rfl⟩ := hcover x
  rw [Topology.IsOpenEmbedding.coheight_eq (f i) (hf i)]
  exact (Order.coheight_le_krullDim y).trans (by
    rw [←dimension_points]
    exact hd i)
end SoberOpenCoverDimension318
