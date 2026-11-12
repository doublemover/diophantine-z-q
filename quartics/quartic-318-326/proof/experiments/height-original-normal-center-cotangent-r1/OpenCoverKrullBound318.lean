module
public import Mathlib.Topology.KrullDimension
public section
noncomputable section
namespace OpenCoverKrullBound318
open Order TopologicalSpace
universe u v w
variable {X:Type u} [TopologicalSpace X] [QuasiSober X] [T0Space X]
variable {ι:Type v} (Y:ι→Type w) [∀i,TopologicalSpace (Y i)]
  [∀i,QuasiSober (Y i)] [∀i,T0Space (Y i)]
attribute [local instance] specializationOrder
/-- Genuine global topological Krull bound from a jointly surjective
family of actual open embeddings. Coheight is unchanged by an open
embedding at each point; no bound only on selected closed points is used. -/
theorem dimension_le (f:∀i,Y i→X)
    (hf:∀i,Topology.IsOpenEmbedding (f i))
    (hcover:∀x:X,∃i y,f i y=x) (n:WithBot ℕ∞)
    (hdim:∀i,topologicalKrullDim (Y i)≤n):topologicalKrullDim X≤n:=by
  have hX:topologicalKrullDim X=Order.krullDim X:=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α:=X))
  rw [hX,Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨i,y,rfl⟩:=hcover x
  rw [Topology.IsOpenEmbedding.coheight_eq (f i) (hf i)]
  have hY:topologicalKrullDim (Y i)=Order.krullDim (Y i):=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α:=Y i))
  apply (Order.coheight_le_krullDim y).trans
  rw [←hY]
  exact hdim i
end OpenCoverKrullBound318
