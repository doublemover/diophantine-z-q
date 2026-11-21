module

public import SelectedActualAbelSameExponentialLatticeQuotient318
public import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Topology.Algebra.Group.Basic

public section

noncomputable section

open Set Topology
open SelectedActualAbelIdentityChartLifts318
open SelectedActualAbelSameExponentialLatticeQuotient318

namespace SelectedActualAbelLiteralExponentialKernel318

variable {V J : Type*} [AddCommGroup V] [AddCommGroup J]

/-- The literal kernel of the prescribed exponential, viewed as its
integer submodule. This does not choose any lattice or new quotient. -/
@[expose] def literalExponentialKernel (q : V →+ J) : Submodule ℤ V where
  carrier := {v | q v = 0}
  zero_mem' := map_zero q
  add_mem' := by
    intro x y hx hy
    change q x = 0 at hx
    change q y = 0 at hy
    change q (x + y) = 0
    rw [map_add q,hx,hy,zero_add]
  smul_mem' := by
    intro n x hx
    change q x = 0 at hx
    change q (n • x) = 0
    rw [map_zsmul q,hx,zsmul_zero]

theorem mem_literal_kernel (q : V →+ J) (v : V) :
    q v = 0 ↔ v ∈ literalExponentialKernel q := by rfl

section Topological

variable {W T : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]

/-- The actual normalized identity chart makes this same exponential
kernel discrete. No topological statement is assumed for the kernel. -/
theorem literal_kernel_discrete (q : W →+ T) (C : IdentityChart q) :
    DiscreteTopology (literalExponentialKernel q) := by
  obtain ⟨U,hU,h0,hinj⟩ := exists_open_local_injectivity q C
  let L := literalExponentialKernel q
  have he : (Subtype.val : L → W) ⁻¹' U = ({0} : Set L) := by
    ext x
    constructor
    · intro hx
      have hxU : (x : W) ∈ U := hx
      have hxq : q x.val = 0 := (mem_literal_kernel q x.val).mpr x.property
      have h := hinj hxU h0 (hxq.trans (map_zero q).symm)
      exact Set.mem_singleton_iff.mpr (Subtype.ext h)
    · intro hz
      have h : x = 0 := Set.mem_singleton_iff.mp hz
      have hval : x.val = (0 : W) := congrArg Subtype.val h
      change x.val ∈ U
      rw [hval]
      exact h0
  apply discreteTopology_of_isOpen_singleton_zero
  change IsOpen ({0} : Set L)
  rw [←he]
  exact hU.preimage continuous_subtype_val

end Topological

end SelectedActualAbelLiteralExponentialKernel318

#print axioms SelectedActualAbelLiteralExponentialKernel318.literal_kernel_discrete
