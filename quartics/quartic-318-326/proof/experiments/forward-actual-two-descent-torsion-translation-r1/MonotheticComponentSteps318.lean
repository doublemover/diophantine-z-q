module
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic
public section

/-! A finite quotient argument for the actual component-progression interface.
No Lie-group structure, circle uniformization or power-surjectivity is assumed. -/
namespace MonotheticComponentSteps318
open Set Filter TopologicalSpace
open scoped Topology
set_option maxHeartbeats 1000000

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

@[expose] def stepClosure (a : G) (k : ℕ) : AddSubgroup G :=
  (AddSubgroup.zmultiples (k • a)).topologicalClosure

/-- For a dense integer orbit, every positive-step closure is clopen. In the
quotient the dense generator has order dividing k. Its finite orbit is closed,
so it is the entire quotient, which is consequently finite and discrete. -/
theorem stepClosure_clopen (a : G) (hd : DenseRange (fun n : ℤ => n • a))
    (k : ℕ) (hk : 0<k) : IsClopen (stepClosure a k : Set G) := by
  let H : AddSubgroup G := stepClosure a k
  letI : IsClosed (H : Set G) := AddSubgroup.isClosed_topologicalClosure _
  let q : G →+ G ⧸ H := QuotientAddGroup.mk' H
  have hq : Continuous q := QuotientAddGroup.continuous_mk
  have hqd : DenseRange (fun n : ℤ => n • q a) := by
    have hd' := (QuotientAddGroup.mk'_surjective H).denseRange.comp hd hq
    simpa only [Function.comp_def,map_zsmul] using hd'
  have hkill : k • q a=0 := by
    rw [←map_nsmul]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact AddSubgroup.le_topologicalClosure _ (AddSubgroup.mem_zmultiples _)
  have horder : IsOfFinAddOrder (q a) :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k,hk,hkill⟩
  have hfinite : (AddSubgroup.zmultiples (q a) : Set (G ⧸ H)).Finite := by
    rw [←horder.multiples_eq_zmultiples]
    exact horder.finite_multiples
  have hfull : (AddSubgroup.zmultiples (q a) : Set (G ⧸ H))=univ := by
    apply eq_univ_of_forall
    intro x
    have hx := hqd x
    change x∈closure (AddSubgroup.zmultiples (q a) : Set (G ⧸ H)) at hx
    rwa [hfinite.isClosed.closure_eq] at hx
  have hQ : (univ : Set (G ⧸ H)).Finite := hfull ▸ hfinite
  letI : Finite (G ⧸ H) := finite_univ_iff.mp hQ
  refine ⟨AddSubgroup.isClosed_topologicalClosure _,?_⟩
  exact QuotientAddGroup.discreteTopology_iff.mp (inferInstance : DiscreteTopology (G ⧸ H))

/-- The identity component is contained in every positive-step closure.
This conclusion does not require a real additive cover of the component. -/
theorem component_subset_stepClosure (a : G) (hd : DenseRange (fun n : ℤ => n • a))
    (k : ℕ) (hk : 0<k) :
    connectedComponent (0:G)⊆(stepClosure a k : Set G) :=
  (stepClosure_clopen a hd k hk).connectedComponent_subset (AddSubgroup.zero_mem _)

/-- Once the step generator belongs to the identity component, its closure is
exactly that component. This replaces a separate step-surjectivity hypothesis. -/
theorem stepClosure_eq_component (a : G) (hd : DenseRange (fun n : ℤ => n • a))
    (k : ℕ) (hk : 0<k) (hstep : k • a∈connectedComponent (0:G)) :
    (stepClosure a k : Set G)=connectedComponent (0:G) := by
  apply subset_antisymm
  · change (AddSubgroup.zmultiples (k • a)).topologicalClosure ≤
      AddSubgroup.connectedComponentOfZero G
    apply AddSubgroup.topologicalClosure_minimal _ _ isClosed_connectedComponent
    rintro x ⟨n,rfl⟩
    exact (AddSubgroup.connectedComponentOfZero G).zsmul_mem hstep n
  · exact component_subset_stepClosure a hd k hk

/-- A fixed component-return multiple passes to every divisible step. The
existence of such a fixed m for the concrete elliptic orbit is not proved here. -/
theorem component_step_mem (a : G) (m k : ℕ) (hmk : m∣k)
    (hm : m • a∈connectedComponent (0:G)) : k • a∈connectedComponent (0:G) := by
  obtain ⟨l,rfl⟩ := hmk
  rw [Nat.mul_comm,mul_smul]
  exact (AddSubgroup.connectedComponentOfZero G).nsmul_mem hm l

/-- The historical component-annihilation premise now suffices for the exact
step-closure conclusion, without an additional divisibility theorem on G^0. -/
theorem component_multiple_closure (a : G) (hd : DenseRange (fun n : ℤ => n • a))
    (m k : ℕ) (hk : 0<k) (hmk : m∣k)
    (hm : m • a∈connectedComponent (0:G)) :
    (stepClosure a k : Set G)=connectedComponent (0:G) :=
  stepClosure_eq_component a hd k hk (component_step_mem a m k hmk hm)

/-- Positive tails in the actual component, with the exact translate retained.
The target remains an explicitly supplied open set meeting that component. -/
theorem component_positive_tail [CompactSpace G]
    (a : G) (hd : DenseRange (fun n : ℤ => n • a))
    (k : ℕ) (hk : 0<k) (hstep : k • a∈connectedComponent (0:G))
    (b : G) (hb : b∈connectedComponent (0:G)) (U : Set G) (ho : IsOpen U)
    (hne : ∃ x∈U, x∈connectedComponent (0:G)) (B : ℕ) :
    ∃ n : ℕ, B<n ∧ b+n • (k • a)∈U := by
  obtain ⟨x,hx,hxc⟩ := hne
  have hc : x-b∈stepClosure a k := by
    change x-b∈(stepClosure a k : Set G)
    rw [stepClosure_eq_component a hd k hk hstep]
    exact (AddSubgroup.connectedComponentOfZero G).sub_mem hxc hb
  have hrec := mapClusterPt_atTop_nsmul_iff_mem_topologicalClosure_zmultiples.mpr hc
  have hnb : (fun y : G => b+y) ⁻¹' U ∈ 𝓝 (x-b) :=
    (ho.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa [add_comm] using hx)
  exact frequently_atTop'.mp (hrec.frequently hnb) B

end MonotheticComponentSteps318
