module
public import PELQuotientBranchIsolation318
public section
noncomputable section
namespace OpenImageHomeomorphChart318
open TopologicalSpace
set_option maxHeartbeats 1600000
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An actual homeomorphism of nonempty open subspaces gives an ambient
open partial homeomorphism, preserving the literal source and target. -/
@[expose] def extend (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hne : Nonempty U) (e : U≃ₜV) : OpenPartialHomeomorph X Y :=
  (((⟨U,hU⟩:Opens X).openPartialHomeomorphSubtypeCoe hne).symm.trans
    e.toOpenPartialHomeomorph).trans
      ((⟨V,hV⟩:Opens Y).openPartialHomeomorphSubtypeCoe ⟨e (Classical.choice hne)⟩)

theorem extend_source (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hne : Nonempty U) (e : U≃ₜV) : (extend U V hU hV hne e).source=U := by
  simp only [extend,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
    Opens.openPartialHomeomorphSubtypeCoe_source,Opens.openPartialHomeomorphSubtypeCoe_target,
    Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]

theorem extend_target (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hne : Nonempty U) (e : U≃ₜV) : (extend U V hU hV hne e).target=V := by
  simp only [extend,OpenPartialHomeomorph.trans_target,OpenPartialHomeomorph.symm_target,
    Opens.openPartialHomeomorphSubtypeCoe_source,Opens.openPartialHomeomorphSubtypeCoe_target,
    Homeomorph.toOpenPartialHomeomorph_target,Set.preimage_univ,Set.inter_univ]

theorem extend_value (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hne : Nonempty U) (e : U≃ₜV) (x : U) : extend U V hU hV hne e x=(e x:Y) := by
  let I := (⟨U,hU⟩:Opens X).openPartialHomeomorphSubtypeCoe hne
  have hi : I.symm (x:X)=x := I.left_inv (Set.mem_univ x)
  change (e (I.symm (x:X)):Y)=(e x:Y)
  rw [hi]
end OpenImageHomeomorphChart318
