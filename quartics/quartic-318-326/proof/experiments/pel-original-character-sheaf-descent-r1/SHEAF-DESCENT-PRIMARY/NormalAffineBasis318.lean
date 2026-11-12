module
public import AffineDominantNormRestriction318
public section
noncomputable section
namespace NormalAffineBasis318
open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (Y:Scheme.{u}) [IsIntegral Y]
/-- Local normal affine data for the actual scheme, rather than a named
normality surrogate or a generic-point assertion. -/
@[expose] def HasBasis:Prop:=∀(U:Y.Opens)(x:U),∃V:Y.Opens,
  V≤U ∧ x.1∈V ∧ IsAffineOpen V ∧ IsIntegrallyClosed Γ(Y,V)
lemma basic_normal {U:Y.Opens} [Nonempty U] [IsIntegrallyClosed Γ(Y,U)]
    (hU:IsAffineOpen U) (s:Γ(Y,U)) [Nonempty (Y.basicOpen s)]:
    IsIntegrallyClosed Γ(Y,Y.basicOpen s):=by
  letI:IsLocalization.Away s Γ(Y,Y.basicOpen s):=hU.isLocalization_basicOpen s
  apply isIntegrallyClosed_of_isLocalization Γ(Y,Y.basicOpen s) (Submonoid.powers s)
  intro a ha
  rcases ha with ⟨n,rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  apply pow_ne_zero
  intro hs
  have he:Y.basicOpen s=⊥:=by simp [hs]
  have ⟨x⟩:Nonempty (Y.basicOpen s):=inferInstance
  simpa [he] using x.2
lemma of_cover {ι:Type u} (V:ι→Y.Opens) (cover:∀x:Y,∃i,x∈V i)
    (affine:∀i,IsAffineOpen (V i)) (normal:∀i,IsIntegrallyClosed Γ(Y,V i)):
    HasBasis Y:=by
  intro U x
  obtain ⟨i,hi⟩:=cover x
  letI:Nonempty (V i):=⟨⟨x,hi⟩⟩
  letI:IsIntegrallyClosed Γ(Y,V i):=normal i
  obtain ⟨s,hs,hx⟩:=(affine i).exists_basicOpen_le x hi
  letI:Nonempty (Y.basicOpen s):=⟨⟨x,hx⟩⟩
  exact ⟨Y.basicOpen s,hs,hx,(affine i).basicOpen s,basic_normal Y (affine i) s⟩
end NormalAffineBasis318
