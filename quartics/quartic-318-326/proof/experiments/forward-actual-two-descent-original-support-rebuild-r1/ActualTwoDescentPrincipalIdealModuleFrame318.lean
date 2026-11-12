module
public import ActualTwoDescentRootLocalizedIdeals318
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public section
noncomputable section
namespace ActualTwoDescentPrincipalIdealModuleFrame318
variable {S : Type*} [CommRing S] [IsDomain S]

/-- Multiplication by the actual ideal generator, retaining the ideal
as a native S-module rather than replacing it by a formal rank-one token. -/
def principalFrameMap (I : Ideal S) (g : S) (hg : g∈I) : S →ₗ[S] I where
  toFun a := ⟨a*g,I.mul_mem_left a hg⟩
  map_add' a b := by apply Subtype.ext; exact add_mul a b g
  map_smul' a b := by apply Subtype.ext; exact mul_assoc a b g

lemma actual_principal_frame_bijective (I : Ideal S) (g : S)
    (hg : g∈I) (hI : I=Ideal.span {g}) (hg0 : g≠0) :
    Function.Bijective (principalFrameMap I g hg) := by
  constructor
  · intro a b h
    exact mul_right_cancel₀ hg0 (congrArg Subtype.val h)
  · intro x
    have hx : (x : S)∈Ideal.span {g} := hI ▸ x.property
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp hx
    refine ⟨a,?_⟩
    apply Subtype.ext
    change a*g=(x:S)
    simpa only [mul_comm] using ha

def principalModuleFrame (I : Ideal S) (g : S)
    (hI : I=Ideal.span {g}) (hg0 : g≠0) : S ≃ₗ[S] I :=
  LinearEquiv.ofBijective (principalFrameMap I g
    (hI.symm ▸ Ideal.subset_span (Set.mem_singleton g)))
    (actual_principal_frame_bijective I g _ hI hg0)
@[simp] lemma actual_principal_frame_value (I : Ideal S) (g : S)
    (hI : I=Ideal.span {g}) (hg0 : g≠0) (a : S) :
    (principalModuleFrame I g hI hg0 a : S)=a*g := rfl

/-- Explicit unit scaling in the SAME scalar ring. -/
def unitScale (e : Sˣ) : S ≃ₗ[S] S where
  toFun a := a*(e:S)
  invFun a := a*(e⁻¹:Sˣ)
  left_inv a := by rw [mul_assoc,Units.mul_inv,mul_one]
  right_inv a := by rw [mul_assoc,Units.inv_mul,mul_one]
  map_add' a b := add_mul a b _
  map_smul' a b := mul_assoc a b _
end ActualTwoDescentPrincipalIdealModuleFrame318
