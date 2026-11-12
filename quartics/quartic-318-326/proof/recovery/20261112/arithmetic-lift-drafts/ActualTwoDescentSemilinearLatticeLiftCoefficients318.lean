module
public import ActualTwoDescentSemilinearLatticeLiftGroup318
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public section
noncomputable section
namespace ActualTwoDescentSemilinearLatticeLiftCoefficients318
open ActualTwoDescentSemilinearLatticeLiftGroup318
variable {G F X : Type*} [Group G] [Field F] (D : Data G F X)
lemma formula (u : Lift D) (f : F) :
    operator D u f=operator D u 1*D.sigma (projection D u) f := by
  have h := semilinear D u f 1
  simpa only [mul_one,mul_comm] using h
lemma zero (u : Lift D) : operator D u 0=0 := by rw [formula,map_zero,mul_zero]
lemma coefficient_ne (u : Lift D) : operator D u 1≠0 := by
  intro h
  have hh : operator D u 1=operator D u 0 := h.trans (zero D u).symm
  exact one_ne_zero ((operator D u).injective hh)
def coefficient (u : Lift D) : Fˣ := Units.mk0 (operator D u 1) (coefficient_ne D u)
lemma additive (u : Lift D) (f h : F) :
    operator D u (f+h)=operator D u f+operator D u h := by
  simp only [formula,map_add,mul_add]
lemma coefficient_product (u v : Lift D) :
    (coefficient D (u*v) : F)=(coefficient D u : F)*
      D.sigma (projection D u) (coefficient D v : F) := by
  change operator D u (operator D v 1)=operator D u 1*D.sigma (projection D u) (operator D v 1)
  exact formula D u _
lemma kernel (u : Lift D) (hu : projection D u=1) :
    (∀ f,operator D u f=(coefficient D u : F)*f) ∧
    (∀ x f,f∈D.lattice x ↔ (coefficient D u : F)*f∈D.lattice x) := by
  have hf : ∀ f,operator D u f=(coefficient D u : F)*f := by
    intro f
    rw [formula,hu,D.sigma_one] <;> rfl
  refine ⟨hf,?_⟩
  intro x f
  simpa only [hu,D.point_one,hf] using preserves D u x f
lemma ext (u v : Lift D) (hbase : projection D u=projection D v)
    (hc : coefficient D u=coefficient D v) : u=v := by
  apply Subtype.ext
  apply Prod.ext hbase
  apply Equiv.ext
  intro f
  change operator D u f=operator D v f
  rw [formula,formula,hbase]
  exact congrArg (fun a : Fˣ => (a:F)*D.sigma (projection D v) f) hc
def ofKernelUnit (a : Fˣ)
    (ha : ∀ x f,f∈D.lattice x ↔ (a:F)*f∈D.lattice x) : Lift D := by
  let u : Equiv.Perm F :=
    { toFun := fun f => (a:F)*f
      invFun := fun f => (↑a⁻¹:F)*f
      left_inv := by intro f; simp [←mul_assoc]
      right_inv := by intro f; simp [←mul_assoc] }
  refine ⟨(1,u),?_,?_⟩
  · intro f h
    change (a:F)*(f*h)=D.sigma 1 f*((a:F)*h)
    rw [D.sigma_one]
    ring
  · intro x f
    change f∈D.lattice (D.point 1 x) ↔ (a:F)*f∈D.lattice x
    rw [D.point_one]
    exact ha x f
lemma ofKernelUnit_base (a : Fˣ) (ha) : projection D (ofKernelUnit D a ha)=1 := rfl
lemma ofKernelUnit_coefficient (a : Fˣ) (ha) : coefficient D (ofKernelUnit D a ha)=a := by
  apply Units.ext
  change (a:F)*1=(a:F)
  exact mul_one _
lemma kernel_reconstruct (u : Lift D) (hu : projection D u=1) :
    ofKernelUnit D (coefficient D u) (kernel D u hu).2=u := by
  apply ext D
  · exact hu.symm
  · exact ofKernelUnit_coefficient D _ _
end ActualTwoDescentSemilinearLatticeLiftCoefficients318
