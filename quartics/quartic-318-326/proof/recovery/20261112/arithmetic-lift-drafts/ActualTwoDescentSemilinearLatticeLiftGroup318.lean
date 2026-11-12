module
public import ActualTwoDescentOriginalTwoTorsionLiftMultiplication318
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public section
noncomputable section
namespace ActualTwoDescentSemilinearLatticeLiftGroup318
structure Data (G F X : Type*) [Group G] [Field F] where
  sigma : G → F ≃+* F
  sigma_one : ∀ f,sigma 1 f=f
  sigma_mul : ∀ g h f,sigma (g*h) f=sigma g (sigma h f)
  point : G → X → X
  point_one : ∀ x,point 1 x=x
  point_mul : ∀ g h x,point (g*h) x=point h (point g x)
  lattice : X → Set F
variable {G F X : Type*} [Group G] [Field F] (D : Data G F X)
def Semilinear (g : G) (u : Equiv.Perm F) : Prop :=
  ∀ f h,u (f*h)=D.sigma g f*u h
def Preserves (g : G) (u : Equiv.Perm F) : Prop :=
  ∀ x f,f∈D.lattice (D.point g x) ↔ u f∈D.lattice x
lemma sigma_cancel (g : G) (f : F) : D.sigma g (D.sigma g⁻¹ f)=f := by
  rw [←D.sigma_mul,mul_inv_cancel,D.sigma_one]
lemma point_cancel (g : G) (x : X) : D.point g (D.point g⁻¹ x)=x := by
  rw [←D.point_mul,inv_mul_cancel,D.point_one]
def subgroup : Subgroup (G × Equiv.Perm F) where
  carrier := {u | Semilinear D u.1 u.2 ∧ Preserves D u.1 u.2}
  one_mem' := by
    constructor
    · intro f h
      change f*h=D.sigma 1 f*h
      rw [D.sigma_one]
    · intro x f
      change f∈D.lattice (D.point 1 x) ↔ f∈D.lattice x
      rw [D.point_one]
  mul_mem' := by
    rintro u v ⟨hu,huL⟩ ⟨hv,hvL⟩
    constructor
    · intro f h
      change u.2 (v.2 (f*h))=D.sigma (u.1*v.1) f*u.2 (v.2 h)
      rw [hv,hu,D.sigma_mul]
    · intro x f
      change f∈D.lattice (D.point (u.1*v.1) x) ↔ u.2 (v.2 f)∈D.lattice x
      rw [D.point_mul,hvL,huL]
  inv_mem' := by
    rintro u ⟨hu,huL⟩
    constructor
    · intro f h
      change u.2.symm (f*h)=D.sigma u.1⁻¹ f*u.2.symm h
      apply u.2.injective
      rw [Equiv.apply_symm_apply,hu,sigma_cancel,Equiv.apply_symm_apply]
    · intro x f
      change f∈D.lattice (D.point u.1⁻¹ x) ↔ u.2.symm f∈D.lattice x
      have hh := huL (D.point u.1⁻¹ x) (u.2.symm f)
      rw [point_cancel,Equiv.apply_symm_apply] at hh
      exact hh.symm
abbrev Lift := subgroup D
def projection : Lift D →* G where
  toFun u := u.val.1
  map_one' := rfl
  map_mul' _ _ := rfl
def operator (u : Lift D) : Equiv.Perm F := u.val.2
lemma multiply_apply (u v : Lift D) (f : F) :
    operator D (u*v) f=operator D u (operator D v f) := rfl
lemma inverse_apply (u : Lift D) (f : F) :
    operator D u⁻¹ f=(operator D u).symm f := rfl
lemma semilinear (u : Lift D) (f h : F) :
    operator D u (f*h)=D.sigma (projection D u) f*operator D u h := u.property.1 f h
lemma preserves (u : Lift D) (x : X) (f : F) :
    f∈D.lattice (D.point (projection D u) x) ↔ operator D u f∈D.lattice x := u.property.2 x f
end ActualTwoDescentSemilinearLatticeLiftGroup318
