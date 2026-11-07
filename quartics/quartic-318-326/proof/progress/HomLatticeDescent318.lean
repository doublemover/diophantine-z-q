module
public import MatrixThreeTorsion318
public section
namespace HomLatticeDescent318
open MatrixCongruence318
set_option maxHeartbeats 0
noncomputable section
variable {n:Type*} [Fintype n] [DecidableEq n]

/-- The actual principal congruence kernel modulo3 is torsion-free. -/
theorem finite_order_GL_eq_one (A:Matrix.GeneralLinearGroup n ℤ)
    (hA:modThree (A:Matrix n n ℤ)=1) (hfin:IsOfFinOrder A) : A=1 := by
  apply Units.val_injective
  exact finite_order_eq_one _ hA (Units.isOfFinOrder_val.mpr hfin)

/-- A representation of a finite group on an integral lattice is trivial
if its actual matrices are the identity modulo3. -/
theorem finite_group_representation_trivial {G:Type*} [Group G] [Finite G]
    (rho:G→*Matrix.GeneralLinearGroup n ℤ)
    (hmod:∀g,modThree (rho g:Matrix n n ℤ)=1) : ∀g,rho g=1 := by
  intro g
  exact finite_order_GL_eq_one (rho g) (hmod g) (rho.isOfFinOrder (isOfFinOrder_of_finite g))

/-- The Galois group itself can be infinite: a finite image, together with
triviality modulo3, suffices for the actual integral action to be trivial. -/
theorem finite_image_representation_trivial {G:Type*} [Group G]
    (rho:G→*Matrix.GeneralLinearGroup n ℤ) (hfin:(Set.range rho).Finite)
    (hmod:∀g,modThree (rho g:Matrix n n ℤ)=1) : ∀g,rho g=1 := by
  haveI:Finite rho.range:=hfin
  intro g
  let x:rho.range:=⟨rho g,⟨g,rfl⟩⟩
  have hx:IsOfFinOrder (rho g):=rho.range.subtype.isOfFinOrder (isOfFinOrder_of_finite x)
  exact finite_order_GL_eq_one (rho g) (hmod g) hx

end
end HomLatticeDescent318
#print axioms HomLatticeDescent318.finite_image_representation_trivial
