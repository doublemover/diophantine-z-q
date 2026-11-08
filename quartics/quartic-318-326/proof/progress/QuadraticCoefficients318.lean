module
public import EvenContactEtale318
public section
noncomputable section
namespace QuadraticCoefficients318
open Polynomial EvenContactEtale318
set_option maxHeartbeats 500000
variable {R:Type*} [CommRing R] (u:Rˣ)

/-- Every element of the actual quadratic root algebra has a constant
and a root coefficient, over arbitrary commutative rings. -/
theorem exists_coefficients (z:RootRing u) :
    ∃a b:R,z=algebraMap R (RootRing u) a+algebraMap R (RootRing u) b*root u:=by
  obtain ⟨f,rfl⟩:=AdjoinRoot.mk_surjective z
  induction f using Polynomial.induction_on with
  | C a => exact ⟨a,0,by simp [AdjoinRoot.mk_C]⟩
  | add f g hf hg =>
    obtain ⟨a,b,hf⟩:=hf
    obtain ⟨c,d,hg⟩:=hg
    refine ⟨a+c,b+d,?_⟩
    rw [map_add,hf,hg,map_add,map_add]
    ring
  | monomial n a ih =>
    obtain ⟨b,c,hbc⟩:=ih
    refine ⟨c*(u:R),b,?_⟩
    rw [pow_succ,←mul_assoc,map_mul,hbc,AdjoinRoot.mk_X,map_mul]
    change (algebraMap R (RootRing u) b+algebraMap R (RootRing u) c*root u)*root u=_
    rw [add_mul,mul_assoc,←pow_two,root_square]
    ring

end QuadraticCoefficients318
