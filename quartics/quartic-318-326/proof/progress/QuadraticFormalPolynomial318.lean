module
public import QuadraticFormalBasis318
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.DedekindDomain.Different
public section
noncomputable section
namespace QuadraticFormalPolynomial318
set_option maxHeartbeats 0
open PowerSeries QuadraticFormalBasis318 Module
variable (k:Type*) [Field k]

instance : IsDiscreteValuationRing (Cover k) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (toSeries k).symm

@[expose] def polynomial : Polynomial k⟦X⟧ := Polynomial.X^2-Polynomial.C PowerSeries.X

theorem monic : (polynomial k).Monic := Polynomial.monic_X_pow_sub_C _ (by decide)

theorem degree_two : (polynomial k).degree=2 := by
  rw [Polynomial.degree_eq_natDegree (monic k).ne_zero]
  simp [polynomial,Polynomial.natDegree_X_pow_sub_C]

theorem root_equation : Polynomial.aeval (root k) (polynomial k)=0 := by
  simp only [polynomial,map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C]
  rw [base_parameter,sub_self]

theorem minpoly_root : minpoly k⟦X⟧ (root k)=polynomial k := by
  apply minpoly.eq_of_linearIndependent k⟦X⟧ (root k) (monic k) (root_equation k) 2 (degree_two k)
  have h: (fun i:Fin 2=>(root k)^i.val)=basis k := by
    funext i
    exact ((powerBasis k).basis_eq_pow i).symm
  rw [h]
  exact (basis k).linearIndependent

theorem derivative_value :
    Polynomial.aeval (root k) (Polynomial.derivative (minpoly k⟦X⟧ (root k)))=2*root k := by
  rw [minpoly_root]
  norm_num [polynomial,Polynomial.derivative_pow]
  exact Or.inl (map_ofNat (algebraMap k⟦X⟧ (Cover k)) 2)

/-- The actual monogenic conductor is the unit ideal. -/
theorem conductor_top : conductor k⟦X⟧ (root k)=⊤ :=
  conductor_eq_top_of_powerBasis (powerBasis k)

end QuadraticFormalPolynomial318
