module
public import RingEvenOddSeries318
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public section
noncomputable section
namespace RingQuadraticBasis318
set_option maxHeartbeats 0
open PowerSeries RingEvenOddSeries318 Module
variable (k:Type*) [CommRing k] [IsDomain k]

/-- A distinct copy of the actual covering formal series ring. -/
@[expose] def Cover := ULift.{0} k⟦X⟧
instance : CommRing (Cover k) := inferInstanceAs (CommRing (ULift k⟦X⟧))

@[expose] def toSeries : Cover k ≃+* k⟦X⟧ := ULift.ringEquiv
instance : IsDomain (Cover k) := (toSeries k).injective.isDomain (toSeries k).toRingHom
@[expose] def baseMap : k⟦X⟧ →+* Cover k :=
  (toSeries k).symm.toRingHom.comp (expandTwo (k:=k)).toRingHom
instance : Algebra k⟦X⟧ (Cover k) := (baseMap k).toAlgebra

@[expose] def quadraticAlgEquiv : QuadraticAlgebra k⟦X⟧ X 0 ≃ₐ[k⟦X⟧] Cover k where
  __ := (quadraticEquiv (k:=k)).trans (toSeries k).symm
  commutes' a := by
    apply (toSeries k).injective
    change expandTwo (QuadraticAlgebra.re (algebraMap k⟦X⟧ (QuadraticAlgebra k⟦X⟧ X 0) a))+
      X*expandTwo (QuadraticAlgebra.im (algebraMap k⟦X⟧ (QuadraticAlgebra k⟦X⟧ X 0) a))=expandTwo a
    simp

@[expose] def basis : Basis (Fin 2) k⟦X⟧ (Cover k) :=
  (QuadraticAlgebra.basis (X:k⟦X⟧) 0).map (quadraticAlgEquiv k).toLinearEquiv

instance : Module.Free k⟦X⟧ (Cover k) := .of_basis (basis k)
instance : Module.Finite k⟦X⟧ (Cover k) := .of_basis (basis k)

theorem rank_two : Module.finrank k⟦X⟧ (Cover k)=2 := by
  rw [Module.finrank_eq_card_basis (basis k)]
  rfl

@[expose] def root : Cover k := (toSeries k).symm X

theorem basis_zero : basis k 0=1 := by
  simp only [basis,Basis.map_apply,QuadraticAlgebra.basis_apply_zero,AlgEquiv.toLinearEquiv_apply,map_one]

theorem basis_one : basis k 1=root k := by
  apply (toSeries k).injective
  simp [basis,quadraticAlgEquiv,quadraticEquiv,quadraticMap,root]

@[expose] def powerBasis : PowerBasis k⟦X⟧ (Cover k) where
  gen:=root k
  dim:=2
  basis:=basis k
  basis_eq_pow i:=by fin_cases i <;> simp [basis_zero,basis_one]

theorem base_parameter : algebraMap k⟦X⟧ (Cover k) X=(root k)^2 := by
  apply (toSeries k).injective
  simp only [map_pow]
  change expandTwo (X:k⟦X⟧)=X^2
  rw [expandTwo,expand_apply,subst_X (HasSubst.X_pow (by decide))]

end RingQuadraticBasis318
