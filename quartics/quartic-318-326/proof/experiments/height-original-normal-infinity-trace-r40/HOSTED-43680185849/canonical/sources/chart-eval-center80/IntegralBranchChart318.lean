module
public import LinearRootCoordinate318
public import ThreeRootOrder318
public section
noncomputable section
namespace IntegralBranchChart318
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 4096
open Polynomial QuadraticPresentation318 LinearRootCoordinate318
open scoped TensorProduct
variable {F:Type*} [CommRing F] (c:Fˣ) (a:F) (d:Fin 3→Fˣ) (b:Fin 3→F)
abbrev Base:=F[X]
abbrev BranchBase:=LinearRootCoordinate318.Root c a
@[expose] def other (i:Fin 3) : Base (F:=F) := parameter (d i) (b i)
@[expose] def denominator : BranchBase c a :=
  ∏i:Fin 3,algebraMap (Base (F:=F)) (BranchBase c a) (other d b i)
abbrev OpenBase:=Localization.Away (denominator c a d b)
abbrev OriginalOrder:=BranchBase c a⊗[Base (F:=F)]ThreeRootOrder318.Order (other d b)
abbrev OpenOrder:=ThreeRootOrder318.Order
  (fun i=>algebraMap (Base (F:=F)) (OpenBase c a d b) (other d b i))

theorem denominator_at_branch :
    branchEvaluation c a (denominator c a d b)=∏i:Fin 3,(d i:F)*(a-b i) := by
  simp only [denominator,map_prod,other,branchEvaluation_other]

/-- Unlike field nonvanishing, this hypothesis gives an integral branch section. -/
theorem denominator_at_branch_unit (hb:∀i,IsUnit (a-b i)) :
    IsUnit (branchEvaluation c a (denominator c a d b)) := by
  rw [denominator_at_branch]
  have h : ∀ i : Fin 3, IsUnit ((d i:F)*(a-b i)) :=
    fun i => (d i).isUnit.mul (hb i)
  exact IsUnit.prod_univ_iff.mpr h

/-- The ramification point belongs to this integral neighborhood whenever
its three actual contact differences are units in the coefficient base. -/
@[expose] def branchPoint (hb:∀i,IsUnit (a-b i)) : OpenBase c a d b→+*F :=
  IsLocalization.Away.lift (denominator c a d b)
    (denominator_at_branch_unit c a d b hb)

@[simp] theorem branchPoint_on_base (hb:∀i,IsUnit (a-b i)) (z:BranchBase c a) :
    branchPoint c a d b hb (algebraMap (BranchBase c a) (OpenBase c a d b) z)=
      branchEvaluation c a z :=
  IsLocalization.Away.lift_eq _ _ _

theorem other_unit (i:Fin 3) :
    IsUnit (algebraMap (Base (F:=F)) (OpenBase c a d b) (other d b i)) := by
  rw [IsScalarTower.algebraMap_apply (Base (F:=F)) (BranchBase c a) (OpenBase c a d b)]
  apply IsLocalization.Away.isUnit_of_dvd (denominator c a d b)
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem two_unit (h2:IsUnit (2:F)) : IsUnit (2:OpenBase c a d b) := by
  simpa only [map_ofNat] using
    h2.map (algebraMap F (OpenBase c a d b))

local instance originalOrder_commRing : CommRing (OriginalOrder c a d b) := inferInstance
local instance originalOrder_algebra : Algebra (BranchBase c a) (OriginalOrder c a d b) := inferInstance
/-- The full original four-root order, now viewed over its genuine ramified
root coordinate, has this explicit localized three-root presentation. -/
@[expose] def localizedOrderEquiv :
    OpenBase c a d b⊗[BranchBase c a]OriginalOrder c a d b≃ₐ[OpenBase c a d b]
      OpenOrder c a d b :=
  (Algebra.TensorProduct.cancelBaseChange (Base (F:=F)) (BranchBase c a)
    (OpenBase c a d b) (OpenBase c a d b) (ThreeRootOrder318.Order (other d b))).trans
      (ThreeRootOrder318.baseChange (other d b) (OpenBase c a d b))

theorem open_finite_free_etale (h2:IsUnit (2:F)) :
    Module.Finite (OpenBase c a d b) (OpenOrder c a d b) ∧
    Module.Free (OpenBase c a d b) (OpenOrder c a d b) ∧
    Algebra.Etale (OpenBase c a d b) (OpenOrder c a d b) :=
  ⟨(ThreeRootOrder318.finite_free _).1,(ThreeRootOrder318.finite_free _).2,
    ThreeRootOrder318.etale _ (two_unit c a d b h2) (other_unit c a d b)⟩


end IntegralBranchChart318
