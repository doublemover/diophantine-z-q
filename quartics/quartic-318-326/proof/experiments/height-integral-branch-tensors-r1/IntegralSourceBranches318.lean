module
public import IntegralBranchChart318
public import FourRootPivot318
public section
noncomputable section
namespace IntegralSourceBranches318
open Polynomial FourRootPivot318
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R]
@[expose] def contacts : Fin 4 → R := ![0,32,76832,-343]
variable (c : Fin 4 → Rˣ)
@[expose] def coefficient (i : Fin 4) : R[X] :=
  LinearRootCoordinate318.parameter (c i) (contacts R i)
abbrev SourceOrder := FourRootOrder318.Order (coefficient R c)
@[expose] def otherTwist (i : Fin 4) (j : Fin 3) : Rˣ := c (indices i j.succ)
@[expose] def otherContact (i : Fin 4) (j : Fin 3) : R := contacts R (indices i j.succ)
abbrev BranchBase (i : Fin 4) := IntegralBranchChart318.BranchBase (c i) (contacts R i)
abbrev OpenBase (i : Fin 4) := IntegralBranchChart318.OpenBase
  (c i) (contacts R i) (otherTwist R c i) (otherContact R i)
abbrev OpenOrder (i : Fin 4) := IntegralBranchChart318.OpenOrder
  (c i) (contacts R i) (otherTwist R c i) (otherContact R i)
abbrev RegroupedOrder (i : Fin 4) := IntegralBranchChart318.OriginalOrder
  (c i) (contacts R i) (otherTwist R c i) (otherContact R i)

/-- The original four-root order is regrouped at every one of its actual contacts. -/
@[expose] def sourceRegroup (i : Fin 4) :
    SourceOrder R c ≃ₐ[R[X]] RegroupedOrder R c i :=
  Fin.cases (FourRootPivot318.regroup (coefficient R c) 0)
    (Fin.cases (FourRootPivot318.regroup (coefficient R c) 1)
      (Fin.cases (FourRootPivot318.regroup (coefficient R c) 2)
        (Fin.cases (FourRootPivot318.regroup (coefficient R c) 3)
          (fun j => Fin.elim0 j)))) i

@[expose] def localizedSourceEquiv (i : Fin 4) :
    OpenBase R c i ⊗[BranchBase R c i] RegroupedOrder R c i ≃ₐ[OpenBase R c i]
      OpenOrder R c i :=
  IntegralBranchChart318.localizedOrderEquiv _ _ _ _

theorem finite_free_etale (h2 : IsUnit (2 : R)) (i : Fin 4) :
    Module.Finite (OpenBase R c i) (OpenOrder R c i) ∧
    Module.Free (OpenBase R c i) (OpenOrder R c i) ∧
    Algebra.Etale (OpenBase R c i) (OpenOrder R c i) :=
  IntegralBranchChart318.open_finite_free_etale _ _ _ _ h2

/-- An actual integral branch section, requiring unit rather than merely
nonzero contact differences. No square roots of the twists are chosen. -/
@[expose] def branchPoint (i : Fin 4)
    (hi : ∀ j, IsUnit (contacts R i - otherContact R i j)) :
    OpenBase R c i →+* R :=
  IntegralBranchChart318.branchPoint _ _ _ _ hi

end IntegralSourceBranches318
