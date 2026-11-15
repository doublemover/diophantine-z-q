module
public import ActualTwoDescentRankOnePrimaryJointCyclic318
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public section
noncomputable section
namespace ActualTwoDescentJointCyclicPrimaryInvolutions318
set_option maxHeartbeats 16000000
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentFullEllipticHOneKernel318
open groupCohomology
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherKummerHom318
open ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318
open ActualTwoDescentPrimaryGeometricBoundary318 ActualTwoDescentFiniteLevelIntoPrimary318
open ActualTwoDescentPrimaryFullClass318 ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerIntoPrimary318
open ActualTwoDescentPrimarySelmerFiniteLevels318 ActualTwoDescentHigherRationalImage318

open ActualTwoDescentActualPrimaryRationalImage318 ActualTwoDescentRationalPrimaryDivision318
open ActualTwoDescentFullPrimarySelmerTorsion318 ActualTwoDescentPrimaryAllRoots318


open ActualTwoDescentPrimaryAllRoots318 ActualTwoDescentFullPrimarySelmerTorsion318

open ActualTwoDescentRestrictedRationalPrimaryImage318
open ActualTwoDescentRestrictedRationalPrimaryDivision318
open ActualTwoDescentFiniteFactorPrimaryVanishing318
open ActualTwoDescentRankOneRationalCoordinates318
open ActualTwoDescentRankOnePrimaryJointCyclic318

open ActualTwoDescentPrimaryPowerLevels318

lemma actual_joint_cyclic_involution_unique {G : Type} [CommGroup G]
    (hp : IsPGroup 2 G)
    (hc : ∀ x y : G, ∃ g : G, x ∈ Subgroup.zpowers g ∧ y ∈ Subgroup.zpowers g)
    (x y : G) (hx : x^2=1) (hy : y^2=1) (hx0 : x ≠ 1) (hy0 : y ≠ 1) : x=y := by
  classical
  obtain ⟨g,hgx,hgy⟩ := hc x y
  let C := Subgroup.zpowers g
  letI : Finite C := (hp.isOfFinOrder (by decide : 2 ≠ 0) g).finite_zpowers
  letI := Fintype.ofFinite C
  let a : C := ⟨x,hgx⟩
  let b : C := ⟨y,hgy⟩
  have ha : a^2=1 := Subtype.ext hx
  have hb : b^2=1 := Subtype.ext hy
  have ha0 : a ≠ 1 := fun h => hx0 (congrArg Subtype.val h)
  have hb0 : b ≠ 1 := fun h => hy0 (congrArg Subtype.val h)
  by_contra hxy
  have hab : a ≠ b := fun h => hxy (congrArg Subtype.val h)
  have hsub : ({1,a,b} : Finset C) ⊆ Finset.univ.filter (fun z => z^2=1) := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl <;> simp [ha,hb]
  have hcard : ({1,a,b} : Finset C).card=3 := by
    simp [ha0,hb0,hab,Ne.symm ha0,Ne.symm hb0]
  have hle := (Finset.card_le_card hsub).trans (IsCyclic.card_pow_eq_one_le (α:=C) (n:=2) (by decide))
  rw [hcard] at hle
  omega

lemma actual_joint_cyclic_primary_two_bound {G : Type} [CommGroup G]
    (hp : IsPGroup 2 G)
    (hc : ∀ x y : G, ∃ g : G, x ∈ Subgroup.zpowers g ∧ y ∈ Subgroup.zpowers g) :
    Finite (powerLevel G 1) ∧ Nat.card (powerLevel G 1) ≤ 2 := by
  classical
  let f (x : powerLevel G 1) : Bool := decide (x.val=1)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    by_cases hx : x.val=1
    · have hy : y.val=1 := by
        by_contra hy
        simp [f,hx,hy] at h
      exact hx.trans hy.symm
    · have hy : y.val ≠ 1 := by
        intro hy
        simp [f,hx,hy] at h
      exact actual_joint_cyclic_involution_unique hp hc x.val y.val
        (by simpa only [pow_one] using x.property)
        (by simpa only [pow_one] using y.property) hx hy
  haveI : Finite (powerLevel G 1) := Finite.of_injective f hf
  exact ⟨inferInstance,by simpa using Nat.card_le_card_of_injective f hf⟩

end ActualTwoDescentJointCyclicPrimaryInvolutions318
