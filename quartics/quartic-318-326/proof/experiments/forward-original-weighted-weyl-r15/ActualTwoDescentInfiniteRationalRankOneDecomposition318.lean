module
public import ActualTwoDescentRankOneRationalPruefer318
public section
noncomputable section
namespace ActualTwoDescentInfiniteRationalRankOneDecomposition318
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
open ActualTwoDescentJointCyclicPrimaryInvolutions318
open ActualTwoDescentRationalPrimaryTwoBound318
open ActualTwoDescentRankOnePrimaryNonzero318
open ActualTwoDescentRankOnePrimaryInfinite318
open ActualTwoDescentRankOneRationalPruefer318

open ActualTwoDescentActualMordellWeilStructure318 ActualTwoDescentEllipticDoubleQuotient318

def freeOneIntegerEquiv : (Fin 1 →₀ ℤ) ≃+ ℤ where
  toFun f := f 0
  invFun z := Finsupp.single 0 z
  left_inv f := by
    ext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    simp
  right_inv z := by simp
  map_add' f g := rfl

lemma actual_infinite_rank_one_decomposition (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8) [Infinite (Point n)] :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Finite T), Nonempty (Point n ≃+ ℤ × T) := by
  obtain ⟨r,hr,T,hT,hfin,⟨e⟩,_⟩ := actual_free_rank_at_most_one n hn hf hb
  letI := hT
  letI := hfin
  have hr1 : r=1 := by
    by_contra h
    have hr0 : r=0 := by omega
    subst r
    haveI : Finite (Point n) := Finite.of_equiv ((Fin 0 →₀ ℤ) × T) e.symm.toEquiv
    exact not_finite (Point n)
  subst r
  exact ⟨T,inferInstance,inferInstance,⟨e.trans (AddEquiv.prodCongr freeOneIntegerEquiv (AddEquiv.refl T))⟩⟩

end ActualTwoDescentInfiniteRationalRankOneDecomposition318
