module
public import SelectedGenuinePeriodMark318
public import Mathlib.Topology.Algebra.Group.Quotient
public section
noncomputable section

namespace SelectedGenuinePeriodLattice318

open SelectedGenuinePeriodMark318

/-- The literal family quotient has all of the original lattice and
is compact, by its actual periodic projection, with no auxiliary
finite index periods. -/
theorem compact_torus (τ : UpperHalfPlane) : CompactSpace (Torus τ) := by
  let L := (period τ).lattice
  let q : ℂ →+ Torus τ := QuotientAddGroup.mk' L.toAddSubgroup
  have hq : Continuous q := QuotientAddGroup.continuous_mk
  have ht : ∀ z w : ℂ, w ∈ L → q (z+w) = q z := by
    intro z w hw
    have hw' : q w = 0 := (QuotientAddGroup.eq_zero_iff w).mpr hw
    rw [map_add,hw',add_zero]
  have hc := IsZLattice.isCompact_range_of_periodic L (q : ℂ → Torus τ) hq ht
  have hu : Set.range q = Set.univ := Set.range_eq_univ.mpr
    (QuotientAddGroup.mk'_surjective L.toAddSubgroup)
  rw [hu] at hc
  exact ⟨hc⟩

/-- The library function is literally a sum over ALL periods. A
new basis for the same submodule cannot change any affine x. -/
theorem weierstrassP_eq {P Q : PeriodPair} (h : P.lattice = Q.lattice) (z : ℂ) :
    P.weierstrassP z = Q.weierstrassP z :=
  congrArg (fun L : Submodule ℤ ℂ =>
    ∑' l : L, (1/(z-(l : ℂ))^2 - 1/(l : ℂ)^2)) h

theorem derivWeierstrassP_eq {P Q : PeriodPair} (h : P.lattice = Q.lattice) (z : ℂ) :
    P.derivWeierstrassP z = Q.derivWeierstrassP z :=
  congrArg (fun L : Submodule ℤ ℂ =>
    -(∑' l : L, 2/(z-(l : ℂ))^3)) h

theorem eisenstein_eq {P Q : PeriodPair} (h : P.lattice = Q.lattice) (n : ℕ) :
    P.G n = Q.G n :=
  congrArg (fun L : Submodule ℤ ℂ => ∑' l : L, ((l : ℂ)^n)⁻¹) h

theorem g₂_eq {P Q : PeriodPair} (h : P.lattice = Q.lattice) : P.g₂ = Q.g₂ := by
  rw [PeriodPair.g₂,PeriodPair.g₂,eisenstein_eq h]

theorem g₃_eq {P Q : PeriodPair} (h : P.lattice = Q.lattice) : P.g₃ = Q.g₃ := by
  rw [PeriodPair.g₃,PeriodPair.g₃,eisenstein_eq h]

end SelectedGenuinePeriodLattice318

#print axioms SelectedGenuinePeriodLattice318.compact_torus
#print axioms SelectedGenuinePeriodLattice318.weierstrassP_eq
#print axioms SelectedGenuinePeriodLattice318.derivWeierstrassP_eq
#print axioms SelectedGenuinePeriodLattice318.g₂_eq
#print axioms SelectedGenuinePeriodLattice318.g₃_eq
