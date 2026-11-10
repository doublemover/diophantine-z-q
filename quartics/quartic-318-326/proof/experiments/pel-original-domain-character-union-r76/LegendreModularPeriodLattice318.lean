module
public import OriginalPeriodIndependentBiholomorph318
public import LatticeInvariants318
public import ActualJSurjective318
public section
noncomputable section
namespace LegendreModularPeriodLattice318
open ComplexAffineFreeTranslation318 OriginalComplexPeriodPair318
open scoped Topology

/-- The WHOLE actual lattice Z*tau+Z, not a finite-index period sublattice. -/
@[expose] def lattice (tau:UpperHalfPlane) : AddSubgroup ℂ:=
  (PeriodEisenstein318.periods tau).lattice.toAddSubgroup
instance lattice_discrete (tau:UpperHalfPlane) : DiscreteTopology (lattice tau) :=
  inferInstanceAs (DiscreteTopology (PeriodEisenstein318.periods tau).lattice)

/-- Compactness is derived from the actual full Z-lattice fundamental
parallelogram, not supplied as a uniformization hypothesis. -/
instance torus_compact (tau:UpperHalfPlane) : CompactSpace (Torus (lattice tau)) := by
  apply isCompact_univ_iff.mp
  have hc:=IsZLattice.isCompact_range_of_periodic (PeriodEisenstein318.periods tau).lattice
    (projection (lattice tau)) continuous_quotient_mk' (fun z w hw=>by
      rw [map_add,(show projection (lattice tau) w=0 from
        (QuotientAddGroup.eq_zero_iff).mpr hw),add_zero])
  rwa [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective (lattice tau))] at hc

/-- The basis selected by the original period-cubic producer spans
EXACTLY the original modular lattice. There is no basis or index change
in any infinite sum below. -/
lemma whole_lattice (tau:UpperHalfPlane) :
    (pair (lattice tau)).lattice=(PeriodEisenstein318.periods tau).lattice := by
  rw [pair_lattice]
  ext z
  rfl
lemma whole_sum (tau:UpperHalfPlane) (n:ℕ) :
    (pair (lattice tau)).G n=(PeriodEisenstein318.periods tau).G n := by
  unfold PeriodPair.G
  rw [whole_lattice]
lemma whole_g2 (tau:UpperHalfPlane) :
    (pair (lattice tau)).g₂=(PeriodEisenstein318.periods tau).g₂ := by
  rw [PeriodPair.g₂,PeriodPair.g₂,whole_sum]
lemma whole_g3 (tau:UpperHalfPlane) :
    (pair (lattice tau)).g₃=(PeriodEisenstein318.periods tau).g₃ := by
  rw [PeriodPair.g₃,PeriodPair.g₃,whole_sum]

/-- Original Pprime/2 native coefficients differ from the normalized
modular model by the ACTUAL 2*pi powers, including their signs. -/
lemma native_a4 (tau:UpperHalfPlane) :
    OriginalPeriodProjectiveModel318.A (lattice tau)=
      (2*(Real.pi:ℂ))^4*(ModularWeierstrass318.curve tau).a₄ := by
  rw [OriginalPeriodProjectiveModel318.A,whole_g2,LatticeInvariants318.g2_normalization]
  dsimp [ModularWeierstrass318.curve,NormalizedWeierstrass318.model]
  ring
lemma native_a6 (tau:UpperHalfPlane) :
    OriginalPeriodProjectiveModel318.B (lattice tau)=
      (2*(Real.pi:ℂ))^6*(ModularWeierstrass318.curve tau).a₆ := by
  rw [OriginalPeriodProjectiveModel318.B,whole_g3,LatticeInvariants318.g3_normalization]
  dsimp [ModularWeierstrass318.curve,NormalizedWeierstrass318.model]
  ring
end LegendreModularPeriodLattice318
