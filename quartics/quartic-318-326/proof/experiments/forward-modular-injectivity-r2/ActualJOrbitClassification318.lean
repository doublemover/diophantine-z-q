module
public import IntegralPeriodBasis318
public import OpenJAnalyticPoints318
public section
noncomputable section
open scoped MatrixGroups
namespace ActualJOrbitClassification318
set_option maxHeartbeats 0

/-- Equality of genuine j produces an actual integral modular change of period.
The analytic classification step is supplied by genuine wp scaling and pole lattices. -/
theorem exists_modular_of_j_eq (tau sigma : UpperHalfPlane)
    (hj : ActualQJ318.jInvariant tau=ActualQJ318.jInvariant sigma) :
    ∃ g : SL(2,ℤ), g•tau=sigma := by
  have hJ : (ModularWeierstrass318.curve tau).j=(ModularWeierstrass318.curve sigma).j := by
    simpa only [ModularWeierstrass318.curve_j] using hj
  obtain ⟨u,h4,h6⟩ := ShortScaling318.exists_scaling_of_j_eq
    (ModularWeierstrass318.curve tau) (ModularWeierstrass318.curve sigma) hJ
  obtain ⟨g,hg,_⟩ := IntegralPeriodBasis318.exists_modular_matrix tau sigma u
    (ScaledPeriodLattice318.lattice_homothety tau sigma u h4 h6)
  exact ⟨g,hg⟩

end ActualJOrbitClassification318
