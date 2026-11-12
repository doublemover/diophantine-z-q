module
public import ActualTwoDescentOriginalRootMaximalIdeal318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootLocalParameter318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentRootCofactorData318 ActualTwoDescentOriginalRootEvaluation318
open ActualTwoDescentOriginalRootMaximalIdeal318
variable {K : Type*} [Field K] [CharZero K]

abbrev RootLocalRing (n : K) (i : Fin 3) := Localization.AtPrime (rootIdeal n i)
def rootLocalMap (n : K) (i : Fin 3) : AffineChart n →+* RootLocalRing n i := algebraMap _ _
def rootLocalY (n : K) (i : Fin 3) := rootLocalMap n i (affineY n)
def rootLocalF (n : K) (i : Fin 3) := rootLocalMap n i (rootNumerator n i)
def rootLocalQ (n : K) (i : Fin 3) := rootLocalMap n i (rootCofactor n i)
lemma actual_root_local_cofactor_unit (n : K) (hn : n≠0) (i : Fin 3) :
    IsUnit (rootLocalQ n i) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (RootLocalRing n i) (rootIdeal n i) _).mpr
  rw [actual_root_ideal_kernel]
  change rootEvaluation n i (rootCofactor n i)≠0
  rw [actual_evaluation_cofactor]
  exact actual_root_derivative_nonzero n hn i
lemma actual_root_local_relation (n : K) (i : Fin 3) :
    rootLocalY n i^2=rootLocalF n i*rootLocalQ n i := by
  simpa only [map_pow,map_mul,rootLocalY,rootLocalF,rootLocalQ] using
    congrArg (rootLocalMap n i) (actual_root_factorization n i)
/-- The original root function is a unit times y squared in its ACTUAL local ring. -/
theorem actual_root_local_unit_square (n : K) (hn : n≠0) (i : Fin 3) :
    ∃ e : (RootLocalRing n i)ˣ, rootLocalF n i=(e : RootLocalRing n i)*rootLocalY n i^2 := by
  obtain ⟨q,hq⟩ := actual_root_local_cofactor_unit n hn i
  refine ⟨q⁻¹,?_⟩
  rw [actual_root_local_relation,←hq]
  simp [mul_left_comm,mul_comm,mul_assoc]
lemma actual_root_local_y_mem (n : K) (i : Fin 3) :
    rootLocalY n i∈IsLocalRing.maximalIdeal (RootLocalRing n i) := by
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff (RootLocalRing n i) (rootIdeal n i) _).mpr
  rw [actual_root_ideal_kernel]
  exact actual_evaluation_y n i
lemma actual_root_local_map_injective (n : K) (i : Fin 3) :
    Function.Injective (rootLocalMap n i) :=
  IsLocalization.injective (RootLocalRing n i) (rootIdeal n i).primeCompl_le_nonZeroDivisors
lemma actual_root_local_y_nonzero (n : K) (i : Fin 3) : rootLocalY n i≠0 := by
  intro h
  apply actual_affine_y_nonzero n
  apply actual_root_local_map_injective n i
  simpa only [map_zero] using h
end ActualTwoDescentOriginalRootLocalParameter318
