module
public import FourRootDualityBaseChange318
public import FiniteTraceDualLattice318
public section
noncomputable section
namespace FourRootTraceDualLattice318
open FourRootIntegralDuality318 FourRootTraceCoefficient318 FourRootDualityBaseChange318
open FourRootSignBaseChange318
set_option maxHeartbeats 2200000
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] (a : Fin 4 → R)

/-- The integral trace dual inside the SAME coefficient-changed original
four-root order, using its literal algebra trace over the generic base. -/
@[expose] def lattice : Submodule R (FourRootOrder318.Order (fun i => algebraMap R K (a i))) :=
  FiniteTraceDualLattice318.lattice (coefficientMap a K)

/-- Exact full-order codifferent criterion, before assuming that the
actual different is invertible. This remains valid in every characteristic. -/
theorem mem_iff_different_multiple
    (z : FourRootOrder318.Order (fun i => algebraMap R K (a i))) :
    z∈lattice a ↔∃ x : FourRootOrder318.Order a,
      coefficientMap a K x=
        ((16 : K) • rootProduct (fun i => algebraMap R K (a i)))*z := by
  change z∈FiniteTraceDualLattice318.lattice (coefficientMap a K) ↔ _
  rw [FiniteTraceDualLattice318.mem_iff_euler_multiple (frame a)
    (frame (fun i => algebraMap R K (a i))) (coefficientMap a K)
    (coefficientMap_basis a) (coefficientMap_coefficient a),actual_euler]

/-- Generic separability is required only here. It does not enter the
integral perfect duality or the whole trace-integrality characterization. -/
theorem different_isUnit
    (h2 : IsUnit (2 : K)) (ha : ∀ i,IsUnit (algebraMap R K (a i))) :
    IsUnit ((16 : K) • rootProduct (fun i => algebraMap R K (a i))) := by
  have hg (i : Fin 4) : IsUnit (FourRootOrderSigns318.generator
      (fun j => algebraMap R K (a j)) i) := by
    apply isUnit_of_mul_isUnit_left (y := FourRootOrderSigns318.generator
      (fun j => algebraMap R K (a j)) i)
    rw [←pow_two,FourRootOrderSigns318.generator_square]
    exact (ha i).map (algebraMap K _)
  have h16 : IsUnit (16 : K) := by convert h2.pow 4 using 1 <;> norm_num
  rw [rootProduct_eq,Algebra.smul_def]
  apply (h16.map (algebraMap K _)).mul
  classical
  induction (Finset.univ : Finset (Fin 4)) using Finset.induction_on with
  | empty => simpa using (isUnit_one : IsUnit (1 : FourRootOrder318.Order (fun i => algebraMap R K (a i))))
  | @insert i s hi ih => rw [Finset.prod_insert hi]; exact (hg i).mul ih

/-- The exact fractional trace-dual lattice is the inverse of the actual
16-times-marked-root product times the actual integral order image. -/
theorem mem_iff_inverse_different
    (h2 : IsUnit (2 : K)) (ha : ∀ i,IsUnit (algebraMap R K (a i)))
    (z : FourRootOrder318.Order (fun i => algebraMap R K (a i))) :
    z∈lattice a ↔∃ x : FourRootOrder318.Order a,
      z=↑((different_isUnit a h2 ha).unit⁻¹)*coefficientMap a K x := by
  apply FiniteTraceDualLattice318.mem_iff_inverse_multiple (frame a)
    (frame (fun i => algebraMap R K (a i))) (coefficientMap a K)
    (coefficientMap_basis a) (coefficientMap_coefficient a)
  rw [IsUnit.unit_spec,actual_euler]
end FourRootTraceDualLattice318
