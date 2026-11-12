module
public import CoefficientPairingTrace318
public section
noncomputable section
namespace FiniteTraceDualLattice318
open Module TensorCoefficientDuality318 CoefficientPairingTrace318
set_option maxHeartbeats 2200000
variable {R K A B ι : Type*} [CommRing R] [CommRing K] [CommRing A] [CommRing B]
  [Algebra R K] [Algebra R A] [Algebra K B] [Algebra R B] [IsScalarTower R K B]
  [Fintype ι] [DecidableEq ι]
  (F : Frame R A ι) (G : Frame K B ι) (e : A →ₐ[R] B)
  (hb : ∀ i,e (F.basis i)=G.basis i)
  (hcoeff : ∀ a,G.coefficient (e a)=algebraMap R K (F.coefficient a))

@[expose] def traceTest (a : A) : B →ₗ[R] K where
  toFun z := ((Algebra.trace K B).restrictScalars R) (z*e a)
  map_add' z z' := by rw [add_mul,map_add]
  map_smul' r z := by rw [Algebra.smul_mul_assoc,map_smul]

/-- The actual trace-integral dual of the integral order inside the
specified generic algebra, with the true algebra trace and base map. -/
@[expose] def lattice : Submodule R B :=
  ⨅ a : A,(LinearMap.range (Algebra.linearMap R K)).comap (traceTest e a)

theorem mem_iff (z : B) : z∈lattice e ↔
    ∀ a : A,∃ r : R,algebraMap R K r=Algebra.trace K B (z*e a) := by
  simp only [lattice,Submodule.mem_iInf,Submodule.mem_comap,LinearMap.mem_range] <;> rfl

include hb in
 theorem coordinate_trace (z : B) (i : ι) :
    G.basis.repr (euler G*z) i=Algebra.trace K B (z*e (F.basis (G.switch i))) := by
  rw [←PerfectCoefficientPairing318.pairing_coordinate G.basis G.switch G.involutive G.coefficient G.pairing,
    trace_eq G,hb]
  congr 1
  ring

include hb hcoeff in
/-- Exact coefficientwise characterization of the WHOLE trace-dual
lattice. No pointwise surrogate, field dimension or abstract dual chosen. -/
theorem mem_iff_euler_multiple (z : B) : z∈lattice e ↔∃ a : A,e a=euler G*z := by
  constructor
  · intro hz
    rw [mem_iff] at hz
    have hc (i : ι) : ∃ r : R,algebraMap R K r=G.basis.repr (euler G*z) i := by
      rw [coordinate_trace F G e hb]
      exact hz (F.basis (G.switch i))
    choose r hr using hc
    refine ⟨∑ i,r i • F.basis i,?_⟩
    simp only [map_sum,map_smul,hb]
    simp_rw [←IsScalarTower.algebraMap_smul R K B,hr]
    exact G.basis.sum_repr (euler G*z)
  · rintro ⟨a,ha⟩
    rw [mem_iff]
    intro a'
    refine ⟨F.coefficient (a*a'),?_⟩
    rw [trace_eq G]
    calc
      _ = G.coefficient (e (a*a')) := (hcoeff (a*a')).symm
      _ = G.coefficient ((euler G*z)*e a') := by rw [map_mul,ha]
      _ = _ := by congr 1; ring

include hb hcoeff in
/-- When the actual generic Euler/different element is a unit, the full
trace dual is EXACTLY its inverse times the actual integral order image. -/
theorem mem_iff_inverse_multiple (δ : Bˣ) (hδ : (δ : B)=euler G) (z : B) :
    z∈lattice e ↔∃ a : A,z=(↑δ⁻¹ : B)*e a := by
  rw [mem_iff_euler_multiple F G e hb hcoeff]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    rw [ha,←hδ,←mul_assoc,Units.inv_mul,one_mul]
  · rintro ⟨a,rfl⟩
    refine ⟨a,?_⟩
    rw [←hδ,←mul_assoc,Units.mul_inv,one_mul]
end FiniteTraceDualLattice318
