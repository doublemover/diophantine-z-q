module
public import FiniteOrderConductorTraceDual318
public section
noncomputable section
namespace NormalTraceDualModule318
variable {P F B : Type*} [CommRing P] [CommRing F] [CommRing B]
  [Algebra P F] [Algebra F B] [Algebra P B] [IsScalarTower P F B]
  (N : Subalgebra P B)

/-- The trace-integral coefficients carry multiplication by the ACTUAL
normal order, not only by its polynomial base. -/
@[expose] def lattice : Submodule N B where
  carrier := FiniteOrderConductorTraceDual318.traceDual (K:=F) N
  zero_mem' := (FiniteOrderConductorTraceDual318.traceDual (K:=F) N).zero_mem
  add_mem' := (FiniteOrderConductorTraceDual318.traceDual (K:=F) N).add_mem
  smul_mem' n z hz := by
    rw [FiniteOrderConductorTraceDual318.mem_traceDual] at hz ⊢
    intro m
    obtain ⟨r,hr⟩ := hz (n*m)
    refine ⟨r,hr.trans ?_⟩
    congr 1
    change z*(n.val*m.val)=(n.val*z)*m.val
    ring

lemma mem_iff (z : B) : z ∈ lattice (F:=F) N ↔
    z ∈ FiniteOrderConductorTraceDual318.traceDual (K:=F) N := Iff.rfl

/-- The underlying polynomial-base lattice is EXACTLY the previous
trace codifferent, with no saturation or replacement of its carrier. -/
lemma restrict_scalars : (lattice (F:=F) N).restrictScalars P =
    FiniteOrderConductorTraceDual318.traceDual (K:=F) N := by
  ext z
  rfl
end NormalTraceDualModule318
