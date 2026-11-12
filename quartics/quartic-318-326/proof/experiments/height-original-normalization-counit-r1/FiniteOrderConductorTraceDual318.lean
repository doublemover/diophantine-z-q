module
public import FiniteTraceDualLattice318
public section
noncomputable section
namespace FiniteOrderConductorTraceDual318
variable {R K A B : Type*} [CommRing R] [CommRing K] [CommRing A] [CommRing B]
  [Algebra R K] [Algebra R A] [Algebra K B] [Algebra R B] [IsScalarTower R K B]
  (e : A →ₐ[R] B) (N : Subalgebra R B)

@[expose] def multiply (a : B) : B →ₗ[R] B where
  toFun z := z*a
  map_add' z z' := add_mul z z' a
  map_smul' r z := Algebra.smul_mul_assoc r z a
@[expose] def orderImage : Submodule R B := e.toLinearMap.range
/-- Actual conductor in the common ambient algebra, testing every
normal-order element against the literal original order image. -/
@[expose] def conductor : Submodule R B :=
  ⨅ n : N,(orderImage e).comap (multiply n.val)
lemma mem_conductor (z : B) : z ∈ conductor e N ↔
    ∀ n : N,∃ a : A,e a=z*n.val := by
  simp only [conductor,Submodule.mem_iInf,Submodule.mem_comap,orderImage,
    LinearMap.mem_range] <;> rfl

/-- Trace integrality on the actual larger order; the trace remains
that of the SAME ambient algebra over the SAME generic base. -/
@[expose] def traceDual : Submodule R B :=
  ⨅ n : N,(LinearMap.range (Algebra.linearMap R K)).comap
    (((Algebra.trace K B).restrictScalars R).comp (multiply n.val))
lemma mem_traceDual (z : B) : z ∈ traceDual (K:=K) N ↔
    ∀ n : N,∃ r : R,algebraMap R K r=Algebra.trace K B (z*n.val) := by
  simp only [traceDual,Submodule.mem_iInf,Submodule.mem_comap,LinearMap.mem_range] <;> rfl

variable (hN : ∀ a : A,e a ∈ N)
include hN in
/-- Normal-order trace tests are equivalent to requiring ALL its
multiples to lie in the original codifferent. Both directions use
actual multiplication, not rank comparison or abstract duality. -/
theorem traceDual_iff_multiples (z : B) : z ∈ traceDual (K:=K) N ↔
    ∀ n : N,z*n.val ∈ FiniteTraceDualLattice318.lattice (K:=K) e := by
  rw [mem_traceDual]
  constructor
  · intro hz n
    rw [FiniteTraceDualLattice318.mem_iff]
    intro a
    have h := hz ⟨n.val*e a,N.mul_mem n.property (hN a)⟩
    simpa only [mul_assoc] using h
  · intro hz n
    obtain ⟨r,hr⟩ := (FiniteTraceDualLattice318.mem_iff e (z*n.val)).mp (hz n) 1
    exact ⟨r,by simpa only [map_one,mul_one] using hr⟩

variable (δ : B)
  (hraw : ∀ z : B,z ∈ FiniteTraceDualLattice318.lattice (K:=K) e ↔
    δ*z ∈ orderImage e)
include hN hraw in
/-- The normalization correction is the ACTUAL conductor: multiply
its trace codifferent by the raw order's different. The hypothesis is
an explicit raw codifferent theorem, discharged by the four-root frame. -/
theorem traceDual_iff_conductor (z : B) :
    z ∈ traceDual (K:=K) N ↔ δ*z ∈ conductor e N := by
  rw [traceDual_iff_multiples e N hN,mem_conductor]
  constructor
  · intro hz n
    have h := (hraw (z*n.val)).mp (hz n)
    obtain ⟨a,ha⟩ := h
    exact ⟨a,by simpa only [mul_assoc] using ha⟩
  · intro hz n
    apply (hraw (z*n.val)).mpr
    obtain ⟨a,ha⟩ := hz n
    exact ⟨a,by simpa only [mul_assoc] using ha⟩

include hN in
lemma conductor_le_normal : conductor e N ≤ N.toSubmodule := by
  intro z hz
  obtain ⟨a,ha⟩ := (mem_conductor e N z).mp hz 1
  have he : e a=z := by
    change e a=z*1 at ha
    simpa only [mul_one] using ha
  rw [←he]
  exact hN a

lemma conductor_stable (n : N) (z : B) (hz : z ∈ conductor e N) :
    z*n.val ∈ conductor e N := by
  rw [mem_conductor] at hz ⊢
  intro m
  obtain ⟨a,ha⟩ := hz (n*m)
  change e a=z*(n.val*m.val) at ha
  exact ⟨a,by simpa only [mul_assoc] using ha⟩
end FiniteOrderConductorTraceDual318
