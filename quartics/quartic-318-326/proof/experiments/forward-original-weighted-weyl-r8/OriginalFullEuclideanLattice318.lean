module
public import OriginalEuclideanDualCount318
public import Mathlib.Algebra.Module.ZLattice.Basic
public section
noncomputable section
namespace OriginalFullEuclideanLattice318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalDualDenominator318
set_option maxHeartbeats 2500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual original Euclidean subgroup, bundled as a Z-submodule. -/
@[expose] def realModule (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) : Submodule ℤ E where
  carrier := realLattice p κ t
  zero_mem' := (realLattice p κ t).zero_mem
  add_mem' := (realLattice p κ t).add_mem
  smul_mem' n w hw := (realLattice p κ t).zsmul_mem hw n

/-- An actual embedded integer vector inside the open Euclidean unit ball
is zero. Coordinate bounds use the standard Euclidean norm. -/
lemma embed_zero_of_norm_lt_one (v : Vector ℤ) (hv : ‖embed v‖<1) : v=0 := by
  have h (i : Fin 3) : |embed v i|<1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (embed v) i).trans_lt hv
  have hx : |v.1|<(1:ℤ) := by exact_mod_cast (show |(v.1:ℝ)|<1 from h 0)
  have hz : |v.2.1|<(1:ℤ) := by exact_mod_cast (show |(v.2.1:ℝ)|<1 from h 1)
  have hw : |v.2.2|<(1:ℤ) := by exact_mod_cast (show |(v.2.2:ℝ)|<1 from h 2)
  exact Prod.ext (Int.abs_lt_one_iff.mp hx) (Prod.ext (Int.abs_lt_one_iff.mp hz) (Int.abs_lt_one_iff.mp hw))

/-- Discreteness of the ORIGINAL embedded subgroup, from a genuine open
unit ball. No chosen abstract lattice basis changes the topology. -/
instance realModule_discrete (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    DiscreteTopology (realModule p κ t) := by
  refine discreteTopology_iff_isOpen_singleton_zero.mpr ⟨Metric.ball 0 1,Metric.isOpen_ball,?_⟩
  ext x
  rw [Set.mem_preimage,mem_ball_zero_iff,Set.mem_singleton_iff]
  constructor
  · intro hx
    obtain ⟨v,hv,he⟩ := x.2
    have hz : v=0 := embed_zero_of_norm_lt_one v (by rwa [he])
    apply Subtype.ext
    change (x:E)=0
    rw [←he,hz,embed_zero]
  · intro hx
    subst x
    simp

lemma embedded_mem_real_span (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (v : Vector ℤ) :
    embed v∈Submodule.span ℝ (realModule p κ t : Set E) := by
  let M := FixedSquarefreeCRT318.modulus p
  have hm : (M:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (FixedSquarefreeCRT318.modulus_positive p hp))
  have hx := modulus_multiple_mem p κ t v
  have hcast : embed ((M:ℤ)*v.1,(M:ℤ)*v.2.1,(M:ℤ)*v.2.2)=(M:ℝ) • embed v := by
    ext i
    fin_cases i <;> simp [embed]
  have hmem : (M:ℝ) • embed v∈realModule p κ t := by
    exact ⟨_,hx,hcast⟩
  have hh := (Submodule.span ℝ (realModule p κ t : Set E)).smul_mem (M:ℝ)⁻¹
    (Submodule.subset_span hmem)
  simpa only [smul_smul,inv_mul_cancel₀ hm,one_smul] using hh

/-- Every real vector is the literal linear combination of the three
original coordinate axes; this fixes the ambient metric and coordinates. -/
lemma coordinate_expansion (w : E) :
    w=w 0 • embed (1,0,0)+w 1 • embed (0,1,0)+w 2 • embed (0,0,1) := by
  ext i
  fin_cases i <;> simp [embed]

/-- Full REAL span is constructed from the actual modulus axes. -/
theorem actual_real_span (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    Submodule.span ℝ (realModule p κ t : Set E)=⊤ := by
  apply top_unique
  intro w hw
  rw [coordinate_expansion w]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (embedded_mem_real_span p hp κ t (1,0,0))
    · exact Submodule.smul_mem _ _ (embedded_mem_real_span p hp κ t (0,1,0))
  · exact Submodule.smul_mem _ _ (embedded_mem_real_span p hp κ t (0,0,1))

/-- Genuine Mathlib Z-lattice instance for the original subgroup. -/
theorem actual_isZLattice (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) : IsZLattice ℝ (realModule p κ t) :=
  ⟨actual_real_span p hp κ t⟩

theorem actual_rank (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) : Module.finrank ℤ (realModule p κ t)=3 := by
  letI := actual_isZLattice p hp κ t
  rw [ZLattice.rank ℝ (realModule p κ t)]
  exact finrank_euclideanSpace_fin

end OriginalFullEuclideanLattice318
