module
public import OriginalFullEuclideanLattice318
public section
noncomputable section
namespace OriginalFullDualLattice318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalDualDenominator318 OriginalFullEuclideanLattice318
set_option maxHeartbeats 2500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integral dual constructed on the actual standard Euclidean
lattice, now bundled for the genuine geometry-of-numbers API. -/
@[expose] def dualModule (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) : Submodule ℤ E where
  carrier := Dual p κ t
  zero_mem' := (Dual p κ t).zero_mem
  add_mem' := (Dual p κ t).add_mem
  smul_mem' n w hw := (Dual p κ t).zsmul_mem hw n

lemma dual_zero_of_small_norm (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (w : E) (hw : w∈dualModule p κ t)
    (hwn : ‖w‖<1/(FixedSquarefreeCRT318.modulus p:ℝ)) : w=0 := by
  let M := FixedSquarefreeCRT318.modulus p
  have hm : (0:ℝ)<M := by exact_mod_cast (FixedSquarefreeCRT318.modulus_positive p hp)
  obtain ⟨v,he⟩ := actual_dual_numerator p hp κ t w hw
  have hscale : (M:ℝ) • w=embed v := by
    rw [←he]
    simp only [normalized,smul_smul,mul_inv_cancel₀ hm.ne',one_smul]
  have hvn : ‖embed v‖<1 := by
    rw [←hscale,norm_smul,Real.norm_of_nonneg hm.le]
    calc
      (M:ℝ)*‖w‖<(M:ℝ)*(1/(M:ℝ)) := mul_lt_mul_of_pos_left hwn hm
      _ = 1 := by field_simp
  have hv := embed_zero_of_norm_lt_one v hvn
  rw [←he,hv,normalized_zero]

/-- Discreteness of the ACTUAL Euclidean dual at the proved radius1/M.
Only the original prime facts are used to produce M>0. -/
instance dualModule_discrete (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) : DiscreteTopology (dualModule p κ t) := by
  have hp (i : ι) : (p i).Prime := Fact.out
  have hm : (0:ℝ)<FixedSquarefreeCRT318.modulus p := by
    exact_mod_cast (FixedSquarefreeCRT318.modulus_positive p hp)
  refine discreteTopology_iff_isOpen_singleton_zero.mpr
    ⟨Metric.ball 0 (1/(FixedSquarefreeCRT318.modulus p:ℝ)),Metric.isOpen_ball,?_⟩
  ext x
  rw [Set.mem_preimage,mem_ball_zero_iff,Set.mem_singleton_iff]
  constructor
  · intro hx
    apply Subtype.ext
    exact dual_zero_of_small_norm p hp κ t x x.2 hx
  · intro hx
    subst x
    simpa only [norm_zero] using one_div_pos.mpr hm

/-- Every original integer vector belongs to the integral dual because
its inner products with original integer lattice points are integers. -/
lemma embed_mem_dualModule (p : ι → ℕ) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) (v : Vector ℤ) : embed v∈dualModule p κ t := by
  apply (dual_iff p κ t (embed v)).mpr
  intro u hu
  exact ⟨dot v u,inner_embed v u⟩

theorem actual_dual_real_span (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    Submodule.span ℝ (dualModule p κ t : Set E)=⊤ := by
  apply top_unique
  intro w hw
  rw [coordinate_expansion w]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (embed_mem_dualModule p κ t (1,0,0)))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (embed_mem_dualModule p κ t (0,1,0)))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (embed_mem_dualModule p κ t (0,0,1)))

/-- The actual whole dual is a full discrete real Z-lattice, with its
original inner product and denominator, not a hypothetical dual object. -/
instance actual_dual_isZLattice (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) : IsZLattice ℝ (dualModule p κ t) :=
  ⟨actual_dual_real_span p κ t⟩

theorem actual_dual_rank (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) : Module.finrank ℤ (dualModule p κ t)=3 := by
  rw [ZLattice.rank ℝ (dualModule p κ t)]
  exact finrank_euclideanSpace_fin

end OriginalFullDualLattice318
