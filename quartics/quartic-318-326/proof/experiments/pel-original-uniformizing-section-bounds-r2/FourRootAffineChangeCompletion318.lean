module
public import FourRootAffineChangeCoordinates318
public import FourRootGluedTopology318
public section
noncomputable section
namespace FourRootAffineChangeCompletion318
open FourRootNormalizedPointCharts318 FourRootAffineChangeCoordinates318
variable (b c : Fin 4 → ℂ) (d r : ℂ) (hr : r ≠ 0)
  (h : ∀ i, c i = d + r^2 * b i)
local instance sourceTopology : TopologicalSpace (Completed b) := FourRootGluedTopology318.topology b
local instance targetTopology : TopologicalSpace (Completed c) := FourRootGluedTopology318.topology c

@[expose] def equivalence : Completed b ≃ Completed c :=
  Equiv.sumCongr (finiteEquiv b c d r hr h).toEquiv (Equiv.refl InfinitySigns)
lemma finite_commutes (p : FinitePoints b) :
    equivalence b c d r hr h (finiteChart b p)=
      finiteChart c (finiteForward b c d r h p) := rfl
lemma infinity_commutes (p : InfinityPoints b) :
    equivalence b c d r hr h (infinityChart b p)=
      infinityChart c (infinityForward b c d r hr h p) := by
  by_cases hp : p.val.1=0
  · have hq : (infinityForward b c d r hr h p).val.1=0 := by
      change p.val.1/r=0
      rw [hp,zero_div]
    rw [infinityChart,dif_pos hp,infinityChart,dif_pos hq]
    rfl
  · have hq : (infinityForward b c d r hr h p).val.1≠0 := div_ne_zero hp hr
    rw [infinityChart_nonzero b p hp,infinityChart_nonzero c _ hq,finite_commutes]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · change d+r^2*(b 0+(p.val.1^2)⁻¹)=c 0+((p.val.1/r)^2)⁻¹
      rw [h 0]
      field_simp [hp,hr]
      <;> ring
    · funext i
      change r*(p.val.2 i/p.val.1)=p.val.2 i/(p.val.1/r)
      field_simp [hp,hr]
      <;> ring

lemma inverse_finite_commutes (q : FinitePoints c) :
    (equivalence b c d r hr h).symm (finiteChart c q)=
      finiteChart b (finiteBackward b c d r hr h q) := rfl
lemma inverse_infinity_commutes (q : InfinityPoints c) :
    (equivalence b c d r hr h).symm (infinityChart c q)=
      infinityChart b (infinityBackward b c d r h q) := by
  apply (equivalence b c d r hr h).injective
  rw [Equiv.apply_symm_apply,infinity_commutes,infinity_right]

/-- Genuine homeomorphism for the independently glued topologies. Both
whole affine charts commute, so this is stronger than a point bijection. -/
@[expose] def homeomorph : Completed b ≃ₜ Completed c where
  toEquiv := equivalence b c d r hr h
  continuous_toFun := by
    apply (FourRootGluedTopology318.continuous_iff b _).mpr
    constructor
    · simpa only [Function.comp_def,finite_commutes] using
        (FourRootGluedTopology318.finiteChart_continuous c).comp
          (finiteEquiv b c d r hr h).continuous
    · simpa only [Function.comp_def,infinity_commutes] using
        (FourRootGluedTopology318.infinityChart_continuous c).comp
          (infinityEquiv b c d r hr h).continuous
  continuous_invFun := by
    apply (FourRootGluedTopology318.continuous_iff c _).mpr
    constructor
    · simpa only [Function.comp_def,inverse_finite_commutes] using
        (FourRootGluedTopology318.finiteChart_continuous b).comp
          (finiteEquiv b c d r hr h).symm.continuous
    · simpa only [Function.comp_def,inverse_infinity_commutes] using
        (FourRootGluedTopology318.infinityChart_continuous b).comp
          (infinityEquiv b c d r hr h).symm.continuous

lemma preserves_infinity (s : InfinitySigns) : homeomorph b c d r hr h (.inr s)=.inr s := rfl
lemma finite_base (p : FinitePoints b) :
    (finiteForward b c d r h p).val.1=d+r^2*p.val.1 := rfl
lemma finite_root (p : FinitePoints b) (i : Fin 4) :
    (finiteForward b c d r h p).val.2 i=r*p.val.2 i := rfl
end FourRootAffineChangeCompletion318
