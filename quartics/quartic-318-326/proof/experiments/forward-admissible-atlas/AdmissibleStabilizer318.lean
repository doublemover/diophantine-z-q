module
public import CanonicalXModularity318
public import GammaOneFree318
public section
noncomputable section
open scoped MatrixGroups
namespace AdmissibleStabilizer318
open OpenJComplexEvaluation318
set_option maxHeartbeats 0

/-- Away from j=0,1728, the actual weight-two coordinate scale forces
any integral modular stabilizer denominator to have square one. -/
lemma denominator_square (g : SL(2,ℤ)) (tau : UpperHalfPlane)
    (ht : Admissible tau) (hfix : g•tau=tau) :
    ModularLattice318.d g tau^2=1 := by
  have hs := CanonicalXModularity318.scale_transform
    ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) ⟨g,rfl⟩ tau
  change CanonicalXScale318.scale (g•tau:UpperHalfPlane)=_ at hs
  rw [hfix,←ModularLattice318.d_eq_denom] at hs
  apply mul_right_cancel₀ (CanonicalXScale318.scale_ne_zero 1 tau ht)
  simpa only [one_mul] using hs.symm

lemma lower_left_zero (g : SL(2,ℤ)) (tau : UpperHalfPlane)
    (ht : Admissible tau) (hfix : g•tau=tau) : g 1 0=0 := by
  have hd := denominator_square g tau ht hfix
  rcases sq_eq_one_iff.mp hd with hd|hd
  all_goals
    have hi := congrArg Complex.im hd
    simp only [ModularLattice318.d,Complex.add_im,Complex.mul_im,
      Complex.intCast_re,Complex.intCast_im,zero_mul,add_zero,
      Complex.one_im,Complex.neg_im,neg_zero] at hi
    exact_mod_cast (mul_eq_zero.mp hi).resolve_right tau.im_ne_zero

/-- The actual Gamma1(3) action is free on the admissible locus.
This does not assert freeness at its excluded elliptic j-values. -/
theorem gamma_one_fixed (g : SL(2,ℤ))
    (hg : g∈CongruenceSubgroup.Gamma1 3) (tau : UpperHalfPlane)
    (ht : Admissible tau) (hfix : g•tau=tau) : g=1 := by
  have hc := lower_left_zero g tau ht hfix
  have hreal : GammaOneFree318.realMatrix g•tau=tau := hfix
  obtain ⟨he,hb⟩ := FixedPointTrace318.fixed_equations
    (GammaOneFree318.realMatrix g) (GammaOneFree318.realMatrix_det g) tau hreal
  simp only [GammaOneFree318.realMatrix_entry,hc,Int.cast_zero,
    mul_zero,zero_mul,zero_add] at he hb
  have had : g 0 0=g 1 1 := by
    exact_mod_cast (sub_eq_zero.mp he).symm
  have hdet := g.det_coe
  rw [Matrix.det_fin_two,hc,had,mul_zero,sub_zero,←pow_two] at hdet
  have hd : g 1 1=1 := by
    rcases sq_eq_one_iff.mp hdet with hd|hd
    · exact hd
    · have hz := ((CongruenceSubgroup.Gamma1_mem 3 g).mp hg).2.1
      rw [hd] at hz
      norm_num at hz
  have htrace : GammaOneFree318.realMatrix g 0 0+
      GammaOneFree318.realMatrix g 1 1=2 := by
    simp only [GammaOneFree318.realMatrix_entry,had,hd,Int.cast_one]
    norm_num
  have heq := FixedPointTrace318.eq_one_of_trace_two
    (GammaOneFree318.realMatrix g) (GammaOneFree318.realMatrix_det g) tau hreal htrace
  apply Matrix.SpecialLinearGroup.mapGL_injective (S:=ℝ)
  simpa only [GammaOneFree318.realMatrix,map_one] using heq

end AdmissibleStabilizer318
