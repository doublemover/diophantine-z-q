module
public import PreparedTwistSource318
public import GeneratorMultiplesTwo318
public import GeneratorMultiplesThree318
public section
noncomputable section
namespace ScalarTranslatedIndex318
open ConcreteG8Domain (K pair)
open CoherentMultipleCharts318 CompressedOrientation318
open CompressedAnchorWitness318 (shiftWitness)
open GeneratorScalarProgression318 (normCoefficient)
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

lemma chartU_one_inverse : chartU 1=1/k := by
  rw [GeneratorScalarProgression318.chartU_one]
  apply (eq_div_iff CompressedPoint318.k_ne).mpr
  ext <;> norm_num [k,pair]

lemma chartV_one : chartV 1=m/k^2 := by
  simp only [chartV,one_zsmul]
  change (GlobalGeneratorPoints318.xR^4-6*ConcreteG8Domain.D*GlobalGeneratorPoints318.xR^2+
    ConcreteG8Domain.D^2)/(GlobalGeneratorPoints318.xR^2+ConcreteG8Domain.D)^2=m/k^2
  field_simp [CoherentMultipleCharts318.denominator_ne,CompressedPoint318.k_ne]
  ext <;> norm_num [GlobalGeneratorPoints318.xR,ConcreteG8Domain.D,
    ConcreteG8Domain.i,pair,k,m,pow_succ]

/-- The original compression shift is the actual n−1 chart with its exact
orientation. This is a group-law identity, not a choice among Kummer roots. -/
lemma shifted_chart (n : ℤ) (hn : n≠0) :
    chartU (n-1)= -(chartU n*shiftWitness (chartU n) (chartV n)) := by
  have hgroup : (n-1) • GlobalGeneratorPoints318.R=
      n • GlobalGeneratorPoints318.R+ -GlobalGeneratorPoints318.R := by
    rw [sub_zsmul,one_zsmul,sub_eq_add_neg]
  have he := CoherentAdditionU318.u_add (n • GlobalGeneratorPoints318.R)
    (-GlobalGeneratorPoints318.R)
  have hadd : chartU (n-1)=ReciprocalGroup318.sumU ConcreteG8Domain.D
      (chartU n) (chartV n) (-chartU 1) (chartV 1) := by
    simpa only [chartU,chartV,hgroup,one_zsmul,u_negative,v_negative] using he
  rw [hadd,chartU_one_inverse,chartV_one]
  have hu : chartU n≠0 := fun hz => hn ((chartU_zero_iff n).mp hz)
  have hd : ConcreteG8Domain.D=D := CoherentMultipleCharts318.D_eq.symm
  rw [hd]
  unfold ReciprocalGroup318.sumU shiftWitness
  field_simp [hu,CompressedPoint318.k_ne,CompressedAnchorWitness318.denominator_nonzero,
    CoherentRootSign318.addition_denominator_ne]
  ring

/-- The scalar root is the positive reciprocal at the actual translated
index. Its norm is unchanged by the sign relative to fixedRoot(n−1). -/
lemma scalar_root (n : ℤ) (hn : n≠0) :
    ActualScalarRoot318.root n=1/chartU (n-1) := by
  unfold ActualScalarRoot318.root
  rw [shifted_chart n hn]
  simp

lemma norm_coefficient (u : K) : normCoefficient u=AnchorNorm318.norm u := by
  norm_num [normCoefficient,AnchorNorm318.norm,QuadraticAlgebra.norm_def]
  ring

lemma reciprocal_norm (u : K) : normCoefficient (1/u)=(normCoefficient u)⁻¹ := by
  simp only [one_div,norm_coefficient,AnchorNorm318.norm_inv]

lemma scalar_inverse_norm (n : ℤ) (hn : n≠0) :
    ActualScalarRoot318.inverseNorm n=normCoefficient (chartU (n-1)) := by
  rw [ActualScalarRoot318.inverseNorm,scalar_root n hn,reciprocal_norm,inv_inv]

end ScalarTranslatedIndex318
