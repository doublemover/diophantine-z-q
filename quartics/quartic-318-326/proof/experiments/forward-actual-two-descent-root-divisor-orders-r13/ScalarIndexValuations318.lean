module
public import ScalarTranslatedIndex318
public section
noncomputable section
namespace ScalarIndexValuations318
open ConcreteG8Domain (K)
open CoherentMultipleCharts318 GeneratorScalarProgression318 ScalarTranslatedIndex318
open WeierstrassCurve.Affine
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

lemma fixed_root_norm (n : ℤ) :
    AnchorNorm318.norm (fixedRoot n)=(normCoefficient (chartU n))⁻¹ := by
  rw [←norm_coefficient,fixedRoot]
  have hneg (x : K) : normCoefficient (-x)=normCoefficient x := by simp [normCoefficient]
  rw [hneg,reciprocal_norm]

/-- Actual2-adic common-root norm at every nonzero index. -/
lemma chart_norm_two (n : ℤ) (hn : n≠0) :
    padicValRat 2 (normCoefficient (chartU n))=3+2*(padicValInt 2 n:ℤ) := by
  obtain ⟨x,y,h,hpt,hx,hval⟩ := GeneratorMultiplesTwo318.norm_integer_multiple n hn
  have hs : (fixedRoot n)^2=x := by
    rw [fixedRoot_square n hn,hpt]
    simp only [Point.xRep_some,Matrix.cons_val_zero]
  have hv := AnchorNorm318.root_norm_value 2 (fixedRoot n) x hs
    (-3-2*(padicValInt 2 n:ℤ)) (by rw [hval]; ring)
  rw [fixed_root_norm,padicValRat.inv] at hv
  omega

/-- Actual3-adic norm on the required even-index subgroup. -/
lemma chart_norm_three (n : ℤ) (hn : n≠0) (heven : Even n) :
    padicValRat 3 (normCoefficient (chartU n))=2+2*(padicValInt 3 n:ℤ) := by
  obtain ⟨x,y,h,hpt,_⟩ := GeneratorMultiplesTwo318.integer_multiple n hn
  have hval := GeneratorMultiplesThree318.identified_even_multiple_norm n hn heven x y h hpt
  have hs : (fixedRoot n)^2=x := by
    rw [fixedRoot_square n hn,hpt]
    simp only [Point.xRep_some,Matrix.cons_val_zero]
  have hv := AnchorNorm318.root_norm_value 3 (fixedRoot n) x hs
    (-2-2*(padicValInt 3 n:ℤ)) (by rw [hval]; ring)
  rw [fixed_root_norm,padicValRat.inv] at hv
  omega

/-- The scalar depth is now tied to the actual translated integer n−1,
not a freely supplied scalar norm or an unproved Kummer sign choice. -/
lemma scalar_norm_two (n : ℤ) (hn : n≠0) (hn1 : n≠1) :
    padicValRat 2 (ActualScalarRoot318.inverseNorm n)=3+2*(padicValInt 2 (n-1):ℤ) := by
  rw [scalar_inverse_norm n hn]
  exact chart_norm_two (n-1) (by omega)

lemma scalar_norm_three (n : ℤ) (hn : n≠0) (hn1 : n≠1) (heven : Even (n-1)) :
    padicValRat 3 (ActualScalarRoot318.inverseNorm n)=2+2*(padicValInt 3 (n-1):ℤ) := by
  rw [scalar_inverse_norm n hn]
  exact chart_norm_three (n-1) (by omega) heven

end ScalarIndexValuations318
