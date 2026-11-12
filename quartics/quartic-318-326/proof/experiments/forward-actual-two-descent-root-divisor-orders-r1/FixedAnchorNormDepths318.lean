module
public import PreparedLucasSource318
public import OddMultiplesThree318
public section
noncomputable section
namespace FixedAnchorNormDepths318
open ConcreteG8Domain (K)
open CoherentMultipleCharts318 ScalarTranslatedIndex318 ScalarIndexValuations318
open FixedDetectorScales318 WeierstrassCurve.Affine
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

lemma odd_nonzero (n : ℤ) (hn : Odd n) : n≠0 := by
  have h := Int.odd_iff.mp hn
  omega

lemma fixed_norm_two (n : ℤ) (hn : Odd n) :
    padicValRat 2 (AnchorNorm318.norm (fixedRoot n))= -3 := by
  have hv : padicValInt 2 n=0 := padicValInt.eq_zero_of_not_dvd
    (by rw [Int.dvd_iff_emod_eq_zero]; have h := Int.odd_iff.mp hn; omega)
  rw [fixed_root_norm,padicValRat.inv,chart_norm_two n (odd_nonzero n hn),hv]
  norm_num

/-- The actual odd source point has3-adic unit abscissa and hence unit root norm. -/
lemma fixed_norm_three (n : ℤ) (hn : Odd n) :
    padicValRat 3 (AnchorNorm318.norm (fixedRoot n))=0 := by
  obtain ⟨x,y,h,hpt,_⟩ := GeneratorMultiplesTwo318.integer_multiple n (odd_nonzero n hn)
  have hv := OddMultiplesThree318.identified_odd_multiple_norm n hn x y h hpt
  have hs : (fixedRoot n)^2=x := by
    rw [fixedRoot_square n (odd_nonzero n hn),hpt]
    simp only [Point.xRep_some,Matrix.cons_val_zero]
  exact AnchorNorm318.root_norm_value 3 (fixedRoot n) x hs 0 (by simpa using hv)

lemma normProduct_as_product (labels : Fin 4 → ℤ) :
    normProduct labels=∏ j, AnchorNorm318.norm (fixedRoot (labels j)) := by
  change GeneratorScalarProgression318.normCoefficient (product labels)=_
  rw [norm_coefficient,product]
  exact map_prod QuadraticAlgebra.norm _ _

/-- The exact factor4096 in the final source cancels the four odd-root
norm depths at2. It is not a freely adjustable normalization constant. -/
theorem actual_product_depths (labels : Fin 4 → ℤ) (hn : ∀ j, Odd (labels j)) :
    padicValRat 2 (normProduct labels)= -12 ∧ padicValRat 3 (normProduct labels)=0 := by
  have hN (j : Fin 4) : AnchorNorm318.norm (fixedRoot (labels j))≠0 :=
    AnchorNorm318.norm_ne_zero (fixedRoot_ne_zero _ (odd_nonzero _ (hn j)))
  constructor
  · simp [normProduct_as_product,Fin.prod_univ_four,padicValRat.mul,hN,
      fixed_norm_two _ (hn 0),fixed_norm_two _ (hn 1),
      fixed_norm_two _ (hn 2),fixed_norm_two _ (hn 3)]
  · simp [normProduct_as_product,Fin.prod_univ_four,padicValRat.mul,hN,
      fixed_norm_three _ (hn 0),fixed_norm_three _ (hn 1),
      fixed_norm_three _ (hn 2),fixed_norm_three _ (hn 3)]

end FixedAnchorNormDepths318
