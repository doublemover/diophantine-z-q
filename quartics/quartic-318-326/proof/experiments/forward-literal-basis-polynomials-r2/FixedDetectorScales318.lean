module
public import PreparedPoleCRTWitness318
public import FiniteScale318
public section
noncomputable section
namespace FixedDetectorScales318
open ConcreteG8Domain CoherentMultipleCharts318
open CircuitReplay
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def product (labels : Fin 4 → ℤ) : K := ∏ j, fixedRoot (labels j)
@[expose] def normProduct (labels : Fin 4 → ℤ) : ℚ :=
  (product labels).re^2-2*(product labels).im^2
@[expose] def firstScale (labels : Fin 4 → ℤ) : ℚ :=
  ((product labels).re+normProduct labels)^2
@[expose] def secondScale (labels : Fin 4 → ℤ) : ℚ := (normProduct labels)^2

lemma fixedRoot_abs_gt_one (σ : K →+* ℝ) (n : ℤ) (hn : n≠0) :
    1< |σ (fixedRoot n)| := by
  have hu : chartU n≠0 := fun he => hn ((chartU_zero_iff n).mp he)
  have huR : σ (chartU n)≠0 := fun he => hu (σ.injective (by simpa using he))
  have hc := congrArg σ (chart_curve n)
  simp only [map_pow,map_sub,map_one,map_mul] at hc
  have hd := RealMultiples318.real_D_gt_one σ
  have hu4 : 0<(σ (chartU n))^4 := by
    have hp := sq_pos_of_ne_zero huR
    nlinarith [sq_pos_of_pos hp]
  have hd4 : 0<(σ CompressedOrientation318.D-1)*(σ (chartU n))^4 :=
    mul_pos (by linarith) hu4
  have hsmall : (σ (chartU n))^2<1 := by
    nlinarith [sq_nonneg (σ (chartV n)),sq_nonneg (σ (chartU n)),
      sq_nonneg ((σ (chartU n))^2-1)]
  have huabs : |σ (chartU n)|<1 := (sq_lt_one_iff_abs_lt_one _).mp hsmall
  have he : σ (fixedRoot n)*σ (chartU n)= -1 := by
    simp only [fixedRoot,map_neg,map_div₀,map_one]
    field_simp [huR]
  have habs : |σ (fixedRoot n)|*|σ (chartU n)|=1 := by
    simpa only [abs_mul,abs_neg,abs_one] using congrArg abs he
  by_contra! hroot
  nlinarith [abs_nonneg (σ (fixedRoot n)),abs_nonneg (σ (chartU n))]

lemma product_abs_gt_one (σ : K →+* ℝ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) :
    1< |σ (product labels)| := by
  have h0 := fixedRoot_abs_gt_one σ (labels 0) (hn 0)
  have h1 := fixedRoot_abs_gt_one σ (labels 1) (hn 1)
  have h2 := fixedRoot_abs_gt_one σ (labels 2) (hn 2)
  have h3 := fixedRoot_abs_gt_one σ (labels 3) (hn 3)
  have h01 : 1< |σ (fixedRoot (labels 0))|*|σ (fixedRoot (labels 1))| := by nlinarith
  have h012 : 1< |σ (fixedRoot (labels 0))|*|σ (fixedRoot (labels 1))|*
      |σ (fixedRoot (labels 2))| := by nlinarith
  simp only [product,Fin.prod_univ_four,map_mul,abs_mul]
  nlinarith

lemma normProduct_ne (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) : normProduct labels≠0 := by
  have hp : product labels≠0 := Finset.prod_ne_zero_iff.mpr fun j _ => fixedRoot_ne_zero _ (hn j)
  have hn' := QuadraticAlgebra.norm_eq_zero_iff_eq_zero (z:=product labels)
  simpa [normProduct,QuadraticAlgebra.norm_def,pow_two,mul_assoc] using mt hn'.mp hp

lemma sum_ne (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) :
    (product labels).re+normProduct labels≠0 := by
  have hp := product_abs_gt_one ActualQuadraticEmbeddings318.positiveEmbedding labels hn
  have hm := product_abs_gt_one ActualQuadraticEmbeddings318.negativeEmbedding labels hn
  have he : product labels=pair (product labels).re (product labels).im := by rfl
  rw [he] at hp hm
  simp only [ActualQuadraticEmbeddings318.positiveEmbedding,ActualQuadraticEmbeddings318.negativeEmbedding,
    ActualQuadraticEmbeddings318.realEmbedding_pair] at hp hm
  have hn' := FiniteScale318.norm_add_re_ne_zero (product labels).re (product labels).im hp
    (by simpa [sub_eq_add_neg] using hm)
  simpa [normProduct,add_comm] using hn'

lemma firstScale_pos (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) : 0<firstScale labels :=
  sq_pos_of_ne_zero (sum_ne labels hn)
lemma secondScale_pos (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) : 0<secondScale labels :=
  sq_pos_of_ne_zero (normProduct_ne labels hn)

lemma gate_product (w : Assignment) :
    pair (DetectorGateWitness318.fill w 143) (DetectorGateWitness318.fill w 144)=
      pair (w 79) (w 80)*pair (w 82) (w 83)*pair (w 85) (w 86)*pair (w 88) (w 89) := by
  ext <;> norm_num [DetectorGateWitness318.fill,DetectorGateWitness318.value139,
    DetectorGateWitness318.value140,DetectorGateWitness318.value141,DetectorGateWitness318.value142,
    DetectorGateWitness318.value143,DetectorGateWitness318.value144,pair] <;> ring

lemma source_root (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (j : Fin 4) :
    pair (ActualPadeRatios318.witness q labels h (79+3*j.val))
      (ActualPadeRatios318.witness q labels h (80+3*j.val))=
      RealGuardWitness318.root (CoherentMultiplePrefix318.u labels h)
        (CoherentMultiplePrefix318.v labels h) j := by
  fin_cases j <;> ext <;>
    simp [ActualPadeRatios318.witness,PadeRatioWitness318.fill,ActualPadeRatios318.base,
      CoherentMultiplePrefix318.witness,RealGuardWitness318.fill,pair]

/-- The scale product is fixed before h by the already proved root-sign
constancy, rather than bounded afresh on each later CRT progression. -/
lemma actual_product (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) (h : ℤ)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) :
    pair (DetectorGateWitness318.witness q labels h 143)
      (DetectorGateWitness318.witness q labels h 144)=product labels := by
  have hr (j : Fin 4) :
      pair (ActualPadeRatios318.witness q labels h (79+3*j.val))
        (ActualPadeRatios318.witness q labels h (80+3*j.val))=fixedRoot (labels j) :=
    (source_root q labels h j).trans (CoherentRootSign318.emitted_root_fixed labels h j (hn j)
      (((CoherentMultiplePrefix318.guards_iff labels h).mpr hg) j))
  rw [DetectorGateWitness318.witness,gate_product]
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  norm_num at h0 h1 h2 h3
  rw [h0,h1,h2,h3]
  simp only [product,Fin.prod_univ_four]


lemma actual_norm (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) (h : ℤ)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) :
    DetectorGateWitness318.witness q labels h 145=normProduct labels := by
  have hre := congrArg QuadraticAlgebra.re (actual_product q labels hn h hg)
  have him := congrArg QuadraticAlgebra.im (actual_product q labels hn h hg)
  simp only [pair] at hre him
  have he : DetectorGateWitness318.witness q labels h 145=
      (DetectorGateWitness318.witness q labels h 143)^2-
        2*(DetectorGateWitness318.witness q labels h 144)^2 := by
    dsimp [DetectorGateWitness318.witness,DetectorGateWitness318.fill,DetectorGateWitness318.value145]
    ring
  rw [he,hre,him]
  rfl

end FixedDetectorScales318
