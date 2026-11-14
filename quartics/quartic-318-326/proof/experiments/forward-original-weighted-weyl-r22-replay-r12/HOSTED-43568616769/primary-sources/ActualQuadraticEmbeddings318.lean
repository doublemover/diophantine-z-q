module
public import RelativeHeightEquiv
public section
noncomputable section
open NumberField ConcreteG8Domain
namespace ActualQuadraticEmbeddings318
set_option maxHeartbeats 0

lemma pair_decomposition (u v : ℚ) : pair u v=(u:K)+(v:K)*i := by
  ext <;> simp [pair,i]

lemma hom_pair {F : Type*} [Field F] [CharZero F] (φ : K →+* F) (u v : ℚ) :
    φ (pair u v)=(u:F)+(v:F)*φ i := by rw [pair_decomposition,map_add,map_mul,map_ratCast,map_ratCast]

@[expose] def realEmbedding (s : ℝ) (hs : s^2=2) : K →+* ℝ :=
  (QuadraticAlgebra.lift (a:=(2:ℚ)) (b:=(0:ℚ)) ⟨s,by
    simpa [Algebra.smul_def,pow_two] using hs⟩).toRingHom

lemma realEmbedding_pair (s : ℝ) (hs : s^2=2) (u v : ℚ) :
    realEmbedding s hs (pair u v)=(u:ℝ)+(v:ℝ)*s := by
  simp [realEmbedding,QuadraticAlgebra.lift_apply_apply,pair,Algebra.smul_def]

@[expose] def positiveEmbedding : K →+* ℝ := realEmbedding (Real.sqrt 2) (Real.sq_sqrt (by norm_num))
@[expose] def negativeEmbedding : K →+* ℝ := realEmbedding (-Real.sqrt 2) (by simpa using Real.sq_sqrt (by norm_num : (0:ℝ)≤2))
@[expose] def positiveComplex : K →+* ℂ := Complex.ofRealHom.comp positiveEmbedding
@[expose] def negativeComplex : K →+* ℂ := Complex.ofRealHom.comp negativeEmbedding

lemma complex_embedding_cases (φ : K →+* ℂ) : φ=positiveComplex ∨ φ=negativeComplex := by
  have hi : (φ i)^2=(2:ℂ) := by simpa only [map_pow,map_ofNat] using congrArg φ i_square
  have hs : ((Real.sqrt 2:ℝ):ℂ)^2=(2:ℂ) := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hi.trans hs.symm) with h|h
  · left
    ext x
    rcases x with ⟨u,v⟩
    change φ (pair u v)=positiveComplex (pair u v)
    rw [hom_pair,h]
    simp [positiveComplex,positiveEmbedding,realEmbedding_pair]
  · right
    ext x
    rcases x with ⟨u,v⟩
    change φ (pair u v)=negativeComplex (pair u v)
    rw [hom_pair,h]
    simp [negativeComplex,negativeEmbedding,realEmbedding_pair]

lemma every_embedding_real (φ : K →+* ℂ) : ComplexEmbedding.IsReal φ := by
  rw [ComplexEmbedding.isReal_iff]
  rcases complex_embedding_cases φ with rfl|rfl <;>
    ext x <;> simp [positiveComplex,negativeComplex,ComplexEmbedding.conjugate]

lemma every_infinite_place_real (w : InfinitePlace K) : InfinitePlace.IsReal w :=
  InfinitePlace.isReal_iff.mpr (every_embedding_real w.embedding)

lemma infinite_place_real_value (w : InfinitePlace K) :
    ∃σ : K →+* ℝ, ∀x, w x=|σ x| := by
  refine ⟨InfinitePlace.embedding_of_isReal (every_infinite_place_real w),fun x => ?_⟩
  simpa only [Real.norm_eq_abs] using (InfinitePlace.norm_embedding_of_isReal (every_infinite_place_real w) x).symm

lemma complex_embeddings_ne : positiveComplex≠negativeComplex := by
  intro h
  have hi := congrArg (fun φ : K →+* ℂ => φ i) h
  have hs : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hp := congrArg Complex.re hi
  simp [i,positiveComplex,negativeComplex,positiveEmbedding,negativeEmbedding,realEmbedding_pair] at hp
  linarith

@[expose] def embeddingsEquiv : Fin 2 ≃ (K →+* ℂ) := Equiv.ofBijective
  (fun j => if j=0 then positiveComplex else negativeComplex) (by
    constructor
    · intro j k h
      fin_cases j <;> fin_cases k <;> simp_all [complex_embeddings_ne,Ne.symm complex_embeddings_ne]
    · intro φ
      rcases complex_embedding_cases φ with h|h
      · exact ⟨0,by simpa using h.symm⟩
      · exact ⟨1,by simpa using h.symm⟩)

lemma infinite_part_pair [NumberField K] (u v : ℚ) :
    (∏w : InfinitePlace K, max (w (pair u v)) 1 ^ w.mult)=
      max |(u:ℝ)+(v:ℝ)*Real.sqrt 2| 1 * max |(u:ℝ)-(v:ℝ)*Real.sqrt 2| 1 := by
  rw [RelativeHeightEquiv.infinite_part_embeddings]
  rw [←Fintype.prod_equiv embeddingsEquiv
    (fun j => max ‖embeddingsEquiv j (pair u v)‖ 1) (fun φ => max ‖φ (pair u v)‖ 1) (fun _ => rfl)]
  rw [Fin.prod_univ_two]
  change max ‖(positiveEmbedding (pair u v):ℂ)‖ 1 * max ‖(negativeEmbedding (pair u v):ℂ)‖ 1 = _
  simp only [Complex.norm_real,Real.norm_eq_abs,positiveEmbedding,negativeEmbedding,realEmbedding_pair,mul_neg,sub_eq_add_neg]

#print axioms pair_decomposition
#print axioms hom_pair
#print axioms realEmbedding_pair
#print axioms complex_embedding_cases
#print axioms every_embedding_real
#print axioms every_infinite_place_real
#print axioms infinite_place_real_value
#print axioms complex_embeddings_ne
#print axioms embeddingsEquiv
#print axioms infinite_part_pair
end ActualQuadraticEmbeddings318
