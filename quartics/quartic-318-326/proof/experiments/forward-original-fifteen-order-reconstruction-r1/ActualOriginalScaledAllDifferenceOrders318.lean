module
public import ActualOriginalCompactPairedProduct318
public section
noncomputable section
namespace ActualOriginalScaledAllDifferenceOrders318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalIteratedDifference318 ActualOriginalCompactPairedProduct318
open ActualOriginalUniformPairedMixedConstants318 ActualOriginalScaledPairedMixedDifference318
open scoped ContDiff

lemma actual_mixed_comp_additive {E F G : Type*} [Add E] [Add F] [Sub G]
    (T : E → F) (hT : ∀ x u, T (x+u)=T x+T u) (f : F → G) (us : List E) :
    ∀ x, mixedDifference (fun z => f (T z)) us x=
      mixedDifference f (us.map T) (T x) := by
  induction us with
  | nil => intro x; rfl
  | cons u us ih => intro x; simp only [mixedDifference,List.map_cons,ih,hT]

lemma actual_mixed_ofReal {E : Type*} [Add E] (f : E → ℝ) (us : List E) :
    ∀ x, mixedDifference (fun z => (f z : ℂ)) us x=(mixedDifference f us x : ℂ) := by
  induction us with
  | nil => intro x; rfl
  | cons u us ih => intro x; simp only [mixedDifference,ih,Complex.ofReal_sub]

lemma actual_lattice_pair_mixed_identity (B : ℝ) (W : Coordinates ℝ → ℝ)
    (h : Coordinates ℤ) (us : List (Coordinates ℤ)) (x : Coordinates ℤ) :
    mixedDifference (latticePairedWeight B W h) us x=
      (mixedDifference (translatedPairedWeight W (B⁻¹ • integerEmbed h))
        (us.map (fun u => B⁻¹ • integerEmbed u)) (B⁻¹ • integerEmbed x) : ℂ) := by
  have he : latticePairedWeight B W h=fun z =>
      (translatedPairedWeight W (B⁻¹ • integerEmbed h) (B⁻¹ • integerEmbed z) : ℂ) :=
    funext (actual_lattice_pair_real B W h)
  rw [he,actual_mixed_ofReal,actual_mixed_comp_additive]
  exact fun z u => by rw [integerEmbed_add,smul_add]

lemma actual_scaled_direction_product (B : ℝ) (hB : 0<B) (us : List (Coordinates ℤ)) :
    directionProduct (us.map (fun u => B⁻¹ • integerEmbed u))=
      (B⁻¹)^us.length*directionProduct (us.map integerEmbed) := by
  induction us with
  | nil => simp only [List.map_nil,List.length_nil,directionProduct,pow_zero,one_mul]
  | cons u us ih =>
    simp only [List.map_cons,List.length_cons,directionProduct,ih,norm_smul,
      Real.norm_eq_abs,abs_inv,abs_of_pos hB,pow_succ]
    ring

/-- Every order k of the ACTUAL complex lattice paired weight has
its own produced constant and exact B^-k scaling, uniformly in every
integer displacement,base point and complete list of directions. -/
theorem actual_scaled_paired_all_orders (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (k : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ B : ℝ, 0<B → ∀ h : Coordinates ℤ,
      ∀ us : List (Coordinates ℤ), us.length=k → ∀ x,
      ‖mixedDifference (latticePairedWeight B W h) us x‖≤
        (C/B^k)*directionProduct (us.map integerEmbed) := by
  obtain ⟨C,hC,hb⟩ := actual_uniform_paired_all_orders W hW hc k
  refine ⟨C,hC,fun B hB h us hu x => ?_⟩
  rw [actual_lattice_pair_mixed_identity,Complex.norm_real]
  have hh := hb (B⁻¹ • integerEmbed h) (us.map (fun u => B⁻¹ • integerEmbed u))
    (by simpa only [List.length_map] using hu) (B⁻¹ • integerEmbed x)
  rw [actual_scaled_direction_product B hB,hu] at hh
  simpa only [div_eq_mul_inv,inv_pow,mul_assoc] using hh

end ActualOriginalScaledAllDifferenceOrders318
