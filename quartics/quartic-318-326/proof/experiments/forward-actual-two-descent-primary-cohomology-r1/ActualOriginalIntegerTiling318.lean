module
public import ActualOriginalCoordinateFrequency318
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Algebra.Order.Floor.Ring
public section
noncomputable section
namespace ActualOriginalIntegerTiling318
open QuadricCRTAssembly318 MeasureTheory Set
set_option maxHeartbeats 16000000

@[expose] def integerEmbed (z : Coordinates ℤ) : Coordinates ℝ :=
  (((z.1.1 : ℝ),(z.1.2 : ℝ)),((z.2.1.1 : ℝ),(z.2.1.2 : ℝ)),(z.2.2 : ℝ))

lemma integerEmbed_zero : integerEmbed 0 = 0 := by simp [integerEmbed]
lemma integerEmbed_add (a b : Coordinates ℤ) : integerEmbed (a+b)=integerEmbed a+integerEmbed b := by
  simp [integerEmbed]

/-- Translation by the literal ORIGINAL integer lattice, not an abstract
isomorphic lattice or a changed Euclidean measure. -/
instance originalIntegerAction : AddAction (Coordinates ℤ) (Coordinates ℝ) where
  vadd z x := integerEmbed z+x
  zero_vadd x := by simp [integerEmbed_zero]
  add_vadd a b x := by rw [integerEmbed_add,add_assoc]

lemma original_vadd (z : Coordinates ℤ) (x : Coordinates ℝ) :
    z +ᵥ x = integerEmbed z+x := rfl

instance originalIntegerMeasurable : MeasurableConstVAdd (Coordinates ℤ) (Coordinates ℝ) where
  measurable_const_vadd z := measurable_const.add measurable_id

instance originalIntegerInvariant : VAddInvariantMeasure (Coordinates ℤ) (Coordinates ℝ) volume where
  measure_preimage_vadd z s _ := measure_preimage_add volume (integerEmbed z) s

@[expose] def originalCube : Set (Coordinates ℝ) :=
  (Ico (0 : ℝ) 1 ×ˢ Ico 0 1) ×ˢ (Ico 0 1 ×ˢ Ico 0 1) ×ˢ Ico 0 1

lemma originalCube_measurable : MeasurableSet originalCube :=
  (measurableSet_Ico.prod measurableSet_Ico).prod
    ((measurableSet_Ico.prod measurableSet_Ico).prod measurableSet_Ico)

/-- The exact ORIGINAL product-volume normalization of the unit cube. -/
lemma actual_original_cube_volume : (volume : Measure (Coordinates ℝ)) originalCube = 1 := by
  simp [originalCube,Measure.prod_prod,Real.volume_Ico]

@[expose] def negativeFloor (x : Coordinates ℝ) : Coordinates ℤ :=
  ((-⌊x.1.1⌋,-⌊x.1.2⌋),(-⌊x.2.1.1⌋,-⌊x.2.1.2⌋),-⌊x.2.2⌋)

lemma scalar_translate_unit_interval (n : ℤ) (x : ℝ) :
    (n : ℝ)+x ∈ Ico (0 : ℝ) 1 ↔ n = -⌊x⌋ := by
  constructor
  · rintro ⟨h0,h1⟩
    have hf : ⌊x⌋ = -n := Int.floor_eq_iff.mpr (by
      simp only [Int.cast_neg]
      constructor <;> linarith)
    omega
  · rintro rfl
    have h0 := Int.fract_nonneg x
    have h1 := Int.fract_lt_one x
    simpa only [Int.cast_neg,Int.fract,sub_eq_add_neg,add_comm] using And.intro h0 h1

lemma actual_unique_cube_translate (x : Coordinates ℝ) (z : Coordinates ℤ) :
    z +ᵥ x ∈ originalCube ↔ z = negativeFloor x := by
  simp only [original_vadd,integerEmbed,originalCube,Set.mem_prod,
    Prod.fst_add,Prod.snd_add,scalar_translate_unit_interval]
  constructor
  · rintro ⟨⟨ha,hb⟩,⟨⟨hc,hd⟩,hw⟩⟩
    exact Prod.ext (Prod.ext ha hb) (Prod.ext (Prod.ext hc hd) hw)
  · rintro rfl
    exact ⟨⟨rfl,rfl⟩,⟨⟨rfl,rfl⟩,rfl⟩⟩

/-- Every original point has exactly one integer translate in the
half-open original unit cube, including all boundary points. -/
theorem actual_original_cube_fundamental :
    IsAddFundamentalDomain (Coordinates ℤ) originalCube (volume : Measure (Coordinates ℝ)) := by
  apply IsAddFundamentalDomain.mk' originalCube_measurable.nullMeasurableSet
  intro x
  exact ⟨negativeFloor x,(actual_unique_cube_translate x _).mpr rfl,
    fun z hz => (actual_unique_cube_translate x z).mp hz⟩

/-- Exact countable tiling in the ORIGINAL product Haar volume. The
integrability assumption is on the literal function being tiled. -/
theorem actual_original_integral_tiling (f : Coordinates ℝ → ℂ) (hf : Integrable f) :
    (∫ x : Coordinates ℝ, f x) =
      ∑' z : Coordinates ℤ, ∫ x in originalCube, f (integerEmbed z+x) := by
  simpa only [original_vadd] using
    actual_original_cube_fundamental.integral_eq_tsum'' f hf

end ActualOriginalIntegerTiling318
