module
public import PrueferCanonicalTateTower318
import all PrueferCanonicalTateTower318
import all PrimaryTateTower318
public section
noncomputable section
namespace PrueferBoundedCoordinates318
open ActualTwoDescentDyadicPrueferModel318 PrueferCanonicalTateTower318

/-- Numerator coordinates in Q/Z at the literal level 2^n. -/
def encode (n a : ℕ) : AddCircle (1 : ℚ) := a • circle n

 theorem encode_fraction (n a : ℕ) :
    encode n a = ((a : ℚ) / (2 : ℚ)^n : ℚ) := by
  unfold encode circle
  rw [← AddCircle.coe_nsmul]
  congr 1
  simp [nsmul_eq_mul]

 theorem encode_injective_bounded (n a b : ℕ)
    (ha : a < 2^n) (hb : b < 2^n) (h : encode n a = encode n b) : a = b := by
  letI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
  have hd : (0 : ℚ) < (2 : ℚ)^n := pow_pos (by norm_num) _
  have ha' : (a : ℚ) / (2 : ℚ)^n ∈ Set.Ico (0 : ℚ) (0+1) := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hd.le
    · have : (a : ℚ) < (2 : ℚ)^n := by exact_mod_cast ha
      simpa using (div_lt_one hd).2 this
  have hb' : (b : ℚ) / (2 : ℚ)^n ∈ Set.Ico (0 : ℚ) (0+1) := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hd.le
    · have : (b : ℚ) < (2 : ℚ)^n := by exact_mod_cast hb
      simpa using (div_lt_one hd).2 this
  rw [encode_fraction, encode_fraction] at h
  have he := (AddCircle.coe_eq_coe_iff_of_mem_Ico ha' hb').mp h
  have he' : (a : ℚ) = (b : ℚ) := (div_left_inj' (ne_of_gt hd)).mp he
  exact_mod_cast he'

 theorem exists_bounded_coordinate (n : ℕ) (x : AddCircle (1 : ℚ))
    (hx : (2^n) • x = 0) : ∃ a : ℕ, a < 2^n ∧ encode n a = x := by
  letI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
  obtain ⟨a, ha, he⟩ :=
    (AddCircle.nsmul_eq_zero_iff (p := (1 : ℚ)) (pow_pos (by decide) n)).mp hx
  refine ⟨a, ha, ?_⟩
  simpa [encode_fraction] using he

/-- Reduction of the numerator is exactly reduction modulo the level. -/
 theorem encode_mod (n a : ℕ) : encode n (a % (2^n)) = encode n a := by
  have hzero : ((2^n) * (a / (2^n))) • circle n = 0 := by
    rw [mul_nsmul, circle_annihilated, nsmul_zero]
  conv_rhs => rw [← Nat.mod_add_div a (2^n)]
  unfold encode
  rw [add_nsmul, hzero, add_zero]

 theorem encode_transition (n a : ℕ) : 2 • encode (n+1) a = encode n a := by
  unfold encode
  rw [smul_comm, circle_transition]

/-- The unique bounded numerator of an actual primary-component point.
The torsion proof fixes its level; the underlying group is not replaced. -/
def coordinate (n : ℕ) (x : Additive PrueferTwo) (hx : (2^n) • x = 0) :
    Fin (2^n) := by
  have hc : (2^n) • x.toMul.val.toAdd = 0 :=
    congrArg (fun y : Additive PrueferTwo => y.toMul.val.toAdd) hx
  let h := exists_bounded_coordinate n x.toMul.val.toAdd hc
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

 theorem coordinate_spec (n : ℕ) (x : Additive PrueferTwo) (hx : (2^n) • x = 0) :
    encode n (coordinate n x hx).val = x.toMul.val.toAdd := by
  exact (Classical.choose_spec
    (exists_bounded_coordinate n x.toMul.val.toAdd
      (congrArg (fun y : Additive PrueferTwo => y.toMul.val.toAdd) hx))).2

/-- Adjacent coordinates of every actual Prüfer Tate tower reduce modulo
2^n. This is a compatibility theorem, not merely a count of coordinates. -/
 theorem tower_coordinate_transition
    (x : PrimaryTateTower318.tower (Additive PrueferTwo)) (n : ℕ) :
    (coordinate (n+1) (x.val (n+1)) (by exact x.property.1 (n+1))).val % (2^n) =
      (coordinate n (x.val n) (by exact x.property.1 n)).val := by
  apply encode_injective_bounded n
  · exact Nat.mod_lt _ (pow_pos (by decide) n)
  · exact (coordinate n (x.val n) (x.property.1 n)).isLt
  · rw [encode_mod, ← encode_transition, coordinate_spec, coordinate_spec]
    exact congrArg (fun y : Additive PrueferTwo => y.toMul.val.toAdd)
      (x.property.2 n)

 theorem encode_iterated_transition (n k a : ℕ) :
    (2^k) • encode (n+k) a = encode n a :=
  BoundedPrimaryTowerVanishing318.iterate_transition
    (fun j => encode j a) (fun j => encode_transition j a) n k

/-- Compatibility at all levels, with the actual doubling transition
iterated k times and reduction modulo 2^n on bounded numerators. -/
 theorem tower_coordinate_reduction
    (x : PrimaryTateTower318.tower (Additive PrueferTwo)) (n k : ℕ) :
    (coordinate (n+k) (x.val (n+k)) (by exact x.property.1 (n+k))).val % (2^n) =
      (coordinate n (x.val n) (by exact x.property.1 n)).val := by
  apply encode_injective_bounded n
  · exact Nat.mod_lt _ (pow_pos (by decide) n)
  · exact (coordinate n (x.val n) (x.property.1 n)).isLt
  · rw [encode_mod, ← encode_iterated_transition n k, coordinate_spec, coordinate_spec]
    exact congrArg (fun y : Additive PrueferTwo => y.toMul.val.toAdd)
      (BoundedPrimaryTowerVanishing318.iterate_transition x.val x.property.2 n k)

/-- Equality of bounded coordinates determines the whole actual tower. -/
 theorem tower_ext_coordinates
    (x y : PrimaryTateTower318.tower (Additive PrueferTwo))
    (h : ∀ n, coordinate n (x.val n) (by exact x.property.1 n) =
      coordinate n (y.val n) (by exact y.property.1 n)) : x = y := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  change (x.val n).toMul.val.toAdd = (y.val n).toMul.val.toAdd
  rw [← coordinate_spec n (x.val n) (x.property.1 n),
    ← coordinate_spec n (y.val n) (y.property.1 n), h n]

end PrueferBoundedCoordinates318
