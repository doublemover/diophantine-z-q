module
public import PELOriginalPeriodIntegerCoordinates318
public import PELOriginalTorsionPointComparison318
public section
noncomputable section
namespace PELOriginalTorsionRepresentatives318
open QuaternionicRealPeriod318 PELOriginalPeriodLattice318 PELComplexPeriodSurface318
open DiscreteComplexPeriodAtlas318 PELOriginalPeriodIntegerCoordinates318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ) (hn : 0<n)
abbrev Labels := Fin 4 → Fin n
@[expose] def vector (a : Labels n) : ComplexVectors :=
  coordinates τ hτ (fun i => ((a i).val : ℝ)/(n : ℝ))
include hn in
lemma multiple_vector (a : Labels n) : n • vector τ hτ n a=
    coordinates τ hτ (fun i => ((a i).val : ℝ)) := by
  have hnR : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  rw [vector,←Nat.cast_smul_eq_nsmul ℝ,←map_smul]
  congr 1
  funext i
  change (n : ℝ)*(((a i).val : ℝ)/(n : ℝ))=((a i).val : ℝ)
  field_simp [hnR]
@[expose] def point (a : Labels n) : {q : Surface τ // n • q=0} :=
  ⟨projection (Periods τ) (vector τ hτ n a),by
    change n • (QuotientAddGroup.mk' (Periods τ)) (vector τ hτ n a)=0
    rw [←map_nsmul,multiple_vector τ hτ n hn]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact coordinates_mem τ hτ (fun i => ((a i).val : ℤ))⟩

lemma point_injective : Function.Injective (point τ hτ n hn) := by
  intro a b hab
  have hq : projection (Periods τ) (vector τ hτ n a-vector τ hτ n b)=0 := by
    change (QuotientAddGroup.mk' (Periods τ)) (_-_)=0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hab)
  obtain ⟨k,hk⟩ := (mem_iff τ hτ _).mp ((QuotientAddGroup.eq_zero_iff _).mp hq)
  have hc : (fun i : Fin 4 => ((a i).val : ℝ)/(n : ℝ))- (fun i => ((b i).val : ℝ)/(n : ℝ))=
      fun i => (k i : ℝ) := by
    apply (coordinates τ hτ).injective
    rw [map_sub]
    exact hk
  have hnR : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  funext i
  apply Fin.ext
  have hi : (((a i).val : ℝ)-((b i).val : ℝ))/(n : ℝ)=(k i : ℝ) := by
    simpa only [Pi.sub_apply,←sub_div] using congrFun hc i
  have hz : ((a i).val : ℤ)-((b i).val : ℤ)=(k i)*(n : ℤ) := by
    exact_mod_cast (div_eq_iff hnR).mp hi
  have ha0 : (0 : ℤ)≤(a i).val := by omega
  have hb0 : (0 : ℤ)≤(b i).val := by omega
  have han : ((a i).val : ℤ)<n := by exact_mod_cast (a i).isLt
  have hbn : ((b i).val : ℤ)<n := by exact_mod_cast (b i).isLt
  have hnZ : (0 : ℤ)<n := by exact_mod_cast hn
  have hk0 : k i=0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hneg|hpos
    · have : k i≤-1 := by omega
      nlinarith
    · have : 1≤k i := by omega
      nlinarith
  rw [hk0,zero_mul] at hz
  omega
end PELOriginalTorsionRepresentatives318
