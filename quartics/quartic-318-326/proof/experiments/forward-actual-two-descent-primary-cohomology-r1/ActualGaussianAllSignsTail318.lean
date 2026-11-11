module
public import ActualGaussianSignAction318
public section
noncomputable section
namespace ActualGaussianAllSignsTail318
open scoped BigOperators
open QuadricCRTAssembly318 LiteralSliceBoxCount318 ActualGaussianSignAction318
open ActualGaussianFullSourceTail318 ActualGaussianGrowingCutoff318 OriginalWeightedSelberg318
set_option maxHeartbeats 14000000

/-- Actual original source, allowing either adjacent norm at each of the
two distinct positions. The point is counted once, even if signs overlap. -/
@[expose] def SignedSource (B : ℕ) (κ : ℤ) (Y : ℕ) :=
  {v : Quadric κ // InBox B v.1 ∧ ∃ s t : Bool, ∃ p : ℕ,
    p.Prime ∧ Y<p ∧ (p:ℤ)∣signedG s v.1 ∧ (p:ℤ)∣signedH t v.1}
instance signed_finite (B : ℕ) (κ : ℤ) (Y : ℕ) : Finite (SignedSource B κ Y) :=
  Finite.of_injective (fun v => (⟨v.1,v.2.1⟩ : BoundedQuadric B κ))
    (fun _ _ h => Subtype.ext (congrArg Subtype.val h))

lemma signed_cover (B : ℕ) (κ : ℤ) (Y : ℕ) (hY : cutoff κ B≤Y)
    (v : SignedSource B κ Y) :
    ∃ z : Bool×Bool×AllPrimeSource B κ (cutoff κ B),
      quadricAction κ z.1 z.2.1 z.2.2.1=v.1 := by
  obtain ⟨s,t,p,hp,hpY,hG,hH⟩ := v.2.2
  let w : AllPrimeSource B κ (cutoff κ B) :=
    ⟨quadricAction κ s t v.1,(box_transform B s t v.1.1).mpr v.2.1,p,hp,
      hY.trans_lt hpY,by
        change (p:ℤ)∣LiteralAdjacentNormSlice318.G (transform s t v.1.1)
        rw [(actual_signed_norms s t v.1.1).1]
        exact hG,by
        change (p:ℤ)∣LiteralAdjacentNormSlice318.H (transform s t v.1.1)
        rw [(actual_signed_norms s t v.1.1).2]
        exact hH⟩
  refine ⟨(s,t,w),?_⟩
  apply Subtype.ext
  exact transform_twice s t v.1.1
@[expose] def sourceChoice (B : ℕ) (κ : ℤ) (Y : ℕ) (hY : cutoff κ B≤Y) :
    SignedSource B κ Y → Bool×Bool×AllPrimeSource B κ (cutoff κ B) :=
  fun v => (signed_cover B κ Y hY v).choose
lemma choice_forget (B : ℕ) (κ : ℤ) (Y : ℕ) (hY : cutoff κ B≤Y)
    (v : SignedSource B κ Y) :
    quadricAction κ (sourceChoice B κ Y hY v).1 (sourceChoice B κ Y hY v).2.1
      (sourceChoice B κ Y hY v).2.2.1=v.1 := (signed_cover B κ Y hY v).choose_spec
lemma choice_injective (B : ℕ) (κ : ℤ) (Y : ℕ) (hY : cutoff κ B≤Y) :
    Function.Injective (sourceChoice B κ Y hY) := by
  intro v w he
  apply Subtype.ext
  have hh := congrArg (fun z : Bool×Bool×AllPrimeSource B κ (cutoff κ B) =>
    quadricAction κ z.1 z.2.1 z.2.2.1) he
  simpa only [choice_forget] using hh

variable {J : Type*} [Fintype J] [DecidableEq J]
@[expose] def signedMass (B : ℕ) (κ : ℤ) (Y : ℕ) (γ : J → ℤ) : ℝ := by
  classical
  letI : Fintype (SignedSource B κ Y) := Fintype.ofFinite _
  exact ∑ v : SignedSource B κ Y,weight κ γ v.1

/-- Exact sign transport preserves every original logarithmic form, not
merely its size. All four signs cost at most4, without disjointness. -/
theorem actual_all_signs_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0) (Y : ℕ)
    (hY : cutoff κ B≤Y) (γ : J → ℤ) :
    signedMass B κ Y γ≤4*growingConstant κ γ*(B:ℝ)^(3-(1:ℝ)/200) := by
  classical
  letI : Fintype (SignedSource B κ Y) := Fintype.ofFinite _
  letI : Fintype (FullSource B κ (cutoff κ B)) := Fintype.ofFinite _
  letI : Fintype (AllPrimeSource B κ (cutoff κ B)) :=
    Fintype.ofEquiv (FullSource B κ (cutoff κ B))
      (allPrimeEquiv B κ hκ (cutoff κ B) (cutoff_coefficient κ B)).symm
  let wt : Bool×Bool×AllPrimeSource B κ (cutoff κ B) → ℝ :=
    fun z => weight κ γ z.2.2.1
  have hh := hasSum_le_inj (sourceChoice B κ Y hY) (choice_injective B κ Y hY)
    (fun z _ => weight_nonneg κ γ z.2.2.1)
    (fun v => le_of_eq (by
      have he := congrArg (weight κ γ) (choice_forget B κ Y hY v)
      rw [weight_transform] at he
      exact he.symm))
    (hasSum_fintype (fun v : SignedSource B κ Y => weight κ γ v.1)) (hasSum_fintype wt)
  have he : (∑ z : Bool×Bool×AllPrimeSource B κ (cutoff κ B),wt z)=
      4*allPrimeMass B κ hκ γ := by
    simp only [wt,Fintype.sum_prod_type,Fintype.sum_bool,allPrimeMass]
    ring
  rw [he] at hh
  have hs := mul_le_mul_of_nonneg_left (actual_all_prime_growing_tail B hB κ hκ γ)
    (by norm_num : (0:ℝ)≤4)
  change signedMass B κ Y γ≤_
  exact hh.trans (by simpa only [mul_assoc] using hs)

end ActualGaussianAllSignsTail318
