module
public import ActualOddRegularResidueTower318
public section
noncomputable section
namespace ActualOddBadBaseCount318
open QuadricCRTAssembly318 ActualOddRegularLift318 ActualOddRegularResidueTower318
open FiniteNormDifferenceCount318
open scoped BigOperators
set_option maxHeartbeats 26000000

@[expose] def differenceOrigin {F : Type*} [Field F] : NormDifference (0:F) :=
  ⟨((0,0),(0,0)),by ring⟩

/-- At kappa=0 in the residue field, the genuine regular quadric is
the nonzero FOUR-coordinate split quadric times an unrestricted w. -/
@[expose] def regularZeroEquiv {F : Type*} [Field F] (κ : F) (hκ : κ=0) :
    {x : Quadric κ // Regular x.1} ≃
      ({z : NormDifference (0:F) // z≠differenceOrigin}×F) where
  toFun x := (⟨⟨(x.1.1.1,x.1.1.2.1),by
    have hh := x.1.2
    simpa only [equation,hκ,zero_mul,sub_zero] using hh⟩,by
      intro he
      exact x.2 (congrArg Subtype.val he)⟩,x.1.1.2.2)
  invFun v := ⟨⟨(v.1.1.1.1,v.1.1.1.2,v.2),by
    simpa only [equation,hκ,zero_mul,sub_zero] using v.1.1.2⟩,by
      intro he
      exact v.1.2 (Subtype.ext he)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Integer-valued formula avoids hiding a truncated natural
subtraction when counting the genuine original smooth residue locus. -/
theorem actual_regular_zero_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F≠2) (h2 : (2:F)≠0) (κ : F) (hκ : κ=0) :
    (Nat.card {x : Quadric κ // Regular x.1}:ℤ)=
      (Fintype.card F:ℤ)^4+(Fintype.card F:ℤ)^3-(Fintype.card F:ℤ)^2-(Fintype.card F:ℤ) := by
  classical
  letI : Inhabited (NormDifference (0:F)) := ⟨differenceOrigin⟩
  have hpos : 1≤Nat.card (NormDifference (0:F)) := by
    have hh : 0<Fintype.card (NormDifference (0:F)) := Fintype.card_pos
    simpa only [Nat.card_eq_fintype_card] using hh
  have hnon : Nat.card {z : NormDifference (0:F) // z≠differenceOrigin}=
      Nat.card (NormDifference (0:F))-1 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl (fun z : NormDifference (0:F) => z=differenceOrigin),
      Fintype.card_subtype_eq,←Nat.card_eq_fintype_card]
  have hFC : Nat.card F=Fintype.card F := Nat.card_eq_fintype_card
  rw [Nat.card_congr (regularZeroEquiv κ hκ),Nat.card_prod,hnon,hFC,Nat.cast_mul,
    Nat.cast_sub hpos,Nat.cast_one]
  rw [difference_count hF h2 (0:F)]
  simp only [if_pos rfl]
  ring

@[expose] def actual_prime_regular_equiv (κ : ℤ) (p : ℕ) [NeZero p] :
    RegularResidues κ p p ≃ {x : Quadric (κ:ZMod p) // Regular x.1} where
  toFun x := ⟨x.1,by
    have hh := x.2
    change Regular (mapCoordinates (Int.castRingHom (ZMod p))
      (ActualOriginalModularLift318.digits p x.1.1)) at hh
    rw [ActualOriginalModularLift318.digits_reduce] at hh
    exact hh⟩
  invFun x := ⟨x.1,by
    change Regular (mapCoordinates (Int.castRingHom (ZMod p))
      (ActualOriginalModularLift318.digits p x.1.1))
    rw [ActualOriginalModularLift318.digits_reduce]
    exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem actual_bad_regular_prime_count (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : (p:ℤ)∣κ) :
    (Nat.card (RegularResidues κ p p):ℤ)=(p:ℤ)^4+p^3-p^2-p := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_congr (actual_prime_regular_equiv κ p)]
  have hF : ringChar (ZMod p)≠2 := by simpa only [ringChar_zmod_n] using hp2
  have hk : (κ:ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mpr hκ
  simpa only [ZMod.card] using actual_regular_zero_card hF
    (GoodReductionResidue318.two_residue_ne p hp2) (κ:ZMod p) hk

/-- The actual primitive count above every exponent1 now has its
fully constructed numerical coefficient at an odd valuation-one prime. -/
theorem actual_valuation_one_primitive_count (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : (p:ℤ)∣κ) (hκ2 : ¬(p:ℤ)^2∣κ) (e : ℕ) :
    (Nat.card (ActualPrimitivePrimePower318.PrimitiveResidues κ (p^(e+2)) p):ℤ)=
      ((p:ℤ)^4+p^3-p^2-p)*((p:ℤ)^4)^(e+1) := by
  rw [actual_bad_primitive_count_from_base κ p hp hp2 hκ hκ2 e,Nat.cast_mul,
    actual_bad_regular_prime_count κ p hp hp2 hκ,Nat.cast_pow,Nat.cast_pow]

end ActualOddBadBaseCount318
