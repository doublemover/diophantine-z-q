module
public import ActualTwoDescentLocalUnitData318
public section
noncomputable section
namespace ActualTwoDescentLiteralUnitData318
open ActualTwoDescentLocalUnitData318 ActualTwoDescentSignReciprocity318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentStrippedSymbols318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentThreeSymbol318
open ActualTwoDescentCoordinateSymbols318 ActualTwoDescentTorsionComparison318
open ActualTwoDescentZeroSumCompletion318
open ActualTwoDescentSymbolTable318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actual_nat_int_coprime (a p : ℕ) (h : Nat.Coprime a p) :
    IsCoprime (a : ℤ) (p : ℤ) := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  simpa only [Int.gcd_natCast_natCast] using h

/-- The literal prime monomial has its proved valuation bit and its
ACTUAL stripped-unit symbol as local squareclass invariants. -/
theorem actual_monomial_unit_data (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (u : ι → ZMod 2) (i : ι) :
    UnitData (p:=p i) (monomial p u) (u i) ((edges p *ᵥ u) i) := by
  refine ⟨stripped p u i,actual_nat_int_coprime _ _ (actual_stripped_coprime p hd u i),
    actual_stripped_symbol p hd u i,1,one_ne_zero,?_⟩
  norm_num only [one_pow,mul_one,Int.cast_natCast]
  exact_mod_cast actual_stripped_factor p u i

lemma actual_three_unit_data (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) :
    UnitData (p:=p) 3 0 (symbolBit 3 p) := by
  have hc : Nat.Coprime 3 p :=
    (Nat.coprime_primes (by decide : Nat.Prime 3) Fact.out).mpr hp3.symm
  refine ⟨3,actual_nat_int_coprime 3 p hc,?_,1,one_ne_zero,?_⟩
  · exact (actual_sign_symbol 3 p hc).symm
  · norm_num

lemma actual_minus_unit_data (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    UnitData (p:=p) (-1) 0 ((p/2 : ℕ) : ZMod 2) := by
  refine ⟨-1,(isCoprime_one_left : IsCoprime (1 : ℤ) p).neg_left,?_,1,one_ne_zero,?_⟩
  · have hodd : p%2=1 := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).mpr hp2
    rw [←legendreSym.to_jacobiSym,legendreSym.at_neg_one hp2,
      χ₄_eq_neg_one_pow hodd,sign_natCast]
  · norm_num

lemma actual_first_unit_data (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp3 : ∀ i, p i ≠ 3)
    (δ : ZMod 2) (u : ι → ZMod 2) (i : ι) :
    UnitData (p:=p i) (firstRepresentative p δ u) (u i)
      (δ*lambda p i+(edges p *ᵥ u) i) := by
  have h3 : UnitData (p:=p i) ((3 : ℚ_[p i])^δ.val) 0 (δ*lambda p i) := by
    fin_cases δ
    · simpa using (actual_unit_data_one (p:=p i))
    · simpa [lambda] using actual_three_unit_data (p i) (hp3 i)
  have h := actual_unit_data_mul _ _ _ _ _ _ h3 (actual_monomial_unit_data p hd u i)
  simpa only [firstRepresentative,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,zero_add] using h

lemma actual_full_product_unit_data (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (i : ι) :
    UnitData (p:=p i) (∏ j, p j : ℕ) 1 (row p i) := by
  have h := actual_monomial_unit_data p hd (ones ι) i
  simpa only [monomial,ones,ZMod.val_one,pow_one,Matrix.mulVec,dotProduct,mul_one,row] using h

end ActualTwoDescentLiteralUnitData318
