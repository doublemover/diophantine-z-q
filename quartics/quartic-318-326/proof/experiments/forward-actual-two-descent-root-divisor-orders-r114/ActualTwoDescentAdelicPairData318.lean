module
public import ActualTwoDescentRealRootPositive318
public section
noncomputable section
namespace ActualTwoDescentAdelicPairData318
set_option maxHeartbeats 16000000

open ActualTwoDescentGoodPrimeValuations318 ActualTwoDescentTorsionSquarePairs318
open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentSquareClassFieldMap318
open ActualTwoDescentAllPlacesIntersection318 ActualTwoDescentLocalCosetNonexceptional318
open ActualTwoDescentLiteralKummerClasses318 ActualTwoDescentRealRootPositive318

/-- Concrete nonexceptional local representatives of ONE rational squareclass pair.
There is no rational elliptic point in this data. -/
structure AdelicPair (n : ℕ) (A B : ℚ) : Prop where
  first_ne : A ≠ 0
  second_ne : B ≠ 0
  first_pos : 0 < A
  finite_places : ∀ (p : ℕ) [Fact p.Prime], ∃ P : LocalPoint (p:=p) n,
    SquarePair (P.x+3*n) (P.x-n) (A : ℚ_[p]) (B : ℚ_[p])

lemma actual_squarepair_map_value {K : Type*} [Field K] [CharZero K]
    (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) :
    squarePairMap (algebraMap ℚ K) (classOf A hA,classOf B hB)=
      (classOf (algebraMap ℚ K A) (field_map_ne_zero _ hA),
       classOf (algebraMap ℚ K B) (field_map_ne_zero _ hB)) := by
  apply Prod.ext <;> exact actual_squareclass_map_value _ _ _

/-- Actual all-place image membership supplies the full concrete local data,
including a nonexceptional representative at each finite place. -/
theorem actual_adelic_pair_of_all_places (n : ℕ) (hn : n ≠ 0) (A B : ℚ)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (H : (classOf A hA,classOf B hB) ∈ allPlacesImage (n : ℚ) (Nat.cast_ne_zero.mpr hn)) :
    AdelicPair n A B := by
  have Hplaces := (actual_all_places_iff _ _ _).mp H
  have hR : ∃ P : Point (n : ℝ), kummerClass (n : ℝ) (Nat.cast_ne_zero.mpr hn) P=
      (classOf (A : ℝ) (Rat.cast_ne_zero.mpr hA),classOf (B : ℝ) (Rat.cast_ne_zero.mpr hB)) := by
    simpa only [map_natCast,actual_squarepair_map_value] using Hplaces.1
  obtain ⟨PR,hPR⟩ := hR
  have hpos : 0 < (A : ℝ) := actual_real_first_class_positive (n : ℝ) (A : ℝ) (B : ℝ)
    (by exact_mod_cast Nat.pos_of_ne_zero hn) (Rat.cast_ne_zero.mpr hA) (Rat.cast_ne_zero.mpr hB) PR hPR
  refine ⟨hA,hB,by exact_mod_cast hpos,?_⟩
  intro p hp
  letI : DecidableEq (ℚ_[p]) := Classical.decEq _
  have hP : ∃ P : Point (n : ℚ_[p]), kummerClass (n : ℚ_[p]) (Nat.cast_ne_zero.mpr hn) P=
      (classOf (A : ℚ_[p]) (Rat.cast_ne_zero.mpr hA),classOf (B : ℚ_[p]) (Rat.cast_ne_zero.mpr hB)) := by
    simpa only [map_natCast,actual_squarepair_map_value] using Hplaces.2 p
  obtain ⟨P,hP⟩ := hP
  obtain ⟨Q,hQ⟩ := actual_local_coset_nonexceptional (p:=p) n hn P
  refine ⟨Q,?_⟩
  apply (actual_kummer_pair_iff (n : ℚ_[p]) Q.x Q.y (A : ℚ_[p]) (B : ℚ_[p])
    (Nat.cast_ne_zero.mpr hn) _ Q.plus_ne Q.minus_ne (Rat.cast_ne_zero.mpr hA) (Rat.cast_ne_zero.mpr hB)).mp
  exact hQ.trans hP

end ActualTwoDescentAdelicPairData318
