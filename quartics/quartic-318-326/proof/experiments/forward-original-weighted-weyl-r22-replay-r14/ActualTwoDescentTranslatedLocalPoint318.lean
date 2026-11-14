module
public import ActualTwoDescentTranslatedSquarePair318
public section
noncomputable section
namespace ActualTwoDescentTranslatedLocalPoint318
open ActualTwoDescentTorsionTranslation318 ActualTwoDescentTorsionInvolution318
open ActualTwoDescentGoodPrimeValuations318
set_option maxHeartbeats 16000000
variable {q : ℕ} [Fact q.Prime]

/-- The actual local-point translation, at arbitrary primes including2/3. -/
def translateLocal (n : ℕ) (hn : n ≠ 0) (P : LocalPoint (p:=q) n) : LocalPoint (p:=q) n where
  x := translatedX n P.x
  y := translatedY n P.x P.y
  x_ne := (translated_nonzero n P.x (Nat.cast_ne_zero.mpr hn) P.x_ne P.minus_ne P.plus_ne).1
  minus_ne := (translated_nonzero n P.x (Nat.cast_ne_zero.mpr hn) P.x_ne P.minus_ne P.plus_ne).2.1
  plus_ne := (translated_nonzero n P.x (Nat.cast_ne_zero.mpr hn) P.x_ne P.minus_ne P.plus_ne).2.2
  curve := translated_curve n P.x P.y P.plus_ne P.curve

lemma translateLocal_x_twice (n : ℕ) (hn : n ≠ 0) (P : LocalPoint (p:=q) n) :
    (translateLocal n hn (translateLocal n hn P)).x=P.x :=
  translatedX_twice n P.x (Nat.cast_ne_zero.mpr hn) P.plus_ne

lemma translateLocal_y_twice (n : ℕ) (hn : n ≠ 0) (P : LocalPoint (p:=q) n) :
    (translateLocal n hn (translateLocal n hn P)).y=P.y :=
  translatedY_twice n P.x P.y (Nat.cast_ne_zero.mpr hn) P.plus_ne

end ActualTwoDescentTranslatedLocalPoint318
