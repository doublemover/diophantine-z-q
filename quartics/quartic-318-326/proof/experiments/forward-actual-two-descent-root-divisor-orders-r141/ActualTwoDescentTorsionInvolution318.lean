module
public import ActualTwoDescentTorsionTranslation318
public section
noncomputable section
namespace ActualTwoDescentTorsionInvolution318
open ActualTwoDescentTorsionTranslation318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]

lemma translatedX_twice (n x : K) (hn : n ≠ 0) (hA : x+3*n ≠ 0) :
    translatedX n (translatedX n x)=x := by
  rw [translatedX,translated_first n x hA,translated_second n x hA]
  field_simp [hn,hA]
  <;> ring

lemma translatedY_twice (n x y : K) (hn : n ≠ 0) (hA : x+3*n ≠ 0) :
    translatedY n (translatedX n x) (translatedY n x y)=y := by
  rw [translatedY,translated_first n x hA]
  dsimp [translatedY]
  field_simp [hn,hA]
  <;> ring

end ActualTwoDescentTorsionInvolution318
