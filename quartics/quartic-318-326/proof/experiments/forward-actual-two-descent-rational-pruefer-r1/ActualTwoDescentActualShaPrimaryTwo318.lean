module
public import ActualTwoDescentActualShaPrimary318
public section
noncomputable section
namespace ActualTwoDescentActualShaPrimaryTwo318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaDefinition318 ActualTwoDescentActualShaPrimary318
open ActualTwoDescentPrimaryPowerLevels318

def primaryShaTwoHom (n : ℚ) (hn : n ≠ 0) : powerLevel (actualShaPrimary n hn) 1 →* actualShaTwo n hn where
  toFun x := ⟨primaryShaInclusion n hn x, x.val.val.toAdd.property,by
    have h := congrArg (primaryShaInclusion n hn) x.property
    simpa only [map_pow,map_one,pow_one] using h⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)

lemma actual_primary_sha_two_injective (n : ℚ) (hn : n ≠ 0) : Function.Injective (primaryShaTwoHom n hn) := by
  intro x y h
  apply Subtype.ext
  exact actual_primary_sha_inclusion_injective n hn (congrArg Subtype.val h)

lemma actual_primary_sha_two_surjective (n : ℚ) (hn : n ≠ 0) : Function.Surjective (primaryShaTwoHom n hn) := by
  intro x
  let g : Multiplicative (actualSha n hn) := Multiplicative.ofAdd ⟨x.val.toAdd,x.property.1⟩
  have hg : g^2=1 := actual_full_sha_inclusion_injective n hn (by
    rw [map_pow,map_one]
    exact x.property.2)
  let y : actualShaPrimary n hn := ⟨g,⟨1,by simpa only [pow_one] using hg⟩⟩
  have hy : y ∈ powerLevel (actualShaPrimary n hn) 1 := by
    apply Subtype.ext
    simpa only [pow_one] using hg
  exact ⟨⟨y,hy⟩,Subtype.ext rfl⟩

def primaryShaTwoEquiv (n : ℚ) (hn : n ≠ 0) : powerLevel (actualShaPrimary n hn) 1 ≃* actualShaTwo n hn :=
  MulEquiv.ofBijective (primaryShaTwoHom n hn) ⟨actual_primary_sha_two_injective n hn,actual_primary_sha_two_surjective n hn⟩

end ActualTwoDescentActualShaPrimaryTwo318
