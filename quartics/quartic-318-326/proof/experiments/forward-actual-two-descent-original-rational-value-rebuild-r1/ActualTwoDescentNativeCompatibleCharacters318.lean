module
public import ActualTwoDescentNativeScalarResidues318
public section
noncomputable section
namespace ActualTwoDescentNativeCompatibleCharacters318
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentSelmerPadicAction318
open ActualTwoDescentPrimaryPadicScalar318 ActualTwoDescentDiscreteSelmerDual318
open ActualTwoDescentNativeLevelRestriction318 ActualTwoDescentHigherCohomologyDirectedMaps318

/-- Every transition, not merely neighboring or selected levels, is fixed
by the original subgroup inclusions. -/
def NativeCompatible (n : ℚ) (hn : n ≠ 0) (F : ∀ k, NativeLevelDual n hn k) : Prop :=
  ∀ i j (hij : i ≤ j), nativeLevelDualTransition n hn i j hij (F j)=F i

def nativeFamilyValue (n : ℚ) (hn : n ≠ 0) (F : ∀ k, NativeLevelDual n hn k)
    (x : actualPrimarySelmer n hn) : Circle :=
  F (primaryExponent (actual_selmer_primary n hn) x)
    (Multiplicative.ofAdd ⟨x,actual_primary_exponent (actual_selmer_primary n hn) x⟩)

/-- Reconstruction is independent of the selected annihilating exponent.
The proof uses the common maximum and both ORIGINAL transition maps. -/
lemma actual_native_family_at_level (n : ℚ) (hn : n ≠ 0)
    (F : ∀ k, NativeLevelDual n hn k) (hF : NativeCompatible n hn F)
    (k : ℕ) (x : actualPrimarySelmer n hn) (hx : (2^k) • x=0) :
    nativeFamilyValue n hn F x=F k (Multiplicative.ofAdd ⟨x,hx⟩) := by
  let i := primaryExponent (actual_selmer_primary n hn) x
  have hi : (2^i) • x=0 := actual_primary_exponent (actual_selmer_primary n hn) x
  let j := max i k
  have h₁ := congrArg (fun f : NativeLevelDual n hn i =>
    f (Multiplicative.ofAdd ⟨x,hi⟩)) (hF i j (le_max_left _ _))
  have h₂ := congrArg (fun f : NativeLevelDual n hn k =>
    f (Multiplicative.ofAdd ⟨x,hx⟩)) (hF k j (le_max_right _ _))
  exact h₁.symm.trans h₂

lemma actual_native_family_zero (n : ℚ) (hn : n ≠ 0)
    (F : ∀ k, NativeLevelDual n hn k) (hF : NativeCompatible n hn F) :
    nativeFamilyValue n hn F 0=1 := by
  rw [actual_native_family_at_level n hn F hF 0 0 (by simp)]
  exact map_one (F 0)

lemma actual_native_family_add (n : ℚ) (hn : n ≠ 0)
    (F : ∀ k, NativeLevelDual n hn k) (hF : NativeCompatible n hn F)
    (x y : actualPrimarySelmer n hn) :
    nativeFamilyValue n hn F (x+y)=nativeFamilyValue n hn F x * nativeFamilyValue n hn F y := by
  obtain ⟨i,hi⟩ := actual_selmer_primary n hn x
  obtain ⟨j,hj⟩ := actual_selmer_primary n hn y
  let k := max i j
  have hx : (2^k) • x=0 := actual_nsmul_power_mono (le_max_left _ _) hi
  have hy : (2^k) • y=0 := actual_nsmul_power_mono (le_max_right _ _) hj
  have hxy : (2^k) • (x+y)=0 := by rw [nsmul_add,hx,hy,zero_add]
  rw [actual_native_family_at_level n hn F hF k (x+y) hxy,
    actual_native_family_at_level n hn F hF k x hx,
    actual_native_family_at_level n hn F hF k y hy]
  exact map_mul (F k) (Multiplicative.ofAdd ⟨x,hx⟩) (Multiplicative.ofAdd ⟨y,hy⟩)

/-- A coherent family produces an actual complex-Circle valued continuous
character of the ORIGINAL discrete Selmer group. -/
def nativeCharacterOfFamily (n : ℚ) (hn : n ≠ 0)
    (F : ∀ k, NativeLevelDual n hn k) (hF : NativeCompatible n hn F) :
    ActualPontryagin n hn where
  toFun x := nativeFamilyValue n hn F x.toAdd
  map_one' := actual_native_family_zero n hn F hF
  map_mul' x y := actual_native_family_add n hn F hF x.toAdd y.toAdd
  continuous_toFun := continuous_of_discreteTopology

lemma actual_native_family_restriction (n : ℚ) (hn : n ≠ 0)
    (F : ∀ k, NativeLevelDual n hn k) (hF : NativeCompatible n hn F) (k : ℕ) :
    nativeLevelRestriction n hn k (nativeCharacterOfFamily n hn F hF)=F k := by
  apply PontryaginDual.ext
  intro x
  exact actual_native_family_at_level n hn F hF k x.toAdd.val x.toAdd.property

/-- Exact inverse-limit set-level universal property for native characters.
No global pairing, rank selection or finite cardinal premise is used. -/
theorem actual_native_compatible_unique (n : ℚ) (hn : n ≠ 0)
    (F : ∀ k, NativeLevelDual n hn k) (hF : NativeCompatible n hn F) :
    ∃! f : ActualPontryagin n hn, ∀ k, nativeLevelRestriction n hn k f=F k := by
  refine ⟨nativeCharacterOfFamily n hn F hF,actual_native_family_restriction n hn F hF,?_⟩
  intro f hf
  apply actual_native_restrictions_injective n hn
  intro k
  exact (hf k).trans (actual_native_family_restriction n hn F hF k).symm

end ActualTwoDescentNativeCompatibleCharacters318
