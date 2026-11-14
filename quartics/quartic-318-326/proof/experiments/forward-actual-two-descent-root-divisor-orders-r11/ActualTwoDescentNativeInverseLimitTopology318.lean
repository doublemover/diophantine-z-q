module
public import ActualTwoDescentNativeCompatibleCharacters318
public section
noncomputable section
namespace ActualTwoDescentNativeInverseLimitTopology318
open ActualTwoDescentDiscreteSelmerDual318 ActualTwoDescentNativeLevelRestriction318
open ActualTwoDescentNativeCompatibleCharacters318

/-- The literal compatible-family subgroup inside the product of the actual
native level duals. Its topology is the inherited PRODUCT topology. -/
def nativeCompatibleSubgroup (n : ℚ) (hn : n ≠ 0) :
    Subgroup (∀ k, NativeLevelDual n hn k) where
  carrier := NativeCompatible n hn
  one_mem' := by
    intro i j hij
    exact map_one (nativeLevelDualTransition n hn i j hij)
  mul_mem' := by
    intro F G hF hG i j hij
    change nativeLevelDualTransition n hn i j hij (F j * G j)=F i * G i
    rw [map_mul,hF i j hij,hG i j hij]
  inv_mem' := by
    intro F hF i j hij
    change nativeLevelDualTransition n hn i j hij (F j)⁻¹=(F i)⁻¹
    rw [map_inv,hF i j hij]

def nativeInverseLimitMap (n : ℚ) (hn : n ≠ 0) :
    ActualPontryagin n hn →* nativeCompatibleSubgroup n hn where
  toFun f := ⟨fun k => nativeLevelRestriction n hn k f,
    fun i j hij => actual_native_restriction_compatible n hn i j hij f⟩
  map_one' := by apply Subtype.ext; funext k; exact map_one (nativeLevelRestriction n hn k)
  map_mul' f g := by apply Subtype.ext; funext k; exact map_mul (nativeLevelRestriction n hn k) f g

lemma actual_native_inverse_limit_continuous (n : ℚ) (hn : n ≠ 0) :
    Continuous (nativeInverseLimitMap n hn) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun k => (nativeLevelRestriction n hn k).continuous)

lemma actual_native_inverse_limit_bijective (n : ℚ) (hn : n ≠ 0) :
    Function.Bijective (nativeInverseLimitMap n hn) := by
  constructor
  · intro f g h
    apply actual_native_restrictions_injective n hn f g
    intro k
    exact congrArg (fun F : nativeCompatibleSubgroup n hn => F.val k) h
  · intro F
    refine ⟨nativeCharacterOfFamily n hn F.val F.property,?_⟩
    apply Subtype.ext
    funext k
    exact actual_native_family_restriction n hn F.val F.property k

def nativeInverseLimitEquiv (n : ℚ) (hn : n ≠ 0) :
    ActualPontryagin n hn ≃* nativeCompatibleSubgroup n hn :=
  MulEquiv.ofBijective (nativeInverseLimitMap n hn) (actual_native_inverse_limit_bijective n hn)

/-- Compactness of the ACTUAL native dual, not a transported topology,
and Hausdorffness of the literal product prove inverse continuity. -/
def nativeInverseLimitHomeomorph (n : ℚ) (hn : n ≠ 0) :
    ActualPontryagin n hn ≃ₜ nativeCompatibleSubgroup n hn :=
  (nativeInverseLimitEquiv n hn).toEquiv.toHomeomorphOfContinuousClosed
    (actual_native_inverse_limit_continuous n hn)
    (actual_native_inverse_limit_continuous n hn).isClosedMap

lemma actual_native_inverse_limit_coordinate (n : ℚ) (hn : n ≠ 0)
    (f : ActualPontryagin n hn) (k : ℕ) :
    (nativeInverseLimitHomeomorph n hn f).val k=nativeLevelRestriction n hn k f := rfl

end ActualTwoDescentNativeInverseLimitTopology318
