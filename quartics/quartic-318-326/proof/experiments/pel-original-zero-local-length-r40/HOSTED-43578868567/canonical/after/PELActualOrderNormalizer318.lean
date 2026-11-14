module
public import PELQuaternionNormParity318
public section
noncomputable section
namespace PELActualOrderNormalizer318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
set_option maxHeartbeats 1000000

/-- The actual two-sided normalizer of the original integral order in the
units of the original rational quaternion algebra. -/
@[expose] def normalizer : Subgroup Bˣ where
  carrier := {u | ∀ x : B,x∈order →
    (u:B)*x*((u⁻¹:Bˣ):B)∈order ∧ ((u⁻¹:Bˣ):B)*x*(u:B)∈order}
  one_mem' := by intro x hx; simpa using And.intro hx hx
  mul_mem' := by
    intro u v hu hv x hx
    constructor
    · have h := (hu ((v:B)*x*((v⁻¹:Bˣ):B)) (hv x hx).1).1
      simpa only [mul_inv_rev,Units.val_mul,mul_assoc] using h
    · have h := (hv (((u⁻¹:Bˣ):B)*x*(u:B)) (hu x hx).2).2
      simpa only [mul_inv_rev,Units.val_mul,mul_assoc] using h
  inv_mem' := by
    intro u hu x hx
    simpa only [inv_inv] using And.intro (hu x hx).2 (hu x hx).1

theorem prime_mem (i : Fin 4) : PELPrimeNormalizerData318.rationalUnit i∈normalizer := by
  intro x hx
  exact PELPrimeOrderConjugation318.normalizes_order i x hx

@[expose] def primeElement (i : Fin 4) : normalizer :=
  ⟨PELPrimeNormalizerData318.rationalUnit i,prime_mem i⟩

/-- Every actual prime word used by the original labels belongs to the
whole original-order normalizer, with no local/global normalizer premise. -/
theorem word_mem (v : InertiaLabels318.V) : PELInertiaPrimeWord318.word v∈normalizer := by
  unfold PELInertiaPrimeWord318.word
  apply normalizer.mul_mem
  · apply normalizer.mul_mem
    · apply normalizer.mul_mem
      · split_ifs <;> first | exact normalizer.one_mem | exact prime_mem 0
      · split_ifs <;> first | exact normalizer.one_mem | exact prime_mem 1
    · split_ifs <;> first | exact normalizer.one_mem | exact prime_mem 2
  · split_ifs <;> first | exact normalizer.one_mem | exact prime_mem 3

@[expose] def word (v : InertiaLabels318.V) : normalizer :=
  ⟨PELInertiaPrimeWord318.word v,word_mem v⟩

@[expose] def parity : normalizer →* Multiplicative InertiaLabels318.V :=
  PELQuaternionNormParity318.parityHom.comp normalizer.subtype

theorem parity_word (v : InertiaLabels318.V) : parity (word v)=Multiplicative.ofAdd v :=
  PELQuaternionNormParity318.parity_word v

theorem parity_surjective : Function.Surjective parity := by
  intro v
  exact ⟨word (Multiplicative.toAdd v),parity_word _⟩

/-- Scalar multiples and integral norm-one units are killed by the actual
norm-parity map; equality of this kernel with those elements is NOT asserted. -/
theorem scalar_parity (q : ℚˣ) :
    PELQuaternionNormParity318.parity (PELQuaternionNormParity318.scalarUnit q)=0 :=
  PELQuaternionNormParity318.parity_scalar q
/-- Every actual integral unit normalizes the same order in both directions. -/
theorem integral_mem (u : orderˣ) : PELQuaternionNormParity318.integralUnit u∈normalizer := by
  intro x hx
  change ((u:order):B)*x*((u⁻¹:orderˣ):order)∈order ∧
    (((u⁻¹:orderˣ):order):B)*x*((u:order):B)∈order
  exact ⟨order.mul_mem (order.mul_mem (u:order).property hx) (u⁻¹:orderˣ).val.property,
    order.mul_mem (order.mul_mem (u⁻¹:orderˣ).val.property hx) (u:order).property⟩

theorem inertia_unit_word (i : Fin 5) : PELInertiaNormalizerData318.rationalUnit i=
    PELQuaternionNormParity318.integralUnit (PELInertiaPrimeWord318.connectingUnit i)*
      PELInertiaPrimeWord318.word (InertiaLabels318.fiveLabels i) := by
  apply Units.ext
  exact PELInertiaPrimeWord318.original_label_word i

theorem inertia_mem (i : Fin 5) : PELInertiaNormalizerData318.rationalUnit i∈normalizer := by
  rw [inertia_unit_word]
  exact normalizer.mul_mem (integral_mem _) (word_mem _)

@[expose] def inertiaElement (i : Fin 5) : normalizer :=
  ⟨PELInertiaNormalizerData318.rationalUnit i,inertia_mem i⟩

/-- The original five trace-zero fixed-point representatives, not just the
related prime words, carry the exact original inertia labels. -/
theorem parity_inertia (i : Fin 5) : parity (inertiaElement i)=
    Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) := by
  change PELQuaternionNormParity318.parity (PELInertiaNormalizerData318.rationalUnit i)=
    InertiaLabels318.fiveLabels i
  rw [inertia_unit_word,PELQuaternionNormParity318.parity_mul,
    PELQuaternionNormParity318.parity_norm_one _ (PELInertiaPrimeWord318.connectingUnit_norm i),
    PELQuaternionNormParity318.parity_word,zero_add]

end PELActualOrderNormalizer318
