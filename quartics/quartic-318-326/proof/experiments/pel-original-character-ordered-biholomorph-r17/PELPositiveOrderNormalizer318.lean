module
public import PELActualOrderNormalizer318
public section
noncomputable section
namespace PELPositiveOrderNormalizer318
open PELQuaternionAlgebra318
set_option maxHeartbeats 1000000

/-- The actual normalizer with positive reduced norm, retaining the real
orientation relevant to the already constructed upper-half-plane family. -/
@[expose] def positiveNormalizer : Subgroup Bˣ where
  carrier := {u | u∈PELActualOrderNormalizer318.normalizer ∧ 0<reducedNorm (u:B)}
  one_mem' := ⟨PELActualOrderNormalizer318.normalizer.one_mem,by norm_num [reducedNorm]⟩
  mul_mem' := by
    intro u v hu hv
    refine ⟨PELActualOrderNormalizer318.normalizer.mul_mem hu.1 hv.1,?_⟩
    change 0<reducedNorm ((u:B)*(v:B))
    rw [PELQuaternionNormParity318.norm_mul]
    exact mul_pos hu.2 hv.2
  inv_mem' := by
    intro u hu
    refine ⟨PELActualOrderNormalizer318.normalizer.inv_mem hu.1,?_⟩
    have h : reducedNorm (u:B)*reducedNorm ((u⁻¹:Bˣ):B)=1 := by
      rw [← PELQuaternionNormParity318.norm_mul]
      change reducedNorm (u.val*u.inv)=1
      rw [u.val_inv]
      norm_num [reducedNorm]
    nlinarith [hu.2]

theorem prime_mem (i : Fin 4) : PELPrimeNormalizerData318.rationalUnit i∈positiveNormalizer := by
  refine ⟨PELActualOrderNormalizer318.prime_mem i,?_⟩
  change 0<reducedNorm (PELPrimeNormalizerData318.element i)
  rw [PELPrimeNormalizerData318.element_norm]
  exact PELPrimeNormalizerData318.prime_positive i

theorem word_mem (v : InertiaLabels318.V) : PELInertiaPrimeWord318.word v∈positiveNormalizer := by
  unfold PELInertiaPrimeWord318.word
  apply positiveNormalizer.mul_mem
  · apply positiveNormalizer.mul_mem
    · apply positiveNormalizer.mul_mem
      · split_ifs <;> first | exact positiveNormalizer.one_mem | exact prime_mem 0
      · split_ifs <;> first | exact positiveNormalizer.one_mem | exact prime_mem 1
    · split_ifs <;> first | exact positiveNormalizer.one_mem | exact prime_mem 2
  · split_ifs <;> first | exact positiveNormalizer.one_mem | exact prime_mem 3

@[expose] def word (v : InertiaLabels318.V) : positiveNormalizer :=
  ⟨PELInertiaPrimeWord318.word v,word_mem v⟩
@[expose] def parity : positiveNormalizer →* Multiplicative InertiaLabels318.V :=
  PELQuaternionNormParity318.parityHom.comp positiveNormalizer.subtype

theorem parity_word (v : InertiaLabels318.V) : parity (word v)=Multiplicative.ofAdd v :=
  PELQuaternionNormParity318.parity_word v

theorem parity_surjective : Function.Surjective parity := by
  intro v
  exact ⟨word (Multiplicative.toAdd v),parity_word _⟩

theorem inertia_mem (i : Fin 5) : PELInertiaNormalizerData318.rationalUnit i∈positiveNormalizer := by
  refine ⟨PELActualOrderNormalizer318.inertia_mem i,?_⟩
  change 0<reducedNorm (PELInertiaNormalizerData318.element i)
  rw [PELInertiaNormalizerData318.element_norm]
  exact PELInertiaNormalizerData318.discriminant_positive i

@[expose] def inertiaElement (i : Fin 5) : positiveNormalizer :=
  ⟨PELInertiaNormalizerData318.rationalUnit i,inertia_mem i⟩

theorem parity_inertia (i : Fin 5) : parity (inertiaElement i)=
    Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) :=
  PELActualOrderNormalizer318.parity_inertia i
end PELPositiveOrderNormalizer318
