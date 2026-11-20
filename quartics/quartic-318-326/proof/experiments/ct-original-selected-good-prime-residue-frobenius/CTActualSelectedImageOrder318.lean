module
public import CTActualSelectedGlobalPrime318
public import CTLocalOrderUnramified318
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.EssentialFiniteness
public section
noncomputable section

namespace CTActualSelectedImageOrder318

open CTActualSelectedPadicLayer318 CTActualSelectedPadicValuation318
open CTActualSelectedGlobalPrime318
open IsLocalRing
open scoped NumberField TensorProduct CTPadicSelectedValuationRing318

variable (p : ℕ) [Fact p.Prime] (M : GlobalLayer)
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (Pbar p) Γ) [(Padic.mulValuation (p := p)).HasExtension w]

local notation "R" => ℤ_[p]
local notation "A" => 𝓞 M.toIntermediateField
local notation "S" => selectedIntegers p M w

/-- Restriction of the actual global embedding to the original integers,
with no new choice of local coefficient embedding. -/
@[expose] def oldToSelected : A →ₐ[ℤ] S where
  __ := integerEmbedding p M w
  commutes' z := map_intCast (integerEmbedding p M w) z

/-- The actual finite tensor image order. It is formed inside the
selected valuation ring, hence also inside the same field L. -/
@[expose] def tensorToSelected : R ⊗[ℤ] A →ₐ[R] S :=
  (AlgHom.liftEquiv ℤ R A S) (oldToSelected p M w)

@[expose] def imageOrder : Subalgebra R S :=
  (tensorToSelected p M w).range

local notation "B" => imageOrder p M w

@[expose] def oldToOrder : A →ₐ[ℤ] B :=
  ((tensorToSelected p M w).rangeRestrict.restrictScalars ℤ).comp
    Algebra.TensorProduct.includeRight

@[simp] theorem oldToOrder_val (x : A) :
    B.val (oldToOrder p M w x) = integerEmbedding p M w x := by
  change tensorToSelected p M w (1 ⊗ₜ[ℤ] x) = oldToSelected p M w x
  rw [tensorToSelected,AlgHom.liftEquiv_tmul,one_smul]

instance finite_imageOrder : Module.Finite R B :=
  Module.Finite.of_surjective (tensorToSelected p M w).rangeRestrict.toLinearMap
    (tensorToSelected p M w).rangeRestrict_surjective

theorem old_generates_imageOrder :
    Algebra.adjoin R (Set.range (oldToOrder p M w)) = (⊤ : Subalgebra R B) := by
  let U := Algebra.adjoin R (Set.range (oldToOrder p M w))
  apply eq_top_iff.2
  intro y _
  obtain ⟨t,rfl⟩ := (tensorToSelected p M w).rangeRestrict_surjective y
  change (tensorToSelected p M w).rangeRestrict t ∈ U
  induction t using TensorProduct.inductionOn with
  | zero => rw [map_zero]; exact U.zero_mem
  | add a b ha hb => rw [map_add]; exact U.add_mem ha hb
  | tmul r a =>
      have h : (tensorToSelected p M w).rangeRestrict (r ⊗ₜ[ℤ] a) =
          algebraMap R B r * oldToOrder p M w a := by
        apply Subtype.ext
        change tensorToSelected p M w (r ⊗ₜ[ℤ] a) =
          algebraMap R S r * B.val (oldToOrder p M w a)
        rw [tensorToSelected,AlgHom.liftEquiv_tmul,Algebra.smul_def,oldToOrder_val] <;> rfl
      rw [h]
      exact U.mul_mem (U.algebraMap_mem r)
        (Algebra.subset_adjoin (Set.mem_range_self a))

@[expose] def imageOrderPrime : Ideal B :=
  (maximalIdeal S).comap B.val

local notation "q" => imageOrderPrime p M w
local notation "P" => selectedGlobalPrime p M w

instance imageOrderPrime_isPrime : q.IsPrime :=
  Ideal.comap_isPrime _ _

abbrev localOrder := Localization.AtPrime q
local notation "D" => localOrder p M w

theorem old_prime_comap : P = q.comap (oldToOrder p M w).toRingHom := by
  ext x
  change integerEmbedding p M w x ∈ maximalIdeal S ↔
    B.val (oldToOrder p M w x) ∈ maximalIdeal S
  rw [oldToOrder_val]

/-- Local map on the same two pulled-back primes. -/
def oldLocalToOrder : Localization.AtPrime P →ₐ[ℤ] D :=
  Localization.localAlgHom P q (oldToOrder p M w) (old_prime_comap p M w)

theorem oldLocalToOrder_on_old (x : A) :
    oldLocalToOrder p M w (algebraMap A (Localization.AtPrime P) x) =
      algebraMap B D (oldToOrder p M w x) := by
  rw [oldLocalToOrder,Localization.localAlgHom_apply,Localization.localRingHom_to_map]

private theorem order_denom_unit (b : q.primeCompl) : IsUnit (B.val b.val) :=
  IsLocalRing.notMem_maximalIdeal.1 b.property

/-- Canonical localized integral image order as subring of the actual
valuation ring; the denominators are units at the chosen place. -/
@[expose] def localOrderToSelected : D →ₐ[R] S :=
  IsLocalization.liftAlgHom (f := B.val) (order_denom_unit p M w)

@[simp] theorem localOrderToSelected_on_order (b : B) :
    localOrderToSelected p M w (algebraMap B D b) = B.val b := by
  exact IsLocalization.lift_eq _ _

theorem localOrderToSelected_injective :
    Function.Injective (localOrderToSelected p M w) := by
  change Function.Injective
    (IsLocalization.lift (S := D) (g := B.val.toRingHom) (order_denom_unit p M w))
  apply (IsLocalization.lift_injective_iff _).2
  intro a b
  exact ⟨fun h => by simpa only [localOrderToSelected_on_order] using
    congrArg (localOrderToSelected p M w) h,
    fun h => congrArg (algebraMap B D) (B.val.injective h)⟩

instance localOrderToSelected_isLocal :
    IsLocalHom (localOrderToSelected p M w).toRingHom := by
  apply ((IsLocalRing.local_hom_TFAE (localOrderToSelected p M w).toRingHom).out 4 1).1
  rw [← Localization.AtPrime.map_eq_maximalIdeal,Ideal.map_le_iff_le_comap,
    Ideal.comap_comap]
  change q ≤ (maximalIdeal S).comap
    ((localOrderToSelected p M w).toRingHom.comp (algebraMap B D))
  have h : (localOrderToSelected p M w).toRingHom.comp (algebraMap B D) = B.val.toRingHom :=
    RingHom.ext (localOrderToSelected_on_order p M w)
  rw [h] <;> exact le_rfl

instance baseToLocalOrder_isLocal : IsLocalHom (algebraMap R D) where
  map_nonunit x hx := by
    apply isUnit_of_map_unit (algebraMap R S)
    rw [← (localOrderToSelected p M w).commutes x]
    exact hx.map (localOrderToSelected p M w).toRingHom

theorem localOrder_formallyUnramified
    (hD : ¬(p : ℤ) ∣ NumberField.discr M.toIntermediateField) :
    Algebra.FormallyUnramified R D := by
  letI := selectedGlobalPrime_unramified p M w hD
  apply CTLocalOrderUnramified318.localized_image_order_formallyUnramified
    P q (oldToOrder p M w).toRingHom (oldLocalToOrder p M w)
    (oldLocalToOrder_on_old p M w) (old_generates_imageOrder p M w)

theorem localOrder_maximalIdeal
    (hD : ¬(p : ℤ) ∣ NumberField.discr M.toIntermediateField) :
    (maximalIdeal R).map (algebraMap R D) = maximalIdeal D := by
  letI := localOrder_formallyUnramified p M w hD
  letI : Algebra.EssFiniteType B D := .of_isLocalization D q.primeCompl
  letI : Algebra.EssFiniteType R D := .comp R B D
  exact Algebra.FormallyUnramified.map_maximalIdeal

theorem localOrder_maximalIdeal_span_p
    (hD : ¬(p : ℤ) ∣ NumberField.discr M.toIntermediateField) :
    maximalIdeal D = Ideal.span ({(p : D)} : Set D) := by
  rw [← localOrder_maximalIdeal p M w hD,PadicInt.maximalIdeal_eq_span_p,
    Ideal.map_span,Set.image_singleton,map_natCast]

/-- Local image order is a DVR with the actual p as uniformizer.
Non-fieldness comes from p in the displayed nonzero maximal ideal. -/
theorem localOrder_dvr
    (hD : ¬(p : ℤ) ∣ NumberField.discr M.toIntermediateField) :
    IsDiscreteValuationRing D := by
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  letI : IsNoetherianRing D := IsLocalization.isNoetherianRing q.primeCompl D inferInstance
  have hm := localOrder_maximalIdeal_span_p p M w hD
  have hn : (p : D) ≠ 0 := by
    intro hz
    have hf : (p : S) = 0 := by
      simpa only [map_natCast,map_zero] using congrArg (localOrderToSelected p M w) hz
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hf
  have hf : ¬IsField D := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq,hm,Ideal.span_singleton_eq_bot]
    exact hn
  apply ((IsDiscreteValuationRing.TFAE D hf).out 5 1).1
  rw [hm]
  exact ⟨(p : D),rfl⟩

end CTActualSelectedImageOrder318
