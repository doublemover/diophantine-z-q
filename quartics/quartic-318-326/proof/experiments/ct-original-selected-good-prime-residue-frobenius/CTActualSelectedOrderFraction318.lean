module
public import CTActualSelectedImageOrder318
public import Mathlib.RingTheory.Valuation.ValuationRing
import all CTActualSelectedGlobalPrime318
public section
noncomputable section

namespace CTActualSelectedOrderFraction318

open CTActualSelectedPadicLayer318 CTActualSelectedPadicValuation318
open CTActualSelectedGlobalPrime318 CTActualSelectedImageOrder318
open IsLocalRing
open scoped NumberField CTPadicSelectedValuationRing318

variable (p : ℕ) [Fact p.Prime] (M : GlobalLayer)
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (Pbar p) Γ) [(Padic.mulValuation (p := p)).HasExtension w]

local notation "R" => ℤ_[p]
local notation "A" => 𝓞 M.toIntermediateField
local notation "L" => localField p M
local notation "S" => selectedIntegers p M w
local notation "B" => imageOrder p M w
local notation "D" => localOrder p M w

@[expose] def orderToField : D →+* L :=
  (algebraMap S L).comp (localOrderToSelected p M w).toRingHom

scoped instance orderFieldAlgebra : Algebra D L :=
  (orderToField p M w).toAlgebra

theorem orderToField_injective : Function.Injective (orderToField p M w) :=
  (ValuationSubring.subtype_injective S).comp (localOrderToSelected_injective p M w)

/-- The actual field map from the fraction field of the selected image
order, fixing the original order. -/
@[expose] def fractionToField : FractionRing D →+* L :=
  IsFractionRing.lift (orderToField_injective p M w)

@[simp] theorem fractionToField_on_order (x : D) :
    fractionToField p M w (algebraMap D (FractionRing D) x) = orderToField p M w x :=
  IsFractionRing.lift_algebraMap (orderToField_injective p M w) x

/-- Both required sets of generators are present without an adic
completion comparison. Taking fractions recovers Q_p and j(M). -/
theorem fractionToField_surjective :
    Function.Surjective (fractionToField p M w) := by
  let f := fractionToField p M w
  let K := f.fieldRange
  have hD (x : D) : orderToField p M w x ∈ K :=
    ⟨algebraMap D (FractionRing D) x,fractionToField_on_order p M w x⟩
  have hb (r : R) : algebraMap R L r ∈ K := by
    have hr := hD (algebraMap R D r)
    have he : orderToField p M w (algebraMap R D r) = algebraMap R L r := by
      change algebraMap S L (localOrderToSelected p M w (algebraMap R D r)) = _
      rw [(localOrderToSelected p M w).commutes,← IsScalarTower.algebraMap_apply R S L]
    rw [he] at hr
    exact hr
  have hOld (a : A) : layerEmbedding p M (algebraMap A M.toIntermediateField a) ∈ K := by
    have hr := hD (algebraMap B D (oldToOrder p M w a))
    have he : orderToField p M w (algebraMap B D (oldToOrder p M w a)) =
        layerEmbedding p M (algebraMap A M.toIntermediateField a) := by
      change (algebraMap S L)
        (localOrderToSelected p M w (algebraMap B D (oldToOrder p M w a))) = _
      rw [localOrderToSelected_on_order,oldToOrder_val] <;> rfl
    rw [he] at hr
    exact hr
  have hbase (x : ℚ_[p]) : algebraMap ℚ_[p] L x ∈ K := by
    obtain ⟨u,v,_,rfl⟩ := IsFractionRing.div_surjective R x
    rw [map_div₀,← IsScalarTower.algebraMap_apply R ℚ_[p] L,
      ← IsScalarTower.algebraMap_apply R ℚ_[p] L]
    exact div_mem (hb u) (hb v)
  have hold (x : M.toIntermediateField) : layerEmbedding p M x ∈ K := by
    obtain ⟨u,v,_,rfl⟩ := IsFractionRing.div_surjective A x
    rw [map_div₀]
    exact div_mem (hOld u) (hOld v)
  let F := K.toIntermediateField hbase
  have hL : L ≤ F.map (localField p M).val := by
    apply IntermediateField.adjoin_le_iff.2
    rintro _ ⟨x,hx,rfl⟩
    let y : M.toIntermediateField := ⟨x,hx⟩
    exact IntermediateField.mem_map.2 ⟨layerEmbedding p M y,hold y,rfl⟩
  intro x
  obtain ⟨y,hy,he⟩ := IntermediateField.mem_map.1 (hL x.property)
  have hxy : y = x := (localField p M).val.injective he
  rw [hxy] at hy
  exact hy

theorem field_isFractionRing_of_order : IsFractionRing D L := by
  let g : D →ₐ[D] L := Algebra.ofId D L
  have hg : Function.Injective g := orderToField_injective p M w
  let f : FractionRing D →ₐ[D] L := IsFractionRing.liftAlgHom hg
  have hf : Function.Surjective f := by
    change Function.Surjective (IsFractionRing.lift hg : FractionRing D →+* L)
    exact fractionToField_surjective p M w
  exact IsFractionRing.of_algEquiv (AlgEquiv.ofBijective f ⟨f.injective,hf⟩)

/-- Because D and the selected valuation ring use the same fraction
field, D embeds onto S. In the inverse branch the old local map
reflects the unit detected in S. The p-nonunit rules out a field
via the preceding concrete DVR proof. -/
theorem localOrderToSelected_surjective
    (hD : ¬(p : ℤ) ∣ NumberField.discr M.toIntermediateField) :
    Function.Surjective (localOrderToSelected p M w) := by
  letI : IsFractionRing D L := field_isFractionRing_of_order p M w
  letI : IsDiscreteValuationRing D := localOrder_dvr p M w hD
  let f := localOrderToSelected p M w
  letI : IsLocalHom f.toRingHom := localOrderToSelected_isLocal p M w
  intro x
  rcases (ValuationRing.integers D L).eq_algebraMap_or_inv_eq_algebraMap (x : L) with
    ⟨y,hy | hy⟩
  · exact ⟨y,Subtype.ext hy.symm⟩
  · by_cases hx : (x : L) = 0
    · refine ⟨0,Subtype.ext ?_⟩
      simpa only [map_zero,ZeroMemClass.coe_zero] using hx.symm
    · have hmul : f y * x = 1 := by
        apply Subtype.ext
        change algebraMap D L y * (x : L) = 1
        rw [← hy,inv_mul_cancel₀ hx]
      let u : Sˣ := ⟨f y,x,hmul,by rw [mul_comm,hmul]⟩
      obtain ⟨a,ha⟩ : IsUnit y :=
        isUnit_of_map_unit f.toRingHom y ⟨u,rfl⟩
      let a' := Units.map f.toRingHom.toMonoidHom a
      have hm : (a' : S) * x = 1 := by
        change f (a : D) * x = 1
        rw [ha]
        exact hmul
      refine ⟨(↑(a⁻¹) : D),?_⟩
      change (↑(a'⁻¹) : S) = x
      calc
        (↑(a'⁻¹) : S) = ↑(a'⁻¹) * ((a' : S) * x) := by rw [hm,mul_one]
        _ = x := by simp [← mul_assoc]

/-- Exact good-prime equality on the previously chosen literal
valuation ring, with no independent place or maximal-ideal premise. -/
theorem actual_maximalIdeal_map
    (hD : ¬(p : ℤ) ∣ NumberField.discr M.toIntermediateField) :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
  let f := localOrderToSelected p M w
  have hc : f.toRingHom.comp (algebraMap R D) = algebraMap R S :=
    f.comp_algebraMap
  calc
    _ = ((maximalIdeal R).map (algebraMap R D)).map f.toRingHom := by rw [Ideal.map_map,hc]
    _ = (maximalIdeal D).map f.toRingHom := by rw [localOrder_maximalIdeal p M w hD]
    _ = maximalIdeal S :=
      IsLocalRing.map_maximalIdeal_of_surjective f.toRingHom
        (localOrderToSelected_surjective p M w hD)

end CTActualSelectedOrderFraction318
