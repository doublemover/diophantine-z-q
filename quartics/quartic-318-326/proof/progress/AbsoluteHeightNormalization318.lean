module
public import ActualQuadraticEmbeddings318
public section
noncomputable section
open NumberField Height IntermediateField ConcreteG8Domain ActualQuadraticEmbeddings318
namespace AbsoluteHeightNormalization318
set_option maxHeartbeats 0

lemma absMulHeight_of_adjoin_top {F : Type*} [Field F] [NumberField F] (x : F)
    (hx : ℚ⟮x⟯=⊤) :
    NumberField.absMulHeight₁ x=(Height.mulHeight₁ x)^(Module.finrank ℚ F:ℝ)⁻¹ := by
  have hint : IsIntegral ℚ x := IsIntegral.of_finite ℚ x
  let : FiniteDimensional ℚ ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hint
  let : NumberField ℚ⟮x⟯ := {}
  let e : ℚ⟮x⟯ ≃ₐ[ℚ] F := (IntermediateField.equivOfEq hx).trans IntermediateField.topEquiv
  have he : e.toRingEquiv (IntermediateField.AdjoinSimple.gen ℚ x)=x := rfl
  have hd : Module.finrank ℚ ℚ⟮x⟯=Module.finrank ℚ F := e.toLinearEquiv.finrank_eq
  rw [NumberField.absMulHeight₁,dite_eq_left hint]
  change (Height.mulHeight₁ (IntermediateField.AdjoinSimple.gen ℚ x))^
    (Module.finrank ℚ ℚ⟮x⟯:ℝ)⁻¹ = _
  rw [←RelativeHeightEquiv.mulHeight_equiv e.toRingEquiv,he,hd]

lemma adjoin_pair_eq_top (u v : ℚ) (hv : v≠0) : ℚ⟮pair u v⟯=⊤ := by
  let S : IntermediateField ℚ K := ℚ⟮pair u v⟯
  have hr (q:ℚ) : (q:K)∈S := S.algebraMap_mem q
  have hx : pair u v∈S := IntermediateField.mem_adjoin_simple_self ℚ _
  have he : (pair u v-(u:K))/(v:K)=i := by
    rw [pair_decomposition,add_sub_cancel_left,mul_div_cancel_left₀]
    exact_mod_cast hv
  have hi : i∈S := he ▸ S.div_mem (S.sub_mem hx (hr u)) (hr v)
  apply top_unique
  intro x _
  rcases x with ⟨a,b⟩
  change pair a b∈S
  rw [pair_decomposition]
  exact S.add_mem (hr a) (S.mul_mem (hr b) hi)

lemma absLogHeight_pair [NumberField K] (u v : ℚ) (hv : v≠0) :
    NumberField.absLogHeight₁ (pair u v)=Real.log (Height.mulHeight₁ (pair u v))/2 := by
  rw [NumberField.absLogHeight₁,absMulHeight_of_adjoin_top _ (adjoin_pair_eq_top u v hv),
    ConcreteG8Domain.dimension,Real.log_rpow (Height.mulHeight₁_pos _)]
  norm_num
  ring

lemma exp_twice_absLogHeight_pair [NumberField K] (u v : ℚ) (hv : v≠0) :
    Real.exp (2*NumberField.absLogHeight₁ (pair u v))=Height.mulHeight₁ (pair u v) := by
  rw [absLogHeight_pair u v hv]
  have he : 2*(Real.log (Height.mulHeight₁ (pair u v))/2)=Real.log (Height.mulHeight₁ (pair u v)) := by ring
  rw [he,Real.exp_log (Height.mulHeight₁_pos _)]

/-- Absolute normalization for every actual field element, including rationals. -/
lemma absLogHeight_eq_half_relative [NumberField K] (x : K) :
    NumberField.absLogHeight₁ x=Real.log (Height.mulHeight₁ x)/2 := by
  rcases x with ⟨u,v⟩
  change NumberField.absLogHeight₁ (pair u v)=Real.log (Height.mulHeight₁ (pair u v))/2
  by_cases hv : v=0
  · subst v
    rw [RationalPointBox318.pair_zero_ratCast,RationalAbsoluteHeight.absLogHeight_ratCast,
      RationalAbsoluteHeight.mulHeight_ratCast,ConcreteG8Domain.dimension]
    rw [Real.log_pow]
    ring
  · exact absLogHeight_pair u v hv

#print axioms absLogHeight_eq_half_relative
#print axioms absMulHeight_of_adjoin_top
#print axioms adjoin_pair_eq_top
#print axioms absLogHeight_pair
#print axioms exp_twice_absLogHeight_pair
end AbsoluteHeightNormalization318
