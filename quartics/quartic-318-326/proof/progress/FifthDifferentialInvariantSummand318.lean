module
public import FifthDifferentialProjection318
public section
noncomputable section
namespace FifthDifferentialInvariantSummand318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthCompletedGlobal318 FifthCompletedFunctionField318
open ContactGlobalDifferentialCoefficient318 FifthDifferentialTraceComparison318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
local instance rawCharZero:CharZero Raw:=Algebra.charZero_of_charZero (RatFunc ℚ) Raw
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance originalAlgebra:Algebra Infinity Raw:=(InfinityOpenFractionField318.openEmbedding units).toAlgebra
local instance characterAlgebra:Algebra Order Character:=FifthShortFraction318.embedding.toAlgebra
attribute [local instance] sourceAlgebra targetAlgebra FifthCompletedDegree318.pullbackAlgebra
abbrev G:=Γ(FifthSignRestriction318.M,⊤)
/-- Invariance means equality of actual global canonical pullbacks under
every one of the eight whole-map-fixing source automorphisms. -/
@[expose] def Fixed (s:G):Prop:=∀b∈FifthFixingSigns318.signs,
  ContactDifferentialCharacters318.action b s=s
/-- The actual average lands in actual global invariants, not just in a
fixed coefficient field. -/
theorem average_fixed (s:G):Fixed (FifthDifferentialAveraging318.average s):=by
  intro b hb
  apply ContactGlobalCoefficientScalars318.coefficient_injective
  rw [coefficient_action,FifthDifferentialProjection318.coefficient_average]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp
    ((FifthFixingFieldEnumeration318.sign_mem b).mpr hb) _ (Subtype.mem _)
/-- Conversely a globally invariant section is fixed by normalized averaging. -/
theorem average_eq_of_fixed (s:G) (h:Fixed s):FifthDifferentialAveraging318.average s=s:=by
  apply ContactGlobalCoefficientScalars318.coefficient_injective
  rw [FifthDifferentialAveraging318.average,ContactGlobalCoefficientScalars318.coefficient_smul,
    coefficient_signSum]
  have hs:∀b∈FifthFixingSigns318.signs,
      FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b (coefficient s)=
        coefficient s:=by
    intro b hb
    rw [←coefficient_action,h b hb]
  simp_rw [Finset.sum_congr rfl hs]
  rw [Finset.sum_const,FifthFixingSigns318.cardinality,nsmul_eq_mul]
  simp only [map_div₀,map_one,map_ofNat]
  field_simp
  norm_num
/-- Exact global invariant-summand criterion. It does not identify this
space with sections of the target differential sheaf. -/
theorem average_eq_iff (s:G):FifthDifferentialAveraging318.average s=s ↔ Fixed s:=by
  constructor
  · intro h;rw [←h];exact average_fixed s
  · exact average_eq_of_fixed s
/-- The range of the genuine global averaging operator is exactly the
sections invariant under the actual eight source automorphisms. -/
theorem range_average:Set.range FifthDifferentialAveraging318.average={s:G|Fixed s}:=by
  ext s
  constructor
  · rintro ⟨t,rfl⟩;exact average_fixed t
  · intro h;exact ⟨s,average_eq_of_fixed s h⟩
/-- The invariant additive subgroup is cut out by the actual canonical
pullbacks, rather than by assigning an abstract character decomposition. -/
@[expose] def invariants:AddSubgroup G where
  carrier:={s|Fixed s}
  zero_mem':=by intro b hb;exact map_zero _
  add_mem':=by intro s t hs ht b hb;rw [map_add,hs b hb,ht b hb]
  neg_mem':=by intro s hs b hb;rw [map_neg,hs b hb]
@[expose] def retraction:G→+invariants where
  toFun s:=⟨FifthDifferentialAveraging318.average s,average_fixed s⟩
  map_zero':=by apply Subtype.ext; simp only [FifthDifferentialAveraging318.average,map_zero,smul_zero];rfl
  map_add':=by intro s t;apply Subtype.ext;exact FifthDifferentialAveraging318.average_add s t
/-- Inclusion of the actual invariant subgroup followed by its actual
averaging retraction is the identity. -/
theorem retraction_inclusion (s:invariants):retraction s.val=s:=by
  apply Subtype.ext
  exact average_eq_of_fixed s.val s.property
end FifthDifferentialInvariantSummand318
