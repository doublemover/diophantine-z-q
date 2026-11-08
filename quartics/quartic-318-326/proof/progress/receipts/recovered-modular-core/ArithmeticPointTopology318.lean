module
public import ModularCoordinateProper318
public section
noncomputable section
open Filter Set Topology
open scoped Topology
namespace ArithmeticPointTopology318
open OpenJModel318 ThreeArithmeticQuotient318 ModularArithmeticCoordinates318 ModularCoordinateProper318
set_option maxHeartbeats 0

/-- Actual homomorphisms from the literal full diamond-fixed arithmetic algebra. -/
@[ext] structure Points (N : ℕ) [NeZero N] where
  hom : LiteralThreeXComparison318.Fixed N →+* ℂ

@[expose] def jValue (N : ℕ) [NeZero N] (p : Points N) : JOpen := by
  let b := p.hom.comp (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N))
  refine ⟨b (jCoord N),((base_units N).2.2.2.1.map b).ne_zero,?_⟩
  have h := ((base_units N).2.2.2.2.map b).ne_zero
  simpa only [map_sub,map_ofNat,sub_ne_zero] using h

@[expose] def pointCoordinates (N : ℕ) [NeZero N] (p : Points N) : JOpen × ℂ :=
  (jValue N p,p.hom (xGenerator N))

lemma pointCoordinates_injective (N : ℕ) [NeZero N] : Function.Injective (pointCoordinates N) := by
  intro p q h
  apply Points.ext
  apply hom_ext N
  · exact congrArg (fun r : JOpen × ℂ => r.1.val) h
  · exact congrArg Prod.snd h

/-- The literal j,x coordinate topology; no analytification construction is assumed. -/
instance (N : ℕ) [NeZero N] : TopologicalSpace (Points N) :=
  TopologicalSpace.induced (pointCoordinates N) inferInstance

lemma pointCoordinates_embedding (N : ℕ) [NeZero N] : IsEmbedding (pointCoordinates N) :=
  (pointCoordinates_injective N).isEmbedding_induced

instance (N : ℕ) [NeZero N] : T2Space (Points N) :=
  (pointCoordinates_embedding N).t2Space

@[expose] def sourceMap (N : ℕ) [NeZero N] (q : Source) : Points N := ⟨complexPoint N q⟩

lemma sourceMap_coordinates (N : ℕ) [NeZero N] (q : Source) :
    pointCoordinates N (sourceMap N q)=openCoordinates q := by
  apply Prod.ext
  · apply Subtype.ext
    exact complexPoint_j N q
  · exact complexPoint_x N q

lemma sourceMap_continuous (N : ℕ) [NeZero N] : Continuous (sourceMap N) := by
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def,sourceMap_coordinates] using openCoordinates_continuous

lemma sourceMap_surjective (N : ℕ) [NeZero N] : Function.Surjective (sourceMap N) := by
  intro p
  obtain ⟨q,hq⟩ := ThreeArithmeticSurjective318.complexPoint_surjective N p.hom
  exact ⟨q,Points.ext hq⟩

/-- Actual topological properness of the specified arithmetic comparison. -/
theorem sourceMap_proper (N : ℕ) [NeZero N] : IsProperMap (sourceMap N) := by
  apply isProperMap_of_comp_of_t2 (sourceMap_continuous N) (pointCoordinates_embedding N).continuous
  simpa only [Function.comp_def,sourceMap_coordinates] using openCoordinates_proper

lemma sourceMap_finite_fiber (N : ℕ) [NeZero N] (p : Points N) :
    (sourceMap N ⁻¹' {p}).Finite := by
  apply (ThreeArithmeticFinite318.finite_fiber N p.hom).subset
  intro q hq
  exact congrArg Points.hom hq

/-- The actual finite-to-one proper surjection is a quotient map in the proven
literal coordinate topology. This is weaker than a bijective analytification comparison. -/
theorem sourceMap_isQuotientMap (N : ℕ) [NeZero N] : IsQuotientMap (sourceMap N) :=
  (sourceMap_proper N).isClosedMap.isQuotientMap (sourceMap_continuous N) (sourceMap_surjective N)

end ArithmeticPointTopology318
