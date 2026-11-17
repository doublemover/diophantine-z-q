module
public import FifthCompletedGlobal318
public import CubicClosedImmersion318
public import CompletedIntegral318
public section
noncomputable section
namespace FifthCompletedProper318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma infinityShort_injective:Function.Injective FifthSourceInfinityAlgebra318.shortMap:=by
  intro a b h
  apply FifthShortFraction318.embedding_injective
  apply Subtype.ext
  have he:=congrArg FifthSourceInfinityCoordinates318.embedding h
  have ha:=RingHom.congr_fun FifthSourceInfinityAlgebra318.original_field_square a
  have hb:=RingHom.congr_fun FifthSourceInfinityAlgebra318.original_field_square b
  exact ha.symm.trans (he.trans hb)
theorem infinityFinite_dominant:IsDominant FifthSourceInfinityScheme318.toFinite:=by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap FifthSourceInfinityAlgebra318.shortMap.toRingHom)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  intro x hx
  have he:FifthSourceInfinityAlgebra318.shortMap x=0:=hx
  have hz:x=0:=infinityShort_injective (he.trans (map_zero _).symm)
  rw [hz]
  exact Ideal.zero_mem _
theorem proper:IsProper map:=by
  letI:=CubicClosedImmersion318.structure_separated A B
  letI:IsProper (map≫WeierstrassGluing318.structureMap A B):=by
    rw [over_Q]
    exact (ContactGlobalProper318.proper_integral_extension units).2.2
  exact IsProper.of_comp map (WeierstrassGluing318.structureMap A B)
theorem dominant:IsDominant map:=by
  letI:=infinityFinite_dominant
  letI:=CompletedIntegral318.completed_irreducible A B
  letI:=AffineCoordinateDomain318.affine_domain A B
  letI:Nonempty (ShortAffineScheme318.scheme A B):=by
    change Nonempty (Spec (CommRingCat.of (ShortAffineJacobian318.Ring A B)))
    infer_instance
  letI:IsDominant (WeierstrassGluing318.finiteChart A B):=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
      (WeierstrassGluing318.finiteChart A B).isOpenEmbedding.isOpenMap⟩
  letI:IsDominant (InfinityGlobalScheme318.chartEmbedding units≫map):=by
    rw [on_infinity,FifthSourceInfinityScheme318.intoCompleted]
    infer_instance
  exact IsDominant.of_comp (InfinityGlobalScheme318.chartEmbedding units) map
theorem surjective:Surjective map:=by
  letI:=proper
  letI:=dominant
  infer_instance
theorem target_smooth:Smooth (WeierstrassGluing318.structureMap A B):=
  WeierstrassGluing318.structure_smooth A B discriminant_unit
theorem target_proper_integral:IsProper (WeierstrassGluing318.structureMap A B)∧IsIntegral Target:=
  ⟨CubicClosedImmersion318.structure_proper A B,CompletedIntegral318.completed_integral A B⟩
end FifthCompletedProper318
