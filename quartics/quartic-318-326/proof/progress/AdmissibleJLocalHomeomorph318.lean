module
public import ActualJImmersion318
public import AdmissibleQuotientCover318
public import ModularCoordinateProper318
public section
noncomputable section
open Filter Set Topology
namespace AdmissibleJLocalHomeomorph318
open ModularArithmeticCoordinates318 ThreeArithmeticQuotient318 OpenJLocalComparison318
set_option maxHeartbeats 0

lemma locus_complex_embedding :
    Topology.IsOpenEmbedding (fun tau : Locus => (tau.val:ℂ)) :=
  UpperHalfPlane.isOpenEmbedding_coe.comp
    AdmissibleQuotientCover318.locus_open.isOpenEmbedding_subtypeVal

/-- Genuine j, restricted to the actual admissible period locus, is locally
invertible in the existing topology, by its computed nonzero derivative. -/
theorem periodJ_localHomeomorph :
    IsLocalHomeomorph (fun tau : Locus => ActualQJ318.jInvariant tau.val) := by
  intro tau
  let hc := locus_complex_embedding.isLocalHomeomorph
  let hd := (j_analyticAt tau.val).hasStrictDerivAt.hasStrictFDerivAt_equiv
    (ActualJImmersion318.deriv_j_ne_zero tau.val tau.property)
  let e := hd.toOpenPartialHomeomorph j
  refine ⟨(hc.localInverseAt tau).symm.trans e,?_,?_⟩
  · constructor
    · exact hc.self_mem_localInverseAt_target
    · change (hc.localInverseAt tau).symm tau∈e.source
      rw [hc.localInverseAt_symm]
      exact hd.mem_toOpenPartialHomeomorph_source
  · funext z
    symm
    change e ((hc.localInverseAt tau).symm z)=ActualQJ318.jInvariant z.val
    rw [hc.localInverseAt_symm]
    change j (z.val:ℂ)=ActualQJ318.jInvariant z.val
    simp only [j,UpperHalfPlane.ofComplex_apply]

@[expose] def sourceComplexJ (q : Source) : ℂ := QuotientJ318.jMap 3 q.val

lemma sourceComplexJ_projection (tau : Locus) :
    sourceComplexJ (sourceProjection tau)=ActualQJ318.jInvariant tau.val := rfl

/-- Genuine j is an actual local homeomorphism on the existing level-three
source quotient. No global fine-level freeness hypothesis is used. -/
theorem sourceJ_localHomeomorph : IsLocalHomeomorph sourceComplexJ := by
  have hcomp : IsLocalHomeomorph (sourceComplexJ ∘ sourceProjection) := by
    simpa only [Function.comp_def,sourceComplexJ_projection] using periodJ_localHomeomorph
  have h := IsLocalHomeomorphOn.of_comp_right (s:=Set.univ)
    hcomp.isLocalHomeomorphOn AdmissibleQuotientCover318.localHomeomorph.isLocalHomeomorphOn
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  simpa only [Set.image_univ,sourceProjection_surjective.range_eq] using h

end AdmissibleJLocalHomeomorph318
