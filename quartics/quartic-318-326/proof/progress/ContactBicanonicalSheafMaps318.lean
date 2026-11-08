module
public import SectionGeneratorIsomorphism318
public import ContactBicanonicalGenerators318
public section
noncomputable section
namespace ContactBicanonicalSheafMaps318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
@[expose] def zeroMap := ModuleGlobalSections318.ofTop (ContactGlobalBicanonical318.tensor c)
  (ContactGlobalBicanonical318.q0 c)
@[expose] def oneMap := ModuleGlobalSections318.ofTop (ContactGlobalBicanonical318.tensor c)
  (ContactGlobalBicanonical318.q1 c)

theorem zero_branch_isIso (i : Fin 4) :
    IsIso ((Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).map
      (zeroMap c)) :=
  SectionGeneratorIsomorphism318.restrict_isIso (ContactIntrinsicFrames318.branchEmbedding c i)
    _ _ (ContactBicanonicalGenerators318.global_branch_generator c i)

theorem one_infinity_isIso :
    IsIso ((Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map
      (oneMap c)) :=
  SectionGeneratorIsomorphism318.restrict_isIso (InfinityGlobalScheme318.chartEmbedding c)
    _ _ (ContactBicanonicalGenerators318.global_infinity_generator c)
end ContactBicanonicalSheafMaps318
