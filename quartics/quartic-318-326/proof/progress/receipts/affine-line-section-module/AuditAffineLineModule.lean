module
import all OpenLineSectionBasis318
import all AffineLineModule318
import all AffineLineFrameCover318
import all OpenLineRestriction318
import all AffineModuleSectionEquiv318
import all AffineLineSections318
import all FifthLineSectionModule318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`OpenLineSectionBasis318,`AffineLineModule318,`AffineLineFrameCover318,`OpenLineRestriction318,`AffineModuleSectionEquiv318,`AffineLineSections318,`FifthLineSectionModule318]
  for name in #[`OpenLineSectionBasis318.overFrame,`OpenLineSectionBasis318.sections,`OpenLineSectionBasis318.basis,`OpenLineSectionBasis318.restrictFrame,`OpenLineSectionBasis318.sections_hom_inv,`OpenLineSectionBasis318.sections_inv_hom,`AffineLineModule318.restriction,`AffineLineModule318.restriction_localized,`AffineLineModule318.span_top,`AffineLineModule318.localBasis,`AffineLineModule318.finitePresentation,`AffineLineModule318.flat,`AffineLineModule318.rank_one,`AffineLineFrameCover318.locallyFree,`AffineLineFrameCover318.principalCover,`AffineLineFrameCover318.properties,`OpenLineRestriction318.frame,`OpenLineRestriction318.covers,`AffineModuleSectionEquiv318.ring_square,`AffineModuleSectionEquiv318.ring_roundtrip,`AffineModuleSectionEquiv318.equiv,`AffineLineSections318.properties,`FifthLineSectionModule318.sectionEquiv,`FifthLineSectionModule318.properties] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        checked := checked+1
  unless found == 7 do throwError "Expected seven modules, found {found}"
  logInfo m!"AFFINE_LINE_MODULE_AUDIT_PASS declarations={checked} modules={found}"
