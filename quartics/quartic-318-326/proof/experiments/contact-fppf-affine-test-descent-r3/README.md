# Original Contact relative descent for fppf covers of affine tests

Status: source draft, hosted elaboration and recursive axiom audit pending. No local Lean compilation, baseline promotion, represented Picard/Jacobian or PEL identification is claimed.

This connected extension removes the affine-cover requirement from the previous Contact Čech result when the original test base is affine. Every original fppf covering morphism onto that affine test, with possibly non-affine and non-quasi-compact source and without requiring the arrow itself quasi-compact, has an actual finite affine faithfully flat refinement. The refinement is the existing constructed one, not an additional hypothesis. Its original totalMap base change is a genuine refinement of the original total covering arrow of Contact families.

The original matching class determines the same genuine original Čech datum whose laws were derived from rigidity. Existing refined object descent reconstructs a line that recovers the datum on the whole original cover, not just the refinement. Original compatible isomorphisms descend through the same supplied refinement and recover on the original arrow. This proves existence and uniqueness for the unchanged standard full-test relative-class matching equation. A separate fpqc variant uses quasi-compactness of the original covering morphism.

New source order:
1. OriginalLineRefinementIso318: unchanged original covering isomorphism descends via specified genuine refinement, with literal original covering recovery.
2. RelativeRefinedCechEffectivity318: injectivity and unique relative Čech matching under actual total refinement, without affine f.
3. OriginalTestRefinement318: base change of the actual refinement through original totalMap, with exact original totalMap factorization.
4. ContactFppfCechDescent318: refined, fppf and fpqc original Contact matching theorems; fppf/fpqc hypotheses construct the actual refinement on an affine test base.

All252 predecessor sources are exact contact-cech-evaluation-r2 copies. Frozen earlier packets are untouched. Remaining: coproduct/family assembly and non-affine test-base gluing for full fppf sheaf identification, then degree-zero representability, Jacobian/polarization and their downstream uses. The affine-test-base limitation is retained explicitly.

## Revision after exactcb6-replay hosted replay

The exact cb6 replay passes all earlier composition declarations and isolates the final composite adjoint: its domain is explicitly extendScalars(g.hom.comp f.hom), preventing the generic sheafIso_adjoint simplifier match. Prove the same adjoint equation at that exact domain using the original adjunction unit and definitional sectionsIso formula. No dependent ring-hom rewrite, map change, extra premise, or budget change. Frozen predecessors and exact failure bytes are preserved. Hosted validation pending.

## Revision after bounded source review

Guard the final definitional reflexivity after the exact composite adjunction-unit rewrite, because rw may already close its unchanged goal. Reviewer requested preflight only; no statement, map, hypothesis, or budget change. Hosted validation remains pending.
