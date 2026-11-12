# Pin actual field structures in both quotient consumers

Immutable successor to original-finite-quotient-reconstruction-r54. Two consumer sources replace local instance declarations whose outputs omitted their determining quotient map and group action by explicit letI telescopes and identical proof-local letI bindings. The original baseAlgebra p kappa and field_structure p kappa b bone bmul hover hb hfixed are unchanged. The normal-chart assumptions and branch hypothesis now sit inside that explicit structure telescope; no new mathematical premise is added. The actual generic base, function field, canonical coordinate, scheme quotient map and complete original arithmetic reconstruction conclusion are unchanged.

OriginalCanonicalCoordinateReconstruction318 and OriginalCartesianCurveReconstruction318 both receive this mechanism fix; the latter closure_branch proof also has the exact same explicit context needed for the actual original chart. No blanket alternative instance or changed field action is installed.

This addresses hazards identified by independent review of54, rather than claiming an observed new hosted failure. Additional chart-producer elaboration remains governed by hosted CI. Static checks only; no local Lean/profiler, new limits, proof acceptance or final arithmetic claim.
