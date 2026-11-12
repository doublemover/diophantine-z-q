# Exact inherited hosted312 repair

The hosted312 forward-original-weighted-weyl-r1 log stops at UniformScaledPoleDomain318.lean line76: exact_mod_cast sees real-valued pair projections rather than the required rational inequalities. The retained exact log is HOSTED312-EVIDENCE/UniformScaledPoleDomain318.log.txt.

This packet makes exactly the already published native-dual-levels-r1 repair: after chain_actual rewrites hb to the pair of realChain and imagChain casts, execute `simp only [Prod.fst, Prod.snd] at hb`, then the existing `exact_mod_cast hb`. No statement, coefficient, quantifier, bound or budget changes. The repaired file was compared against native-dual-levels-r1 and is byte-identical.

Therefore1183 (not1184) predecessor sources are byte-identical; one inherited file has this documented elaboration normalization. The nine new source proofs remain pending hosted checking. A first failure in an inherited source is not evidence that downstream new sources passed.
