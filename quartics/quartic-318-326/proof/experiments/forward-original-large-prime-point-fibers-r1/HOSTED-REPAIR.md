# Exact FormalPoleCoherentChart318 hosted-boundary repair

Latest hosted run on commitb0d8a09c, packetforward-prime-local-counts-r1, passed the retained CompactLocalPointCoding repair and failed at FormalPoleCoherentChart318. The exact source log and RESULT are preserved in hosted-failure-b0d8a09c.

The quotient square must be expanded by div_pow before mul_pow; the actual failing goal still had a quotient under the square. The natural-number absolute-value bounds are explicitly rewritten to the same field numerals used by the later inequalities, rather than leaving w(natCast2) syntactically distinct from w2 to the arithmetic tactic. The already-solved field_simp branch now sequences ring with<;> so success cannot create a no-goals error.

The original K-valued curve's commutative-ring instance and the field's underlying ring are definitionally equal but were not identified by the rewrite tactic's default transparency. The theorem uses the same narrow respectTransparency=false setting already used in the preceding accepted repair, normalizes Q to the exact E(D).Point domain, and instantiates pointMap_some once at the actual x,y,h. The formal-pole inequality is changed to the literal xRep statement before rewriting, avoiding an opaque Real order-instance simplification. No statement, curve, map, field, bound or hypothesis changes. The finite1M heartbeat budget remains unchanged.

All248 other sources are byte-identical to density249r1, including all four new substantive density modules. No local Lean build was run. New hosted checking is required; this source repair is not itself a claim that the whole packet has passed.
