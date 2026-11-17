# Squarefree CRT and centered-root API repairs

Fresh two-root79 run43986190361 exposed four exact errors. In both modules, cast the natural bound to an explicitly natural-absolute-value integer inequality before rewriting Int.natCast_natAbs. The centered-root cast proof additionally simplifies Int.cast_mul. The CRT proof calls the pinned global induction_on_primes and explicitly imports its native Factorization.Induction module.

Only these proof/API sites and the required native import change. All statements, assumptions, definitions, options and resource limits remain unchanged. All1334 other source bytes and1336-root order are retained, including strict126 sources, the four norm ingredients, modular/Qp residue sources, affine80 repair and actual-C81 checkpoint.

The repaired target union remains two native-only experiment roots. No further mathematical layer is added. Source/API review is not Lean acceptance; hosted checking remains required.
