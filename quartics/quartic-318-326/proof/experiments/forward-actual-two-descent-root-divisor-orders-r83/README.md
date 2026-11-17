# Signed auxiliary reciprocity and finite product cancellation

Two independent native-only modules are added. AuxiliarySignedReciprocity318 proves J(C/q)=J(q/|C|) for C=1 modulo4 and odd q, including the negative-C sign cancellation; it conditionally converts the finite-product and splitting6 equalities to a square6C modulo q. AuxiliaryJacobiProduct318 proves the exact reciprocal-pair sign and cancellation of the finite P/U sign product in the real-compatible positive/negative coefficient cases, with explicit gcd and parity premises.

All1336 predecessor sources and their relative order remain byte-identical. Each new module imports only native Mathlib, so the target union is two roots. No unchecked experiment dependency is introduced.

These are narrow finite reciprocity identities. They do not produce the local symbol equalities, prove a CRT residue class is a unit, select a Dirichlet prime, or establish the global anchor. Actual-C81, affine80 and the two82 repairs are retained without claiming their pending checks have passed. Source/API review is not Lean acceptance.
