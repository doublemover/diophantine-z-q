# P-adic anchor universality elaboration repairs

Fresh anchor59 run43899157249 passed107 roots and recursively audited4050 declarations, including the corrected finite-field isotropy module. The newly reached p-adic module failed when simplification distributed polynomial constants before differentiation and when exact_mod_cast did not map the equation from p-adic integers into the field.

At the derivative proof, explicitly unfold F, differentiate the constant first, apply derivative_C_mul_X_sq to the quadratic term, and normalize the numeric evaluation. At the final equation, use congrArg on the native p-adic integer-to-field coercion; the native addition, multiplication, powers and integer casts are definitionally preserved. These are two exact proof repairs, not new hypotheses or construction choices.

All mathematical statements, Hensel norm bounds, isotropic vector data, universality proof, definitions and imports stay unchanged. All1324 other predecessor sources and root order remain exact, including107 passed dependencies and independent pure60 candidates. This successor revises60 and retains the same108-root frontier target. No local Lean or full arithmetic conclusion; strict hosted compilation and recursive audit remain required.
