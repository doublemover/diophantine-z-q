# P-adic representative literal hom reduction

Fresh75 run43975754875 cleared the polynomial map-order failure and left one goal: application of the explicitly constructed ring hom to q equals the cast of q.appr2. Add RingHom.coe_mk and guarded definitional rfl to the existing hmap simp proof. The guard prevents a redundant-tactic error if simp already closes the goal.

Only this proof site changes. All statements, assumptions, definitions, imports, options and resource limits remain unchanged. All1331 other source bytes and1332-root order are retained, including checked modular-root73, checked124 arithmetic sources and the protected filter76 repair.

The repaired target remains a one-root closure. No mathematical layer or auxiliary-prime compatibility is added. Source/API review is not Lean acceptance; hosted checking remains required.
