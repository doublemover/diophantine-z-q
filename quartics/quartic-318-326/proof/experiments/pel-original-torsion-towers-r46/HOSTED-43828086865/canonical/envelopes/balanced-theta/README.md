# Original balanced theta product repair

Own normal run43828086865, exact4b989557 torsion45:67 whole-module passes, then BalancedThetaProducts1.818s,667 unreached. This is a failed packet.

Three actual issues: rename unavailable card_insert_of_not_mem to pinned card_insert_of_notMem; retain the same holomorphic factor multiplication but transport its proof along an explicit whole-function product equality, avoiding simp rewriting of differentiability dictionaries; invoke native Finset.prod_ne_zero_iff explicitly with a direct public import of its owner.

All original coefficients, finite indices (including n=0), theta series, full lattice, balance condition, product and automorphy maps retained. No new premise, option, runtime budget or public mathematical signature change. Extra native import explicitly disclosed. No local Lean or current propagation/hosted success claim.
