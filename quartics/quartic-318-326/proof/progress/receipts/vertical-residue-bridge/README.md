# Actual residue characteristic and ramification in the different bound

This packet strengthens the frozen local-different bridge without changing it.

- `DVRRamification318.residue_prime_not_unit` derives that p is a nonunit from the actual residue field having characteristic p.
- `value_map` and `value_map_nat` prove that the actual DVR valuation restricts by the actual value of a uniformizer. The proof uses the DVR unit-times-uniformizer decomposition and maps units through the actual homomorphism.
- `VerticalResidueDifferent318.vertical_bound` applies the actual different theorem with the residue-characteristic certificate constructed internally.
- `ramification_value` derives v_B(p)=v_B(pi_A) v_A(p) in the actual DVR tower.
- `ramified_vertical_bound` proves r≤2e e_p floor(log d/log p) with e and e_p defined by those actual valuations. It assumes neither the nonunit certificate, ramification product identity nor the desired local coefficient inequality.

The geometric application still must construct the relevant completed local extensions, identify their different exponent with the differential-divisor coefficient, provide a base uniformizer, and establish local degree≤d and branch prime p≤d. Those are not asserted by this packet. The complementary residue-characteristic-zero horizontal wrapper is in the separate frozen residue-different-bridge.

Run `bash run.sh` for a fresh two-module strict-kernel rebuild and exhaustive recursive axiom audit. Only propext, Classical.choice and Quot.sound are allowed. This packet is outside the386-module checkpoint9554e589.
