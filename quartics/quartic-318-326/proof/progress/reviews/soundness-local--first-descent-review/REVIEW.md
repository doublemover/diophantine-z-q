# Independent first-descent review

PASS: all four exact modules were copied, independently rebuilt with debug.skipKernelTC=false, and recursively audited. The audit checks 22 declarations with only propext, Classical.choice, Quot.sound. Source hashes match the producer byte-for-byte and are recorded in REVIEWED_SHA256SUMS; full compiler output is rebuild.log.

The mathematical path was inspected. Every actual prime of the proved Euclidean Z[sqrt 2] order except delta has even x-value, by the curve equation and unequal odd valuation minimum. Removing exactly one delta when necessary makes every prime value even; this works for negative as well as positive valuations. Reduced fraction factorization then expresses x as a square times an actual integral unit. The four unit squareclasses follow from norm ±1, the explicit norm−1 unit 1+sqrt 2, and the already reviewed Pell theorem for norm1 units. Multiplying the four classes by delta gives exactly the eight representatives in the existing FirstDescentClasses definition, with all nonzero denominators/square factors discharged.

GlobalFirstDescent318.first_descent_classes proves that exact arithmetic interface unconditionally; no prime classification, unit-group, or PID premise remains. This does not by itself assert global group generation or canonical-height bounds. Those remain separate work.
