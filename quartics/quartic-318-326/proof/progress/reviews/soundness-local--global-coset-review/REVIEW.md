# Independent bounded norm-square coset review

PASS. Four exact source snapshots independently rebuilt with Lean 4.35.0 and debug.skipKernelTC=false; all 30 declarations recursively audited with only propext, Classical.choice and Quot.sound. See rebuild.log and REVIEWED_SHA256SUMS.

Reviewed the eight first-descent representatives, rational norm-square elimination, all identity/x=0 branches, the negative-square translate x(Q+T0)=−D/x(Q), actual curve/additive-equivalence and generator equality, literal Norm(fH)=nH² to Norm(xH) square, common torsion offset and sign H−V=P, and n≠0. No mismatch found. In particular V=(n−1)P+tau uses exactly the same tau as H=nP+tau; it does not incorrectly discard torsion.

The resulting literal label theorem remains conditional on FirstDescentClasses and SquarePointGeneration. This review does not prove those global arithmetic inputs, the finite generator enumeration, rank, or canonical-height estimates. Imported dependency proofs were not all rebuilt during this bounded pass.
