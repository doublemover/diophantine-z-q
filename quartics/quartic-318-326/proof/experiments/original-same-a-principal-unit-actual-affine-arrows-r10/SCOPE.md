# Original same-A principal-unit affine arrows r10

The exact official r9 packet passed 21/25 with 335 audited declarations
and all 97 traced baseline module keys. ConstantActualReduction is now green.
The sole newly reached compilation error is ActualConstantAffineCoefficients
L152:74 unknown identifier hf. The type of constant_coefficient_restriction
does not mention its section-level chart-square proof hf; the final proof
uses it explicitly to produce the restriction among actual chart maps.
Add include hf in before that declaration. This retains the exact existing
geometric chart-square witness in its telescope, not an additional premise
or map special to the proof. No other proof, statement, import, or owner is
edited. All 21 accepted and three blocked peers are byte-identical.
The 25/97 terminal remains signed forward boundary, not old KS recognition.
