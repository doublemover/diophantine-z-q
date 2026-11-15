# Actual translated-index group-law proof termination repair

Published before a257620302c4a784c6c1f1dc9838c8fd61954de3, own descent19 and weighted19 run 43658730606. Both actual logs show the final sub_eq_add_neg rewrite fails because the target is already the identical addition-of-negative expression on both sides. Remove only that redundant final rewrite; retain sub_zsmul and one_zsmul. No active source changed.

1. Required inputs: same n : ℤ and hn : n≠0 in shifted_chart; no additional point, order, nonvanishing or arithmetic premise.
2. Constructed objects: identical local hgroup for the actual generator R, then the existing coherent-addition chart and actual scalar root. No replacement chart is introduced.
3. Coverage: same entire integer index domain and all public declarations; zero excluded only where already required by hn. No finite sample or restricted index substituted.
4. Transition maps: same n−1 shift, original compression shiftWitness and CoherentAdditionU.u_add at n•R and −R. No transport map changed.
5. Scalar factors: same integer scalar action, exact negative sign, k denominators and norm reciprocals. The proof uses the actual additive group structure, not a new normalization assumption.
6. Identity: the unchanged hgroup statement equates (n−1)•R with n•R+−R; sub_zsmul and one_zsmul already produce the reflexive target seen in both authentic errors. Removing the third rewrite leaves native reflexivity to close that identity.
7. Exceptional cases: all existing nonzero chart and denominator proofs remain byte-identical; no exceptional root, sign or coefficient case omitted.
8. Dependencies: imports/options/public telescopes and all later theorem proofs are unchanged. Both own replays passed ScalarLocalSquares (descent 2.571s, weighted 2.369s) and PreparedTwistSource (1.919s, 1.818s); their next first failure is this exact module after 102 successful commands.
9. Verification boundary: own descent19 failure 2.320s and weighted19 failure 2.169s are bound to each exact predecessor intake. This is a proof-only source candidate, not Lean acceptance, a full packet pass, a new resource/trust setting or arithmetic closure. No local Lean/Lake is run; original-source research remains inactive.

Current packet: forward-actual-two-descent-root-divisor-orders-r20. Actual scope: ScalarTranslatedIndex318. Own immutable hosted evidence and exact before/current copies are bound in APPLICATION.json and COPY-BINDINGS.json.
