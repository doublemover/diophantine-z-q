# Actual inert-prime exclusion and selected-place realization

## Result

Six Lean modules close the good-prime local-place-existence seam for all three literal 318 detector chains. The final theorem in each chain takes the actual raw circuit constraints and a positive odd finite contact, and produces a square root of 2 in Q_p together with a selected orientation satisfying all sixteen literal leaf bounds. At that same orientation H has depth at least 8, while H at the opposite orientation is a unit.

The final `RawSelectedContact318` theorems do not assume a square root in Q_p, an abstract valuation, leaf inequalities, parity of auxiliary weights, terminal-chain facts, pole facts, formal logarithms, reduction maps, elliptic group labels, or finiteness of the auxiliary scale valuation.

## Proof layers

1. `InertPlace318.lean` proves that nonsquareness of 2 in ZMod p prevents cancellation in a²−2b² after the common p-power is removed. It proves the exact integer and rational norm-valuation formulas, then handles zero coordinates with WithTop integers. The actual valuation on Q(√2) is

   v(a+b√2) = min(v_p(a),v_p(b)).

   Multiplicativity follows from norm multiplicativity and injectivity of doubling on WithTop integers. The triangle inequality follows coefficientwise. Crucially v(p)=1 and v restricted to Q is v_p, not 2v_p. The norm formula is v_p(N(x))=2v(x).

2. `InertSourceExclusion318.lean` applies the already checked literal-source contact extraction at this actual inert valuation. The two rational norm leaves force positive valuation of both compressed factors H and V at this same place. The raw compression identity and its checked separation theorem forbid this. All three positive odd consumed contacts are therefore impossible at an inert prime, and all three force a square root of 2 in ZMod p.

3. `InertHensel318.lean` lifts that residue root using Mathlib's checked Hensel lemma for X²−2 over the p-adic integers. The prime is odd, and the residue root is nonzero, so the derivative 2x is a unit. This yields an actual square root in Q_p. The three source-specific corollaries provide the formerly assumed square root.

4. `InertSelectedContact318.lean` composes these actual square roots with `SelectedContact318.source_contactj_selected`. It retains the full selected orientation statement, including the exact 16 leaf inequalities, H depth at least 8 and opposite H unit.

5. `FiniteScale318.lean` removes the auxiliary nonzero-scale premise. A0=1. A2 is the square of the product of four nonzero root norms. For A1, each literal root satisfies j²=h⁴−D, and both real embeddings of D exceed 1; hence the absolute value of each root at both embeddings exceeds 1. For the product's two conjugates u,v, this implies |uv|>(|u|+|v|)/2≥|Re(product)|. The norm therefore cannot cancel the real part. This is a source-linked real-algebra argument, with no global labels or parity premise.

6. `RawSelectedContact318.lean` instantiates a=padicValRat p A_j using the proved A_j≠0 and removes the finite hA input from all three selected-contact statements.

## Exact remaining premises

For chain j=0,1,2, the final theorem assumes:

- p is prime;
- the literal `Constraints (stage0 S) w` hold;
- p does not divide `contactModulus`, 17, or 41;
- the actual rational valuation of t_j−root(i) is the positive odd integer f, for i in Fin 5.

The conclusion also retains 0 < f−5·padicValRat p A_j. The contact modulus is exactly 2·3·5·7·11·37·109·439·2399 from `FiniteContact318`, not a newly enlarged exceptional set.

This closes local-place construction and exclusion for an already consumed finite contact. It does not manufacture a contact, prove the final Lucas/group-label comparison, identify elliptic scalar multiplication, prove a formal logarithm isometry, or discharge the full source arithmetic statement.

## Validation

Run `bash inert-place-bridge/run.sh` from the scratch root. It fresh-builds all six modules using Lean 4.35.0 with `-Ddebug.skipKernelTC=false`, then audits every declaration of those modules recursively for axioms. The accepted whitelist is exactly `propext`, `Classical.choice`, and `Quot.sound`. The full audit reports 67 declarations across 6 modules. There are no admitted proofs or native-decide axioms.

`receipt.json` records exact file, imported-source, compiler-log and audit hashes. Local soundness independently reviewed and rebuilt all six modules, including finite-scale elimination, with no mismatch. Its separate receipt is `soundness-local/inert-review/REVIEW.md`. Its copied-source audit covers 62 declarations; the fresh in-place audit covers 67 including generated module auxiliaries. Both recursively check all axioms against the same standard whitelist.
