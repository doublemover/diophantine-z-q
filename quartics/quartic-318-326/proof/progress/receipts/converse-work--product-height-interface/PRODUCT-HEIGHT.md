# Actual product-height identity and real factors

Source: pinned V10, lines 19378–19424, `v9:lem:product` and the beginning of `v9:cor:scales`.

## Checked conclusions

Three modules contain fifteen audited results. All pass kernel checking with only `propext`, `Classical.choice`, and `Quot.sound`.

1. `ProductHeight318.absolute_height_product` proves exact actual absolute-height additivity for any finite occurrence-indexed family of elements of K=Q(sqrt(2)), assuming:
   - at each actual normalized finite place, either every factor has absolute value at most one or every factor has absolute value at least one;
   - at every actual real embedding, every factor exceeds one.

   The proof multiplies the local maxima, exchanges the finite products with the actual finite-place product using proved finite support, applies the exact relative height formula, and then the proved actual absolute normalization. Repeated factors are allowed. There is no norm down to Q in the formula.

2. `RealMultiples318.multiple_P_abscissa_gt_one` proves the real-embedding hypothesis unconditionally for every actual nonzero integer multiple nP. The proof establishes:
   - the actual image of D=(3−sqrt(2))² exceeds one at either real embedding;
   - a nonzero square abscissa on the actual curve exceeds one, using the actual curve equation;
   - any finite nonidentity double has such an abscissa, using the literal doubling formula, with identity and y=0 branches handled explicitly;
   - nP is not the identity for n≠0, using the proved actual canonical height and its positive value at P;
   - P=2R identifies nP as the required double.

3. `OddProductHeight318.odd_multiple_height_product` specializes additivity to odd integer labels. Its **only remaining argument** is the actual finite-place common weak-sign property. That property is being supplied separately by the local subgroup lane; this package does not pretend that it has proved the full odd-label identity without it.

4. `OddProductHeight318.product_real_part_positive` proves that the actual product's rational coefficient C0 is positive. Both actual real embeddings of the product are positive and their sum is twice C0. This assertion is unconditional for nonzero labels, does not require the finite-place sign property, and includes the empty product.

## Exact scope

The finite local algebra, global normalized product calculation, real factors and C0 positivity are closed. The arithmetic construction of the finite-place subgroup/common weak signs is not part of this package. No formal-neighborhood or reduction theorem is assumed silently. The source's norm-versus-product distinction is retained throughout.

## Reproduction

Run `bash verify.sh`. The receipt binds the three source files, compiled objects and axiom logs, the exact consumed height/canonical receipts, and the actual curve/doubling inputs. No live height or repository source files were edited.
