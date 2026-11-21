# A fixed-index scalar with an exact denominator squareclass

The signed isogeny Cassels forms on the literal conductor-15
receiver now have explicit first-level formulas and an exact
second-level test for the chosen marked class. Its value on the
unchanged scalar still requires a denominator character. An
independent specialization keeps the actual original input a=0
and real index h, changes only the translated index, and proves
that the entire odd denominator squareclass is the product of
the four known normalizer primes. It retains the visible local
rows used in both tests.

If the retuned scalar's squareclass has exactly one unseen
prime, both scalar Selmer spaces have order four, the second
pairing is nontrivial, and the resulting conductor-15 twist has
rank zero with both 2-primary Tate–Shafarevich groups of order
four and exponent two. The one-unseen hypothesis is not proved.
No rank at the unchanged scalar, rational marked point, or
simultaneous four-pole detector tuple is asserted. The separate
positive numerical example only controls the opposite,
rank-one gate for an unlinked permitted numerical profile.

- [First and second Cassels forms](rc-native-helper-20261120/ct-original-constant15-cassels-first-second-r1/EXACT-CONSTANT15-FIRST-AND-SECOND-CASSELS-BITS.md)
- [Exact retuning and conditional rank-zero deduction](rc-native-helper-20261120/ct-original-constant15-clear-crossed-retune-r1/EXACT-RETUNED-SCALAR-WITH-NO-CROSSED-DENOMINATOR.md)
- [Signed independent review](independent-review-nov20/rc-constant15-actual-retuned-denominator-cold-r1/INDEPENDENT-ACTUAL-CONSTANT15-RETUNED-DENOMINATOR.md)

```sh
sha256sum -c SHA256SUMS
(cd rc-native-helper-20261120/ct-original-constant15-cassels-first-second-r1 &&
 python3 -B replay_scalar_cassels.py | cmp - EXACT-SCALAR-CASSELS-CONTROLS.json)
(cd rc-native-helper-20261120/ct-original-constant15-clear-crossed-retune-r1 &&
 python3 -B check_retune.py | cmp - EXACT-RETUNE-CONTROLS.json)
```
