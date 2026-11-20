# One negative coefficient per direct CM4 trace

For the fixed marked mod-13 eigenline used by the direct conductor-four Hilbert trace at level 48, its full Hilbert residue Λ_d satisfies Λ_d² = 4·A⁻₃₇(d)², where A⁻₃₇ is the earlier phase-normalized negative coefficient of the fixed level-2544 quaternionic theta source.

The [paper proof](comparison/DIRECT-TRACE-ONE-NEGATIVE-COEFFICIENT.md) compares the actual unaveraged conductor-four orbit to an ordinary maximal-order toric period by averaging precisely six dyadic unit cosets, and compares its Waldspurger formula to the negative coefficient formula on the same fixed Hecke lift. The [independent review](independent/INDEPENDENT-REVIEW.md) checks that the torus average is also fixed by the admissible dyadic compact and verifies the full algebraic normalization. This tests one negative coefficient per twist with no positive coefficient or auxiliary imaginary field. It has not produced a common completed production prime q for which **both** required coefficients are nonzero.

### Reproduce the exact finite checks

Run from this directory after leaving the previously published sibling [direct source](../heegner-direct-cm4/README.md) intact:

~~~sh
sh replay.sh
~~~

If the sibling has been relocated, pass its directory as the sole argument. The original proof scripts and seven-case JSON are immutable reviewed bytes; the wrapper reconstructs the old relative directory geometry in disposable scratch and checks the three existing frozen source-donor hashes in the underlying script. The four old weighted JSON donors needed for comparison are included and also hash-pinned. No network, Lean, external package install or production enumeration is used.

The four old substitute-scalar pair references and three small controls d=35,1931,2579 are only finite cross-checks. In the matched 1931/2579 pair both sides give zero/unit with those exact same local types; zero is not a characteristic-zero vanishing assertion.
