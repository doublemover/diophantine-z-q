# The original noncontact t-chart and its cotangent

This paper/replay appendix concerns the literal D=210 curve in the
reverse direction of the original 318/326 proof. The rational point,
its four-root mark, the fine-level lift and the underlying abelian surface
are the same objects throughout. No new witness or replacement model
is selected.

1. [The ordinary cotangent constructor](ordinary-cotangent/ACTUAL-NONCONTACT-COTANGENT-CONSTRUCTOR.md)
   constructs the characteristic-zero d(t) frame and the field-valued
   specialization of the original arithmetic fundamental differential.
2. [The four-root étale handoff](four-root-handoff/ACTUAL-FOUR-ROOT-ETALE-HANDOFF.md)
   supplies the missing ordinary étaleness from the original four ordered
   quadratic equations, actual full-level forgetting and the central-sign
   rigidification of the maximal moduli stack.
3. [The universal family and the KS comparison](background/ACTUAL-UNIVERSAL-FAMILY-AND-UNSCALED-KS.md)
   and [the same finite and complex sections](background/ACTUAL-COTANGENT-FINITE-ARCH-JOIN.md)
   record exactly how this cotangent is used by the earlier comparison.

4. [The independent paper review](INDEPENDENT-ACTUAL-ORDINARY-FOUR-ROOT-REVIEW.md)
   binds both proofs and exact author replays. The background folder also
   gives the arithmetic root constants and the common level-3/11 overlap.

The original project sources for the coarse finite-free étale cover and
its ordinary differential are pinned in
[the existing progress tree](https://github.com/doublemover/diophantine-z-q/tree/226803e8a0cced68705e01a3ba10d337b9ecd11d/quartics/quartic-318-326/proof/progress).
The notes reference Lean source prototypes by declaration name, but the
appendix is paper and portable arithmetic replay, not a remotely hosted
Lean test or a claim of compiled PEL geometry. The actual moduli
representability, polarization and cohomological KS theorem remain
stated classical inputs. There is no claim of étaleness or ordinarity
of the coarse comparison on a bad closed fiber. The modular Jacobian
period/Abel computation is a separate calculation on a different abelian
variety.

Replay with Python 3 (standard library only), from this directory:

    sha256sum -c SHA256SUMS
    python3 ordinary-cotangent/check_ordinary_axis.py | cmp - ordinary-cotangent/EXACT-ORDINARY-AXIS.json
    python3 four-root-handoff/check_literal_coarse.py | cmp - four-root-handoff/EXACT-LITERAL-COARSE.json

The first replay checks 1,416 finite exact examples of the simple-root
equations, including the derivative. The second evaluates ordinary
four-root fiber counts at five primes as arithmetic controls, and
checks the two splitting residues used to exclude larger geometric
stabilizers. Neither converts such controls into an assertion about
the arithmetic moduli fiber of any selected number-field point.
