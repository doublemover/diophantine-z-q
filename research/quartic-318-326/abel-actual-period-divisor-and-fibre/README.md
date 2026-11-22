# The actual period divisor law and regular Abel fibre count

This package contains two independently reviewed classical arguments on
the same original marked compact curve and its own Jacobian:

1. [Point-level divisor-line law](POINT-DIVISOR-LAW.md). Use classical
   Abel's theorem in the full integral-period quotient. Recover its
   meromorphic function in the same marked whole field by trace
   moments on the actual finite cover, without invoking GAGA for
   that readback.
2. [Anchored pencil and the regular fibre count](PROOF-PLAN.md).
   Two distinct effective divisors in one fibre would yield a local
   moving pencil through the reduced regular tuple in the same line.
   The actual local inverse rules this out. Surjectivity uses
   properness of the same algebraic map and one ordinary regular
   derivative. On the full good target the orderings give g! points.

These are paper proofs, **not Lean-verified theorems**. They retain
the actual compact/analytic identification, the same invariant frame
and saturated integral period lattice, the analytic Abel theorem,
and the smooth local analytic/algebraic order comparison. The degree
argument retains the proper same-Jacobian Abel map. The volume consumer
separately needs the full good set and nullity of its complement. The
good set excludes the entire image of bad tuples; the arguments
do not make a regularity assertion for any prescribed arithmetic
J=1 centre or replace the curve's Jacobian with a QM abelian surface.

The author files and source ledgers are unchanged. The two author
manifests and the independent review manifest verify those exact
inputs. The outer SHA256SUMS also covers the published run ledger
and this README. The run ledger records checked Lean components
only, not certification of either paper.
