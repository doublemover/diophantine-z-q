# Direct finite-divisor arithmetic

Status: strict-kernel PASS. Seven public theorems and12 recursively audited declarations, using only propext, Classical.choice and Quot.sound.

`primeLog n` is the actual finite sum of prime valuations (Nat.factorization) times log p. `primeLog_eq_log` proves its equality with log n. `horizontalContact q` sums this for the reduced numerator, denominator, and numerator−denominator of q, the three rational contacts0,∞,1.

For the actual source range0<q<1, `horizontal_contact_bound` proves this sum≤3·NumberField.absLogHeight₁ q. The source specialization q=1/n,n≥2 is included. The interval qualification is necessary: `negative_one_requires_qualification` proves that the unrestricted no-constant assertion fails at q=−1. This does not change the source application or final constants, because its chosen parameters are positive reciprocals.

`vertical_log_bound` proves the actual finite prime sum

    sum_(p in S) floor(log d/log p) log p ≤ #S log d

for positive natural degree d. `finite_contact_budget` combines these into the direct3h(q)+2#S log d bound with no multiplicative degree loss. In the source application S is the prime set of6N.

This packet checks the finite arithmetic sums and actual absolute rational height. Identifying these sums with normalized arithmetic-surface intersections, constructing the regular model and supplying the local different/pullback inequality remain geometric inputs. The exceptional-negative-part matrix step is separately checked in exceptional-negativity-bridge.

Replay: `bash run.sh`; exhaustive audit: build.log.
