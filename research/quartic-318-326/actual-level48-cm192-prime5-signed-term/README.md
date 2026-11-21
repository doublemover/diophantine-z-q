# A prescribed simple CM intersection at 5 on the original first arm

The two literal marked CM −192 flags now have an exact finite receiver at 5: the replay computes the 2- and 3-level choices, tangent normalization, and genus sign. An individual collision at a good, unramified prime has an exact length from the anti-diagonal quaternion norm. If the already allowed final-prime progression permits an inert characteristic-5 residue, a further choice of the same shared prime produces an individual length-one term of either prescribed sign, retaining the same pole and both Selmer eights.

This does not determine the **sum** of the signed terms at 5, the rest of the oriented ideal, a trace, rank, or a rational point.

- [Exact fixed receiver and replay](proof/ACTUAL-CM192-P5-RECEIVER-CALIBRATION.md)
- [Good unramified intersection length](proof/ACTUAL-CM192-GOOD-UNRAMIFIED-INTERSECTION-DEPTH.md)
- [Actual compatible final-prime refinement](proof/ACTUAL-CM192-PRIME5-SIGNED-TERM-PRODUCTION.md)
- [Signed independent review](independent-review/INDEPENDENT-CM192-PRIME5-TERM-REVIEW.md)

    (cd proof && python3 -B replay_cm192_p5_smallest_prime.py | cmp - EXACT-CM192-P5-RECEIVER.json)
    sha256sum -c SHA256SUMS
