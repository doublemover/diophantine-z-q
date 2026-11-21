# A larger family preserving both marked Selmer groups

For one already prepared literal Ready pole, fix a previously selected
pair of twists, including its existing omitted prime and matrix
witness. The reserve-prime construction proves that there are
\(\gg X/(\log X)^{1-\delta/2}\) **distinct** common squarefree
multipliers in \((X,2X]\) preserving both exact full Selmer groups of
size eight and the same original mark. Here \(\delta>0\) is the explicit
relative prime density of the admissible old residue rows. No rank,
rational PointPair, final witness to either polynomial, new numerical
pole, or Lean validation is claimed.

- [Primary theorem, with exact conditions](rc-native-helper-20261120/ct-original-reserve-prime-paired-count-r1/RESERVE-PRIME-AND-THIN-PAIRED-RANK-TARGET.md)
- [Signed independent review](independent-review-nov20/rc-reserve-prime-paired-count-cold-r1/INDEPENDENT-PAIRED-RESERVE-COUNT-REVIEW.md)

The included prior notes are context and provenance, not new results;
their manifests are retained as historical bindings rather than
vendoring all of their own dependencies. The finite graph replay is
self-contained and uses Python's standard library. The prime count is
a paper consequence of Bombieri–Vinogradov, not a numerical count.

    sha256sum -c SHA256SUMS
    (cd rc-native-helper-20261120/ct-original-reserve-prime-paired-count-r1 && \
      python3 -B replay_reserve_graph.py | cmp - EXACT-RESERVE-GRAPH-CONTROLS.json)
