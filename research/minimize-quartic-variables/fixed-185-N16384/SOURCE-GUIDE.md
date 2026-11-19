# Reproducing the three-contact and eight-factor steps
The fixed choice here is 149^16384. Its arithmetic proof is different from that of the neighboring N=15 polynomial. Neither is unconditional. All counts include the input. No decoded coefficient table needs to be tracked. Use Python 3.11+ from this directory:

```sh
python -B derivation189/check_source189.py
python -B ROW-REVIEW.py derivation189 ../170-eight-mixed-factors
```
The first command reconstructs the 160 intermediate rows from the unmodified v74 Laurent source and independently checks the numerical height bounds. The second verifies all 155 non-unit physical rows of 185 after reversing the coordinate charts, and verifies the nonzero guard. In disposable copies of this folder and of derivation189, run `python -B specialize.py` and then `python -B verify.py` to materialize and check the respective signed-hex tables. WITNESS-MANIFEST.json in each gives the logical byte digest (uncompressed), input coefficient and term count. A numeric expansion is data, not additional evidence for arithmetic premises.

Upstream: José Brox, [exact source revision](https://github.com/JoseBrox/diophantine-z-q_improvements/tree/d3a8c223716a0fc0dbf5af4eb7998d640c21048d), under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The original manuscript and Laurent table mentioned in ATTRIBUTION.md are shared with ../170-eight-mixed-factors (DONOR-MANUSCRIPT.tex and DONOR-LAURENT.json). See HEIGHT-AND-CONTACTS.md, EIGHT-FACTORS.md and README.md for changes. The derivation189 subfolder provides source for the intermediate, not a second new bound.
