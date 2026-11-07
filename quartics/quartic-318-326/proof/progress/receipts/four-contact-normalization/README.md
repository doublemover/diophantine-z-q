# Actual normalization of four even contacts

This packet constructs the joint raw quadratic order and its normalization, including all split or repeated factors. All results are kernel-checked against the pinned Mathlib. No geometric realization is asserted.

## Exact proved content

- `TensorPairBaseChange318` constructs the actual tensor/base-change equivalence and proves compatibility on every order element.
- `FourContactOrder318` defines the tensor of the four actual quotients R[Z_i]/(Z_i^2-u_i*pi^(2m_i)). It proves finiteness, freeness, rank16, and constructs the actual map to the tensor of the four unit-root algebras. If pi is nonzero over a domain, this map is injective. After making pi a unit, an actual generic-fiber equivalence is proved, with the exact order-map compatibility.
- `FourContactNormalization318` derives the actual integral closure of the raw order in the genuine generic-fiber algebra from Mathlib's smooth integral-closure base-change theorem. Over a DVR with 2 invertible, the result is a finite etale rank16 algebra. The order is itself rank16, and the injected generic fiber is explicitly identified. The ambient algebra is not asserted to be a field.
- `ActualFourContactNormalization318` starts with the four original inputs f_i and their actual finite even canonical DVR valuations. It derives one common uniformizer and four units, constructs the actual map from the original four-polynomial order by equality transport, and proves that its integral closure is the constructed cover. No unit decomposition, root, normality, generic presentation or final normalization assertion is assumed.

The m_i=0 cases are allowed in these algebraic results. The pi-nonzero condition required for injection and generic equivalence is derived from the actual irreducible uniformizer in the final theorem. There is no formal-series evaluation at a unit here.

## Scope still open

The actual source geometric local fiber must be identified with the joint four-polynomial order. The source's local chart, the even-contact hypotheses and invertibility of2 must be established at the relevant places. These results do not construct a compact curve, an Arakelov realization or the final unconditional Diophantine theorem.

## Reproduction

`bash run.sh > build.log 2>&1` strictly rebuilds the four source modules and exhaustive declaration audit. The script uses only the pinned Lean/Mathlib and the explicitly listed sibling proof packets. The permitted axiom roots are propext, Classical.choice and Quot.sound. No proof placeholders or native-decision oracle are used.
