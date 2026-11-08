# Actual branch signs and whole-quotient cancellation

For every rational unit twist family c and every finite branch i, the original Q[t]-algebra Boolean sign extends to the entire actual branch localization. The exact original source map, polynomial scalars, all four original roots and normalized branch coordinate are preserved or negated as specified. The induced Scheme map satisfies the actual branch/global square, including the ramified locus.

The single i-th root flip induces the identity on the whole quotient ring by the literal original branch coordinate y_i. This is an equality for every quotient element, not merely a residue-field or selected prime statement. An anti-invariant regular coefficient is therefore divisible by y_i, because2 is a unit in the quotient. No quotient reducedness assumption is used.

The controlling endpoints are BranchSignScheme318.flip_square, BranchFlipQuotient318.quotient_fixed, and BranchFlipQuotient318.divisible. BranchSignLocalization318.on_source, on_polynomial, flip_coordinate and flip_other_root retain the exact original maps and sign choices.

All three exact sources passed strict kernel-checked Lean. Log3 includes a failed earlier quotient draft; only its successful BranchSignScheme318 marker certifies that source. The final quotient source is certified by log4. A fresh target-only private-inclusive recursive audit passed43 declarations across3 modules, only propext, Classical.choice and Quot.sound, and checked all required theorem endpoints as propositions. Integrated/hosted replay and independent consuming review are pending.

This packet provides the omitted-branch cancellation prerequisite for actual four-character differential descent. It does not itself prove that descent or construct Picard, Jacobian, polarization or PEL objects. The action is on the entire actual branch ring, and the stronger whole-(y_i) quotient identity is separately proved rather than inferred from the earlier prime/residue inertia results.
