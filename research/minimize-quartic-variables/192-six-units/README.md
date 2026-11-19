# An exact 192-coordinate quartic family

Input coordinate: 1. Witnesses: 191 rational numbers. Fix C = 149^N, with N≥1 an integer coefficient parameter, not a variable. The 166 displayed primitive integral quadratic residuals have a sum of squares of degree exactly four, with 2,719 occurring coordinate monomials for every such C. The coefficient of X1^4 is precisely 1. The JSON table represents each term as coefficient · C^parameterPower times the product of its listed coordinate indices. No polynomial root-finding or numerical fitting is used.

## What this establishes

For every fixed N≥1 and every rational input, this polynomial has a rational zero above the input **if and only if** the primitive-reference compact 193-coordinate polynomial of José Brox does. In fact the *entire* rational witness spaces are explicitly isomorphic. This does not prove any outstanding arithmetic premise of that polynomial or determine its sufficient parameter threshold. The inherited implication is: under the retained v74 arithmetic premises, for every sufficiently large fixed N this polynomial defines Z in Q. It is not a stand-alone unconditional positive solution to Hilbert's tenth problem for Q, not an effective replacement for the separate fixed 229-variable N=15 result, and not a global minimality assertion.

## Four equations remove a coordinate without adding a zero boundary

Call the last six storage coordinates U,I,T,P,V,J, in that order. Their four equations are U·I=1, P·J=1, P=U·V, T·V=U. Thus U and P are nonzero and V=P/U is nonzero. Given any U,V in Q*, there is exactly one extension:
I=1/U, T=U/V, P=UV, J=1/(UV).
There are no other rational points in this six-coordinate chart. Hence the old seven-coordinate chart from v74 and the new one both represent precisely (Q*)², including both signs.

For each non-unit old coordinate x_i, certificate.json specifies its new consecutive coordinate Y_{renumber(i)} and weight (a,b)=(x{i}_0,x{i}_1). Set x_i = Y_{renumber(i)} U^a V^b. On the common torus this is invertible, including at Y=0, and x1=Y1. The first 162 old equations are divided individually by U^r0 V^r1, using the two weights r{row}_0,r{row}_1, and converted to primitive integral quadratics. These multipliers and the final rational row normalizations never vanish. The supplied verifier compares the pulled-back dictionaries exactly up to one nonzero rational constant per row, and separately verifies both charts' guard equations. It independently expands all 166 squares and checks all root/cancellation claims for C=149^N. Thus the two zero loci agree with no unmentioned saturation or omitted exceptional cases. The last four guards are ordinary quadratic residuals, not promises.

## Reproduction and provenance

Run `python -B verify.py` from any directory (Python 3.10+, standard library only). All necessary source inputs are present. Recover the old-coordinate assignment from a new witness via the formulas above, or compute the new coordinates from an old witness using their inverses. Only arithmetic in Q is required.

The complete 193 source table is included byte-for-byte from José Brox, `JoseBrox/diophantine-z-q_improvements`, commit `d3a8c223716a0fc0dbf5af4eb7998d640c21048d`, [compact source](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/d3a8c223716a0fc0dbf5af4eb7998d640c21048d/computation/quartic/seven_units193_v74/compact/quadratic-family.json), Git blob `4ae582839923c88c0530bfd15b0b0a69562cd4d6`. See the [v74 results](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/d3a8c223716a0fc0dbf5af4eb7998d640c21048d/docs/results_20261117_v74.md) for the arithmetic statement and dependencies. Attribution for the source polynomial remains with the original authors.
