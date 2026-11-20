# Exact visible-orientation exclusions for the fixed quartic scalar

The same materialized a=0 scalar has reduced ratio c=C/Z and H=Z²−βC².
All fifteen nonempty switches of known H-prime orientations
(131, 6551, 2470991, 16782959) are excluded by exact finite continued-fraction
cycles in the fixed field Q(√β). A genuinely new primitive norm
representation, outside the original orbit and its conjugate, must
therefore split H/(131·6551·2470991·16782959) into two nontrivial coprime
factors. The calculation does not supply a new representation or a
hidden prime, rank, Selmer class, or scalar point. It is not a Lean proof.

Run sh replay.sh from this directory. Only Python 3 and standard shell
utilities are needed. The two finite replays compute separate exact
quotient trajectories using different state models and CRT methods,
then compare against their original byte-pinned outputs. There is
no scalar expansion, prime interval scan, or numerical height cutoff.
The recorded stopping points are exact repeated states.
Both source modular row tables are included unchanged. The preceding
actual scalar construction and matrix data are available at:
- [The fixed scalar specialization](https://github.com/doublemover/diophantine-z-q/tree/e2ef09acc3675847eacda95f084c3ae86396c4b5/research/quartic-318-326/actual-scalar-specialization)
- [Local matrix and known support](https://github.com/doublemover/diophantine-z-q/tree/527d4f421d526cdbddf0ccd98f27064bf55666a1/research/quartic-318-326/actual-scalar-norm-pair-local-matrix)
