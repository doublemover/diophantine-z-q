# Literal alternate-source J/G logarithm approximation

This frozen packet binds all four stored alternate quotient variables to actual mapped elliptic logarithms. It uses the literal first numerator polynomial 1-delta/5 and the three literal PJ/QJ numerator quotients, with the common literal PG/QG denominator.

Main theorem: `SourceAlternatePrecision318.source_alternate_precision`.

For any actual field embedding phi:Q(sqrt2)->Qp, it constructs one actual logarithm subgroup containing finite compressed V and all four alternate points. It proves v(log V)=s, v(phi(fV))=2s, s>=1. For the first chart its approximation error is at least
v(phi(u_i)/phi(zV)) + min(8*r_i,16*s).
For the other three charts it is at least
v(phi(u_i)/phi(zV)) + min(16*r_i,16*s).
The approximated expression is the actual log(U_i)/log(V), and the subtracted expression is exactly phi of the stored raw quotient. No logarithm-ratio identity is assumed.

The hypotheses retained are literal source equations, p>=19, phi(D) a unit, positive alternate delta depths, reciprocal-abscissa depth v(phi(fV))>=2, and nonzero shift. The supplied embedding can be the conjugate selected split embedding. The selection and leaf-to-depth conversion are separate source-contact composition, not asserted completed by this packet.

The source curve itself proves denominator depth parity and actual subgroup membership. Full-series branch choice and positive-branch J identification are proved, not supplied. A zero numerator is included. `source_identity_points` handles the separate shift=0 branch: compressed V and all four alternate points are identities, without imposing a false constraint on unconstrained stored quotient variables.

`mappedAlternate_source_point` identifies the mapped point with pointMap of the actual RawRootDifference318.V source point; mappedV is pointMap of actual CompressedTranslation318.V. This is the interface for the independently proved coherent global labels and exact rational logarithm-ratio theorem.

Replay: bash run.sh. Fresh strict kernel checks use -Ddebug.skipKernelTC=false. Full recursive axiom audit: 56 declarations in five modules; only propext, Classical.choice, Quot.sound. No repository edits or PRs are made by this packet.
