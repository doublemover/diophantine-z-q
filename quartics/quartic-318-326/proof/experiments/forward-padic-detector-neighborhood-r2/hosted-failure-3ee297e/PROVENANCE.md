# Exact hosted normalization injection failure

Main3ee297e passes the repaired NormalizedPointSigns module. The next module NormalizationInjection318 fails because the exposed scale constructor cannot resolve a private elliptic helper, and two root-nonzero proofs compare a composed algebraMap to the opaque base map. The full tested bytes remain unchanged. This evidence is not a successful kernel check of NormalizationInjection.
