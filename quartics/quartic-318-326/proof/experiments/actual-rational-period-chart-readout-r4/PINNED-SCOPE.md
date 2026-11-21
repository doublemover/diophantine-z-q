# Actual rational period evaluation, r4

Two earlier modules are now strict green on the official hosted run
44941120584. The only repair explicitly presents the residual
localized-base evaluation as the exact application of the original
AlgHom. The previous localization rewrites already succeeded:
the old rewrite could not see through toRingHom coercion; the exact
aeval_X term is applied after changing that elaborated application.
No other source bytes or statements change.
