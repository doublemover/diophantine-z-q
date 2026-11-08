# Actual finite-chart schematic density

Status: four producer modules strictly checked with debug.skipKernelTC=false; bounded recursive import-all audit passed 28 declarations. Hosted integration and independent source review remain separate. No full dependency rebuild was run.

InfinityMonicPresentation318 presents the infinity equation as a monic cubic over R[z] and proves its actual denominator z is a non-zero-divisor. This works for every commutative coefficient ring, including rings with nilpotents. The proof uses an actual left inverse into the monic quotient and flatness of that free module, not field-point density.

SpecSchematicDensity318 identifies injective algebra maps with the required schematic dominance of their Spec maps. SchematicEqualityExtension318 uses the actual closed equalizer of two maps over a separated relative target, with zero ideal kernel, to prove equality after a schematically dominant map.

FiniteChartSchematicDensity318 uses the original localization, pushout overlap identity and two-chart cover to prove finiteChart_dense. Its hom_ext_to_completed determines maps into an actual completed short cubic from their actual finite-chart restrictions and equal structure maps. There is no unit-discriminant or reduced-source hypothesis on these endpoints. Properness of the target is the previously proved CubicClosedImmersion318.structure_proper.

No global group axiom or multiplication kernel is assumed or claimed. Product quasi-compactness/density is a separate packet. The obsolete draft logs and old environment wrapper are not in the public receipt whitelist.
