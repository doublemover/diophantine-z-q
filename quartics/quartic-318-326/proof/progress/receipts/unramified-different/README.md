# Actual unramified local algebra gives zero different coefficient

The actual Mathlib criterion that a prime does not divide the different exactly when the algebra is unramified at that prime implies that, in a DVR, the different ideal is the unit ideal. Its actual DVR exponent is therefore zero. This is not a supplied zero-coefficient or local-domination inequality.

`UnramifiedDifferent318.Data` identifies the canonical coefficient with the actual different and supplies the actual unramified local algebra and finite integral extension. `Data.canonical_zero` derives the zero coefficient, and `Data.toCoefficientData` constructs the corresponding branch of the frozen LocalDivisorData318 model input.

Actual completed local-field/ring construction, unramifiedness of the geometric map, and identification of the canonical coefficient with the different remain geometric realization inputs. No actual global curve/model existence or unconditional five-contact theorem is asserted. Structure projections are included in the exhaustive audit count, not counted as mathematical advances.

Run `bash run.sh` for a strict-kernel rebuild and exhaustive recursive axiom check. Only propext, Classical.choice and Quot.sound are allowed. This packet does not edit any prior frozen source.
