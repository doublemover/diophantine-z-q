# Actual completed nonvertical equalizer and closed torsion inclusion

Status: three new modules strictly checked; recursive import-all axiom audit passed 24 declarations with debug.skipKernelTC=false. Hosted integration and independent review are pending. No full dependency replay was performed.

NonverticalCompletedDoubling318 constructs the actual tangent diagonal of the localization D(2y) and proves that the old localized doubling and negation are exactly the restrictions of the constructed completed doubling and global negation.

ThreeTorsionCompletedEqualizer318 uses the monomorphism of the original finite open immersion to transfer the existing categorical equalizer. Its isLimit and universal endpoints identify the original full rank-eight scheme as the categorical equalizer of these actual completed-curve maps on D(2y). The universal property quantifies over all Scheme test objects, not only fields or affine reduced tests.

ThreeTorsionCompletedClosed318 proves the exact rank-eight inclusion is a closed immersion into the completed curve. Its actual structure map is finite; the completed target is separated, so the inclusion is finite. It is also a monomorphism by the original affine closed inclusion and finite-chart open immersion. Finite plus monomorphism gives a closed immersion. The same argument, using the actual zero-section pullback, proves the canonical map to the actual tripling zero-fiber is a closed immersion.

Hypotheses are an arbitrary commutative base ring, invertible 3, and unit discriminant. No reducedness is assumed and nilpotents are retained. The restricted doubling formula itself does not require invertible 3. The categorical equalizer does.

No equality with the full tripling kernel or its nonzero component is claimed. Turning tripling=zero into doubling=negation still requires a verified cancellation argument; covering the complement of the zero section is also separate. Group axioms, PEL identification and final arithmetic witness construction are outside this packet.
