# Global smooth proper contact model

ContactGlobalSmooth318.smooth_proper_integral_model proves that the actual previously constructed normalization of the original contact cover over the projective contact line is smooth and proper over Q and is an integral scheme. No global smoothness, properness or normal-source hypothesis is supplied to that endpoint.

ContactSmoothBaseCover318 proves the entire t-chart and the specified reciprocal infinity open cover the actual projective contact line. It checks the reciprocal denominator has nonzero constant term, covers its affine chart by the basic opens of s and that denominator, and uses the actual projective overlap map on the punctured line.

ContactGlobalSmooth318 pulls this cover back to the actual normalization. The previously constructed whole-source and infinity open embeddings have exactly those inverse images as their ranges. Their checked structure-map squares and local smoothness therefore descend to smoothness of the actual global rational structure map. Properness and integrality are the already established actual global-model properties.

This is a rational smooth proper integral model of the specified four-root contact cover. It is not yet a formal realization of the PEL Shimura curve or its Jacobian comparison, a controlled integral model, a genus computation, or an unconditional Diophantine height theorem.

Run run.sh under shared heavy.lock. Every module and recursive axiom audit is capped at 180 seconds and kernel checked with debug.skipKernelTC=false. The audit permits only propext, Classical.choice and Quot.sound.
