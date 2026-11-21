# Actual ordered coordinate slices are null without a regular-center assumption

Mathlib pin 56a005855ea17e0b0958f73ec801ae140b0a1679. Source-only.
The true chart measure is a finite pi product of the same nonatomic complex
reference measure. Mathlib's pi_eval_preimage_null handles a coordinate
condition with no need for finite total mass in its other coordinates.
Taking the finite union over coordinates and then the image under the
actual differentiable local Abel map proves target nullness for the discarded
slices. No blanket Sard theorem, permutation quotient scaling, or chosen
arithmetic center is involved. Identification of the actual atlas and
its local Haar factors remains separate.
