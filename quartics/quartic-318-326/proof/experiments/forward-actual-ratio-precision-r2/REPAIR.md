# Narrow hosted derivative-separation repair

Preserve exact190r1 failure4421a9c8 and frozen198r1. The first genuine error is the multiline simp-only list following a same-line `by simpa`: its continuation is left of the tactic block. Move simpa onto its own properly indented line, preserving the identical simplification terms and exact discriminant equation.

The second error prints w(−x₂+−x₁) versus w(x₁+x₂). Replace unrestricted simpa by simpa only [map_neg_eq_map], directly consuming the absolute value of the unchanged negative sum. No change to theorem statements, hypotheses, actual points or finite1M budget. All197 other sources, including the eight new ratio/comparison sources, are exact198r1 copies. Hosted kernel validation is pending; no local Lean.
