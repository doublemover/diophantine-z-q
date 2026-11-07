# Actual Lucas growth

Status: proved with Lean's kernel. The four-module replay audits 27 declarations recursively and permits only propext, Classical.choice and Quot.sound.

The literal equation is
`t² − s(s−2)tz + (s−2)²z² = 1`.
For integral s,t,z with |s|≥7 and z≠0, `LucasSequence318.literal_log_growth` proves |s|−3 < log |t|. `residual_log_growth` gives exactly the logarithmic comparison required by SoundnessHeight318 when |t|≤B.

The proof does not assume generation of norm-one units. It uses a well-founded integer Vieta descent to classify ordered nonnegative solutions of t²−atw+w²=1 by consecutive terms of U₀=0,U₁=1,Uₙ₊₂=aUₙ₊₁−Uₙ. The exact congruences Uₙ≡n modulo a−2 and (−1)ⁿUₙ≡−n modulo a+2 force the relevant index to be large. Both coordinate orderings and both signs of s are covered. The elementary lower bound Uₙ₊₁≥(a−1)ⁿ then yields the actual real logarithmic estimate.

`anchor_orientation_large` derives the necessary |s|≥7 from the actual scalar orientation and 2·3^32767 anchor. `integer_input_from_three_height_comparisons` removes the Lucas premise from the numerical integrality theorem. It retains precisely the high-contact, scalar-height and low-contact comparisons, and requires z≠0 (supplied by odd source labels).

Files: LucasSequence318.lean, LucasDivisibility318.lean, LucasGrowth318.lean. LucasHeight318.lean is unchanged mathematically; its residual definition is now exposed as a public formula so the literal equation can be unfolded across module boundaries. The pushed checkpoint remains byte-identical until the next coordinated integration.

Replay: `./verify_lucas_growth.sh`; complete output: `lucas-growth-audit.log`. This is a bounded arithmetic closure and is not a proof of the retained global five-contact geometric height producer or complete witness existence.
