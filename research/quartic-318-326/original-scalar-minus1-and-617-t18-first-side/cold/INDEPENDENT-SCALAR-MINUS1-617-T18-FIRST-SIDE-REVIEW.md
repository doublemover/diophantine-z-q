# Independent review: literal scalar first points at input −1 and 617

**PASS for the exact first-equation proof and its fixed arithmetic replay.** This receipt binds:

| File | SHA-256 |
|---|---|
| Author `SHA256SUMS` | `d89938215c030b787965c3761f79f3f1c5d23e8c94f10c17e0b15cb8b0e4b679` |
| `ORIGINAL-SCALAR-MINUS1-AND-617-T18-FIRST-SIDE.md` | `2d02612b79aa76cdfe37a23d9425abccf799ec862be5d4dd3ff2f4d8516a8bdf` |
| `replay_two_input_first_points.py` | `dc485d8991f77ae09d1dd9dedfb61ae259b225fc7a0a75f2349ed4caa4f779a9` |
| `EXACT-TWO-INPUT-FIRST-POINTS.json` | `5916652e714f2836eecd92cbcc990708e1ecf0787b0619511b19ec049ede4222` |

The four exact native source hashes were checked independently: `ScalarForwardWitness318.lean` `9b21f269bbf73da643a7259f71dc67ea835a52aaa97bbb6d449549004bf7038c`, `ScalarActualInputs318.lean` `669eb03d31c5490f7278608a416e1e44ec64d10aa90c044c64c6636759e810f1`, `PreparedIntegerSource318.lean` `e3ecec834054e138eb6cc64c92f0e431510c64a878803d689fa55a9fdf06c423`, and `NormalizedPolePoints318.lean` `410995ba113f37dfcb54261e61eb6b90fde58242a4fa0eed79282e99ad060542`.

For input −1 I checked the sharp prepared scalar donor (list `7a3ff6e99c9d4873a41c067ab9ca97cc8a1e109b260107587b4e59eba640abd7`, paper `0449a6016288fd5427719413adc719a8c9ef6bc569a06666b484a9bc3da350a9`) and the separately archived fixed first point (list `16ba82294a3aeef50bfd7182c33ab01fa04a3e541238e2870be2901b3cdb312b`, paper `5dcb7aed94a3be91c5ecf2de57fba678ab00fe93741df876e80f7b6cbf6216e4`). The native scalar only sees the input through the polynomial in a+a², once the exact index and translated label are fixed: the two detector slots read the same chart at that index, and the inverse norm depends on that label. The numerical first point is therefore reused on the same fixed elliptic base at input −1. No equality of packed scalars at different source pairs is inferred.

For 617 I checked the original prepared row and its real guard in the exact reconstruction (list `0a59f95dc56fec541c99877690aa90807e3a75e40fc4b7dcee20ba0b376d3848`, paper `882b8b12f7c41976ac38d1f0f541a2ac6cf43881fa2dfbf36c45648794dfe499`, exact scalar record `7f22536b2da38e57de106f7ea63c0ed10226144d78ec2ec09fdfbbb82d10d8af`). The fixed scale factors as stated, with a new representative beta and a distinct fixed base. The same polynomial point identity is applied to that base, not the old numerical point. On both actual scalars the literal abscissa is B=17b, the parameter satisfies 0<T<B, and the nonzero ordinate gives the exact first equation. The fixed-integer replay matched the author JSON; it does not expand or replace the native packed scalar value.

Only the first scalar equation is supplied at each of the two already specified inputs. There is no complement or companion, full PointPair, rank, new index, anchor, detector tuple, or full four-pole result. No native Lean result beyond the pinned source inputs is asserted.

Signed: independent original-quartic reviewer, 2026-11-22.
