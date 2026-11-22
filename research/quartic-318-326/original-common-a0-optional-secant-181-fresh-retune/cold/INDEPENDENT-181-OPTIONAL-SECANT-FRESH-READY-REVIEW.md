# Independent review: the local optional secant test at 181 and fresh-key retuning

**PASS for the exact bounded arithmetic replay and the fresh-key refinement.**

| Exact file | SHA-256 |
|---|---|
| Author checksum list | `2558dfc95610cc2f214688c4f5f3b8a0cc61ad98f6924af3458cb73f4c4fdb8c` |
| `EXACT-C-181-OBSTRUCTION-AND-FRESH-KEY-RETUNE.md` | `570341178137b8825f56111a2c52fb05ec2a91ad7594454ee302f792344ffc79` |
| `replay_one_181_lift.py` | `82c119c5f5a3a97153b83a3b43bd47ffa9d4278618cca031ba2dcc24ff4a9dce` |
| `EXACT-181-OPTIONAL-SECANT-CONTROLS.json` | `12a45752eec2718ab790736cfac419db96929a27645ed7aed8fc75def7fe8d0e` |

The exact standard-library replay matched the full frozen JSON. I checked that the two optional normalized expressions have nonsquare leading residue 58 when the scalar has a pole at 181; the old archived label and the newer compact label used at that same old index give different actual scalar rows, both obstructed. The known order 909 of the actual half-generator and the kernel killed by 181 between good reduction modulo 181² and 181 justify propagation of the single passing class h ≡ 8676 (mod 164529) for the newer labels. On that class the scalar has positive valuation, and the leading square unit ensures both tests pass at this place only.

The preparation center for the fresh-key argument is the distinct sharp certified center. I checked its retained finite support orders and exact index depths, the compatible congruence and direct original `adjust_center` then `simultaneous` calls, preserving positive real guard and the literal same scalar premodulus. The four native source hashes in the proof and the published Gaussian theorem text `29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0` matched. The ordinary ray at 101 and 181 has norm one with both translated norms two. This allows the additional primes of the progression in the original wheel before a **fresh** key is chosen, and the actual CRT selection keeps the passed residue at the same eventual four-Ready index and unchanged physical anchor.

No actual fresh key, chosen eventual index, global square, companion, or full secant failure is asserted. No inference is made for a previously fixed key or a different rational scalar with the same complement squareclass. This is paper and finite arithmetic evidence, not a new Lean result.

Signed: independent original-quartic reviewer, 2026-11-22.
