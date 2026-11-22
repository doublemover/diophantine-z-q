# Independent review: the common-index scalar's relative isogeny and fixed secant test

**PASS for the mathematical reductions and exact fixed-coefficient replay.** This receipt binds the following two frozen author packets.

| File | SHA-256 |
|---|---|
| Relative-isogeny author `SHA256SUMS` | `173d6f342c7a87f71430fe6cb7b2799cc02da878f771095c55cef238d6f3c158` |
| `COMMON-INDEX-SCALAR-T18-RELATIVE-ISOGENY-GATE.md` | `5c7e2e4714440b551a7ccdc1256a9202596064d281100c3d3becb531619e456d` |
| Fixed-secant author `SHA256SUMS` | `e3c9390760080729456a6926e61552a7883aa939ca84ac8156e31a2846782d37` |
| `FIXED-SECANT-TEST-FOR-THE-COMMON-SCALAR.md` | `abdda9ebcde0564d9902fd3d352e4cea8d757f7561709bf6688588d192fbdb81` |
| `replay_t18_fixed_secant.py` | `8e3958c6d52bfac56a7bc5c12d93c116fe6c222d9af4776ce8fd99badced5f6e` |
| `EXACT-T18-FIXED-SECANT.json` | `1528cfd29d004b220b4dbe1c1d134ed54d77735047dd98a3d6def8dae49f51ed` |

I verified the literal native scalar formula (source SHA-256 `9b21f269bbf73da643a7259f71dc67ea835a52aaa97bbb6d449549004bf7038c`) and the original common-index support-unit handoff (author list `9dc74e33f8afb1fdb40aae98ed766ab5bedb8f8cb63b828c4bc04f401e9b34f5`), fixed first-point/trace input (list `16ba82294a3aeef50bfd7182c33ab01fa04a3e541238e2870be2901b3cdb312b`), and the fixed-beta and dyadic rows from the pure-second calculation (list `66b5e1c5e01763abfbc6a060d5889621ee07580158a73c393017db091e5f27d3`). The two point scalings give the actual prescribed raw PointPair, which requires a nonzero second abscissa multiplier, not a prescribed second Kummer slot. The ordered relative class is labelled by the given first point under the twist sign, and its isogeny image is exactly the bare x-class obstruction. Local solvability uses the stated prepared scalar on that same index, including good-reduction unramified pairs at the remaining nonsquare-beta places. No archived extra ramified depths are used. The additive, minimal cuspidal reduction at 5 rules out the existing good-ordinary detector argument on this scalar.

The pushforward trace on the isogenous curve is a trace of two conjugate points exactly when the given secant quartic has a rational point. I checked the non-double argument, the absence of vertical, repeated-root and infinity exceptions for nonsquare delta, the exact factorization, and the scaled integral polynomial. From a fresh copy I replayed the author standard-library controls byte for byte. Those controls evaluate only fixed coefficients.

I checked the Cassels–Tate adjunction with the dual isogeny, and the resulting vanishing against every element of that dual kernel. For any partner killed by 2, its dual image is killed by the original isogeny; its isogeny-Selmer preimages map to pure-second full descent classes. The same beta/dyadic rows rule out any preimage of a nonzero such image whose pure-second class uses just the fixed primes. Higher or unseen-support partners are not excluded. Quadratic restriction and corestriction yield only the already known factor of 2; a lift to a higher Selmer group gives precisely divisibility in the stated finite Sha subgroup. In particular the radical of the full pairing on the 2-Selmer group is the image from the 4-Selmer group, as recalled in [Fisher, *On binary quartics and the Cassels–Tate pairing*, §1](https://www.dpmms.cam.ac.uk/~taf1000/papers/bq-ctp.pdf), not the rational Kummer image in general.

This is a reduction for the actual common-index scalar and the fixed first choice t=18. Neither paper chooses the eventual index, computes the moving complement, evaluates the obstruction or a pairing, obtains a point, or proves a scalar rank. No other first choice or native Lean claim is covered.

Signed: independent original-quartic reviewer, 2026-11-22.
