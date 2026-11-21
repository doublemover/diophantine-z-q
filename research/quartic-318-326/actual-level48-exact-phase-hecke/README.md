# Exact scalar mod-3 Hecke receivers for the protected original detector

The same inert-13 and inert-19 phase functions are now fixed scalar weight-$3/2$ cusp forms modulo 3 with explicit good-prime Hecke eigenvalues. The oriented fundamental coefficient on either arm is unchanged up to a unit. The replay checks all degree-five neighbors of all original oriented chart labels, with exact multiplicities.

This does **not** compute either primitive coefficient for an actual selected detector, prove common-prime nonvanishing, or determine either rank.

- [Exact proof](proof/ct-level48-exact-phase-hecke-r1/EXACT-LEVEL48-SCALAR-MOD3-HECKE-RECEIVER.md)
- [Independent primary-source and finite-arithmetic review](independent-review/INDEPENDENT-LEVEL48-PHASE-HECKE-REVIEW.md)

Replay (Python 3, standard library only):

    cd proof/ct-level48-exact-phase-hecke-r1
    sha256sum -c SHA256SUMS
    python3 -B replay_exact_phase_hecke.py | cmp - EXACT-HECKE-5-LEVEL48.json

The two sibling finite-input directories preserve the exact previously reviewed scripts, lookup data and source manifests used by the replay; their other historical files are not needed here. The top-level checksum covers every byte delivered.
