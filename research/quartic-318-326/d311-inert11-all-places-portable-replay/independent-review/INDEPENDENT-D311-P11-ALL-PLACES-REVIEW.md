# Independent exact review: the bounded D = −311 ideal at 11

**Pass, November 22, 2026 (UTC).** This review binds the exact author projection manifest SHA-256
`c73012e9c6c2e17cbebd33d604e46f017b7e27f23f6e111962b67262b3586017`
and proof
`d7150c800729dbdfcb67260cc891f77d1fbc942d0674356f0ed0993c48cdc31c`.
The exact dual-place row stream is
`4e3f6196bb1413ceb1540d5b5b38d193963086ed9819ec53a7e8b0a2f853cf01`;
the projection JSON is
`cde3b6c222e27dc65b4db87688447e54588d07129522816f3115129f1c947da6`.
The exact first-place proof donor is the manifest
`b938bf96a9d677895937205383a6ca3cf65795143e08d2e059196360c4ab31f6`
and proof
`23073d4950d26dbae32fd7eb3def8582389a5b86161034298af3a24352898108`.

I independently recomputed the complete published one-place and two-place Python/FLINT replays. Both full 19-by-242 outputs compare byte for byte, and projecting the first-place columns out of the two-place data reproduces the earlier whole row stream. I checked the actual geometric matrix columns, absolute Miller Gauss sign, and degree-two Weil transport; all 160 factors per arc are resolved below precision 5 in both embeddings. The coefficient-field substitution is exact: the quartic equation gives $(i/A)^2+2=-(A^2+2)$, so it flips the named $\sqrt5$ while fixing the other real generator and the moving torsion geometry. It does not change signs independently in different terms.

The two measured exponents at the positive named $\sqrt{-n}$ prime are $-20,+20$. The local Frobenius flips only $\sqrt6$ and the global inverse-conjugation identity supplies the other two exponents $+20,-20$. The ideal push to the split binary fields has weight two per place; the inert binary fields have weight one. Only the projection to $\mathbf Q(\sqrt{-5n})$ is supported at 11, with exponents $-80$ at root 9 and $+80$ at root 2.

This checks the complete 11-supported portion for this single bounded control. It does not evaluate another prime, reconcile the complete ideal with the order-nine residue at 29, or evaluate a chosen original discriminant.

**Independent reviewer: Vesper.**
