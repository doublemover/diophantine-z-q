# Independent review: simultaneous lift norms and a negative bit at every allowed contact profile

Reviewed exact `ct-original-k0-two-norm-contact-profile-r1/MANIFEST.json` SHA-256
`2bf3c1ff16bfcdb07b2b7f3a4cb2aa53821d9f864cb25181061b43def75de229` and
`SIMULTANEOUS-PRIMITIVE-AND-GAUSSIAN-NORMS-ON-CONTACT-PROFILES.md` SHA-256
`2dfc4f12d28f9be00e872e04eb0ff4d3b3ca38b274a4abf776cf9a3a79409f7c`.
All author checksums and four exact upstream pins matched, and replay reproduced the two old profile controls byte for byte.

**Verdict.** For every one of the seven-prime \(\beta\) support profiles allowed for a genuine linear-q detector (either contact phase), the construction gives infinitely many *numerical Ready* poles with the same \(\beta\), with depth one at each of the six contacts, and with a genuine \(k=0\) Cassels obstruction certified by both integer norms. Their companion squareclass may vary. They are not outputs of the original linked fold.

* Both displayed norm identities use the very same \(A=\beta(12tk)^2\) and \(D=12\beta k^2-(t^4-t^2+1)\). Expanding \(A=12t^2(D+f)\) gives \(C=(D-6t^2)^2-3[2t(1+t^2)]^2\) and \((A+3D^2)/3=(D+2t^2)^2+[2t(1-t^2)]^2\). The first is primitive and the second needs no primitivity.
* The monic quartic \(f=\Phi_{12}\) is separable at each selected contact \(p_*\ge409\). If all nonzero values were squares, the smooth genus-one double cover, including its two rational infinity points, would have at least \(2p_*-2\) points, contradicting Hasse. Thus choosing a nonzero nonsquare value there and setting \(t=1\) at each other prime of \(6\beta\) is a compatible CRT. Its sole negative character is at \(p_*\); no choice of the other contact symbols is needed.
* The second CRT ignores, rather than divides by, any old \(\beta\)-prime in \(1+t^2\). At every odd prime of \(1+t^2\), either \(\beta\) or \(k\) vanishes locally, and \(D-6t^2\equiv3\), a unit since \(3\nmid1+t^2\). At primes of \(t\) use residue \(-1\), and at 2 the first norm coordinate is odd. Also \(f\equiv1\bmod t\), \(f\equiv3\bmod(1+t^2)\), so the chosen \(k\)'s remain prime to \(f\), yielding \((A,D)=1\). Large positive \(k\) puts \(C\) strictly between consecutive squares and gives \(0<b=17A/D^2<17\).
* The guards at \(2,3,17\) have the exact depths \(4,2,2\) and local square classes, using the old primes \(1\bmod408\). The selected contacts are at depth one. As \(D\equiv-f\bmod3\beta\) and both \(D,3\beta\) are \(3\bmod4\), the reciprocity minus signs cancel to give \((3\beta/D)=(f/3\beta)=-1\). The primitive norm and Gaussian norm certify the *specified* full Selmer partner \((3\beta,-1,-3\beta)\); this makes the evaluated negative sign a genuine obstruction, not just a candidate isogeny key.

No fixed companion squareclass, source realization, rank or all-direction PointPair obstruction is claimed. Independent mathematical/source cold review: high_review_ci. No Lean execution or remote write.

