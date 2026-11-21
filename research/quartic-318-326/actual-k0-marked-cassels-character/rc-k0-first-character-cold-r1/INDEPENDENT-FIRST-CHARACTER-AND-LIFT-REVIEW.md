# Independent review: exact full marked Cassels character and one specified lift

Reviewed exact `ct-original-k0-first-character-r1/MANIFEST.json` SHA-256
`0af83230c7cc5a9c9f7180f9891913178181b8294917cd8aedb5ea8041ea840b` and
`ACTUAL-K0-FIRST-CHARACTER-AND-EXACT-LIFT.md` SHA-256
`e61c502f7d1095929012f34fd1a1184e9e2e68d0745c8afe8ad0f51e216e08a3`.
Author checksums, eight upstream exact files and byte replay all matched.

**Full character.** For a genuine full 2-Selmer partner \((d_1,d_2,d_3)\) with positive squarefree first coordinate on the literal Ready zero-direction model, the marked Cassels sign is
\[
 (d_1/D)\prod_{p\ge5,\ p\mid A+3D^2}(-2/p)^{v_p(d_1)}.
\]
The proof evaluates any *already admitted* partner, not all abstract isogeny-Selmer keys. The first coordinate is odd and prime to \(D\). No assumption of finite Sha is needed for the classical Selmer-4 kernel statement.

* Independently crossed each local tangent product with \((2\beta,d_2)_v\); the extra product is 1 globally. For \(p\ge5\) in \(A,C,A+3D^2\) the corrected signs are respectively \((-2D/p)^{v_p(d_1)},1,(D/p)^{v_p(d_1)}\). The odd-depth \(A\) case uses the actual two torsion generators and \((3\beta,-3\beta)_p=1\); the even-depth case uses separate-slot parity, with the nonsplit even case all-unramified. At all primes of \(C\) the first slot is square and the correction cancels the original unit class 2 on the other slots. At \(A+3D^2\) the separated second slot has even parity. At good primes, including every denominator prime, all Kummer valuation bits and the usable normalized tangent valuations are even; the first class need not be a square unit there.
* At 2 the two scaled nonzero root depths are \(m+2,0\) with \(m\ge4\) even. An odd depth above the cluster violates total parity, and the potential odd depth \(m+1\) has unit ratio 3 or 7 and cannot cancel the third class 5. All smaller odd depths fail by equal classes of the two clustered factors while the third is nonsquare. Thus the first class is odd. The third class is always 1 or 5, harmless in the second adjusted symbol, and the corrected factor is \((6D,d_1)_2\). At 3 the actual two torsion patterns span (or one may analyze depths against \(n+1,2n\) directly); the first class is 1 or \(-3\), so the corrected factor is \((D,d_1)_3\). The real correction is positive. Moving the \(D\)-factors by reciprocity puts them on the good denominator primes. The leftover dyadic symbol \((6,d_1)_2=(-2/d_1)\) cancels the odd \(A\) factors; a possible factor 3 contributes \(+1\). This gives the displayed formula and independently checks the author's equivalent two-reciprocity derivation.

**Specified lift.** The dual-isogeny first key \(3\beta\) is locally admitted at every place exactly when every prime of \(C\) splits in \(\mathbb Q(\sqrt3)\). For the particular full tuple \((3\beta,-1,-3\beta)\), one additionally needs even valuations of \(A+3D^2\) at nonsplit primes for \(-1\) other than 3. At such a prime, the separated slot 2 being nonsquare forces the point into the cluster. An orbit strictly below the collision depth has equal clustered factors, and at/above that depth at least one factor has the collision valuation. Thus an all-unit witness requires even collision depth; when depth is even the full unramified local image has size four and suffices. A primitive positive norm \(u^2-3v^2=C\) is equivalent to the first split test by the real quadratic Minkowski bound \(<2\), selecting one prime ideal per \(p\mid C\), and the sign forced positive modulo 3. The second test is exactly the sum-of-two-squares criterion for \((A+3D^2)/3\). No claim about other lifts of \(3\beta\) is made.

**Literal scalar scope.** In \(\{3\}\cup\operatorname{Supp}(\beta C)\) only \(3\beta\) can be a nontrivial first coordinate there, the beta-supported homogeneous matrix being injective. The exact four fixed denominator factor signs have product \(+1\); the remaining \((561/D_{\rm exc})\) is not evaluated. The small negative-sign norm witness is standalone numerical Ready, not an original scalar or detector output. The proof does not establish any actual original linked PointPair or rank.

Independent mathematical/source cold review: high_review_ci. No Lean execution or remote operation.

