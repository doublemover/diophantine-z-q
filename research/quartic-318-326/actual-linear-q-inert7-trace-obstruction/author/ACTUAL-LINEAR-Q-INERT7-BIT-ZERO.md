# The original linear-q detector has zero inert-7 Heegner bit

This is a precise obstruction to the **one-prime** finite trace certificate at 7. It concerns each of the three actual linear-\(q\) detector profiles, with balanced or unbalanced selected support, provided the selected \(D=-n\) is inert at 7. It is not a rank obstruction. The exact same low-level method at a different reduction prime remains available.

## 1. A genus character pairs the actual class indices freely

The [published linear Gaussian prime ray](https://github.com/doublemover/diophantine-z-q/blob/add-quartic-318-326/research/quartic-318-326/actual-linear-denominator-prime-route/original-linear-denominator-prime-route-r1/LINEAR-GAUSSIAN-PRIMES-TO-ORIGINAL-READY-POLES.md) requires each true contact prime and the added denominator prime to have Gaussian residue \((1,3)\bmod7\). Their norms are therefore \(3\bmod7\). Each also is \(1\bmod408\). Take any one of those six actual primes \(p\mid\beta\mid n\). In particular \(p\ne7\), \((p/7)=-1\), and \((p/2)=(p/3)=+1\). These are literal support restrictions, not assumed for every standalone numerical Ready pole.

Let \(K=\mathbb Q(\sqrt D)\) with the selected fundamental \(D=-n\equiv1\bmod24\), and let \(H/K\) be its Hilbert class field. The **real** field \(\mathbb Q(\sqrt p)\) lies in \(H\). In fact \(p,D/p\) are coprime fundamental discriminants and the biquadratic field \(K(\sqrt p)\) has discriminant \(p(D/p)D=D^2\); the relative discriminant of \(K(\sqrt p)/K\) is trivial. Write \(\chi_p\) for the resulting quadratic character of \(\operatorname{Gal}(H/K)\).

Fix one prime of \(H\) over 7 and let \(\tau\) be its rational Frobenius; \(H/\mathbb Q\) is Galois and unramified there. Since 7 is inert in \(K\), \(\tau\) is outside \(\operatorname{Gal}(H/K)\). Let \(c\) be ordinary complex conjugation and write \(\tau=\sigma c\), with \(\sigma\in\operatorname{Gal}(H/K)\). On \(\sqrt p\), \(c\) acts trivially and \(\tau\) acts by \((p/7)=-1\); hence
\[
                             \chi_p(\sigma)=-1.
\]
For the selected \(48\)-level ideal \(\mathfrak n=\mathfrak p_2^4\mathfrak p_3\) one has \(\chi_p(\mathfrak n)=(p/2)^4(p/3)=+1\), independent of which primes at 2 and 3 were chosen, since each has residue degree one.

Use the fixed \(48\)-level class orbit \(x_{\mathfrak n}([\mathfrak a])\). The operation \(w_{48}\) reverses the level ideal and changes the base ideal to \(\mathfrak a\mathfrak n^{-1}\); complex conjugation conjugates both ideals. Thus \(g=\tau w_{48}\) acts **within the chosen level orbit** by
\[
          [\mathfrak a]\longmapsto
          B\,[\mathfrak a]^{-1},
          \qquad
          B=[\mathfrak n]\cdot[\sigma]^{\pm1}.
\]
The possible inverse sign refers only to the Artin class convention and has no effect on the quadratic character. This involution has no fixed class because \(\chi_p(B)=-1\), whereas every square class in the finite ideal-class group has character \(+1\). Distinct classes may reduce to the same \(X_0(48)\) coordinate: the freeness is at characteristic-zero class indices, not a claim that the supersingular geometric involution has no fixed points.

## 2. Each class pair contributes the same element of order two

Let \(\phi:X_0(48)\to E_{-1}\) be the exact raw degree-two map used in the fixed-level trace certificate. It satisfies \(\phi w_{48}=T_3-\phi\), with \(T_3=(3,0)\) of order two. For any of the 48 supersingular \(X_0(48)\) labels over \(\mathbb F_{49}\), direct group-law calculation gives the same output
\[
        [2]\bigl(\phi(x)-\operatorname{Frob}_7\phi(x)\bigr)
                        =T_{-1}=(-1,0).                     \tag{1}
\]
The exact phase distribution before doubling is \((1,\pm2i)\), each with multiplicity 16, and \((4,\pm i)\), each with multiplicity 8, for \(i^2=-1\). All four double to the same \(T_{-1}\). The replay verifies the whole chart independently by the exact forgetful \(j\)-map down the modular tower; a single finite sum is not substituted for the universal calculation.

If \(x\) reduces to one of those points then the reduction of \(gx\) has image \(T_3-\operatorname{Frob}_7\phi(x)\). Thus every **class pair** contributes \(T_{-1}\) to the doubled trace, by (1), even if its two reductions happen to coincide. There are \(h(D)/2\) such pairs. In the actual detector profile \(4\mid h(D)\): the two ramified ideal classes at 17 and \(p\) have order two and are independent. Indeed no one of their ideals or their product can be principal, because the norms \(17,p,17p\) are nonsquares below \(n/4\) and an element outside \(\mathbb Z\) has norm at least \(n/4\). The inequality follows from the other actual \(\beta\)-primes in \(n\). Consequently
\[
                    [2]\bar P=(h(D)/2)\,T_{-1}=O.
\]
Here \(h(D)\) is even, so the raw \(P\) is itself anti-invariant and this is exactly the smaller finite nontorsion test, not just an inconclusive reduction after an unnecessary extra factor of 2.

The vanishing is forced for the actual Gaussian ray when 7 is inert. It does not assert a vanishing ordinary/split-7 trace, a vanishing characteristic-zero Heegner trace, rank zero, or failure of independent inert receivers at 13,19,29. In particular the existing positive \(D=-95\) toy is not a counterexample: it does not have the specified actual contact prime type.

## Exact source and replay

- Linear Gaussian prime ray, SHA-256 `29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0`.
- Fixed-level compatible trace, SHA-256 `f1ffe375bf6fe92afe707d06f88dfc6bef2bb2da80532f48cc939f65e395104c`.
- Full prime7 traced-label/weights proof, SHA-256 `c55b170368d49f568ed7a8a38d008b0b9643b1e96afcfcbd57561b3e00dd1fed`.

    python3 -B replay_inert7_constant_pair.py | cmp - EXACT-ORIGINAL-INERT7-CONSTANT-PAIR.json
    sha256sum -c SHA256SUMS
