# The fixed old \(h'=-2207\) symbol is a \(415721\)-adic unit

For the literal \(E^\flat:y^2=x(x+76768)(x-407)\), \(N=205042530\), \(p=415721\), the primitive period-normalized old minus symbol at \(h'=-2207\) is a \(p\)-unit. The proof uses a certified short-enough interval for \(L(E^\flat_{h'},1)\) and an integral absolute-cycle comparison. The full 64-million-coefficient certificate proves nonzero directly and requires **no rank-converse theorem or Sha finiteness**. This is the fixed old-symbol unit in the [two-unit arbitrary-D criterion](../joined-fixed-pa-integral-symbol-and-jet-r1/EXACT-P2-NEW-BETTI-LATTICE-AND-TORIC-JET.md); it does not evaluate the varying ramified trace functional, a production toric sum, or any selected point. The old analytic nonzero also independently checks the original fixed even factor.

## 1. Literal modulo-\(p\) integrality and a bound on the period comparison

Let \(\phi:X_0(N)\to E^\flat\) be the map through the connected-kernel optimal quotient and then a shortest rational isogeny. That isogeny is cyclic (a noncyclic kernel contains full prime-level torsion and factors through a smaller map). By duality its degree can be bounded from the literal \(E^\flat\). This curve has full rational 2-torsion, so an odd prime \(\ell\)-isogeny would imply a rational cyclic \(2\ell\)-isogeny. The Mazur–Kenku rational cyclic degree list (original result, stated as [Thm. 5.1 of Michaud–Jacobs](https://wrap.warwick.ac.uk/id/eprint/176222/1/WRAP-Mazur%27s-isogeny-theorem-Michaud-Jacobs-2023.pdf)) leaves only \(\ell=3,5,7\). To exclude 5 use good Frobenius at 13 with trace \(-2\), polynomial discriminant \(-48\) nonsquare modulo 5. To exclude 3 and 7 use good Frobenius at 17 with trace \(2\), discriminant \(-64\) nonsquare modulo both. The replay checks the exact good traces. No rational cyclic 4-isogeny exists either: a generator \(P\) of a stable cyclic order-four kernel has rational \(x(P)\); for a fixed root \(e_i=x([2]P)\), the duplication formula implies
\[
          (x(P)-e_i)^2=(e_i-e_j)(e_i-e_k).
\]
At the roots \(0,-76768,407\) the right side is respectively negative, of odd 2-valuation, and of odd 11-valuation. Therefore the isogeny to \(E^\flat\) has degree at most two. [Česnavičius's semistable Manin theorem](https://arxiv.org/abs/1703.02951) gives \(c_{\rm opt}=\pm1\), and the pullback scalar for an isogeny of degree at most two divides that degree (compose the dual isogeny on Néron differentials). Thus with the literal minimal Néron differential \(\omega\) of \(E^\flat\),
\[
 \phi^*\omega=c\,(2\pi i) f_N(z)dz,\qquad 1\le |c|\le2.
\]
The optimal quotient surjects on integral homology and the isogeny has cokernel supported at 2 on homology. Hence the resulting primitive \(p\)-integral cohomological periods for \(f_N\) differ from \(\omega\)-periods divided by \(c\) only by \(p\)-units; the same is true in the minus sign using the idempotent \((1-\text{complex conjugation})/2\).

Since \(\gcd(2207,N)=1\), all cusps \(b/2207\) with \(\chi_{h'}(b)\ne0\) represent the same cusp as 0 on \(X_0(N)\): find the matrix with second column \((b,2207)^t\) and lower-left entry divisible by \(N\) by Bézout. The weighted sum of paths from \(\infty\) to these cusps is therefore a closed integral cycle, since \(\sum_b\chi_{h'}(b)=0\). It is in the minus eigenspace of complex conjugation by oddness of \(\chi_{h'}\). Its integral on \(E^\flat\) is an **integer** multiple of the primitive imaginary period, not merely rational with an unknown denominator. Finite Gauss summation gives the integer's absolute value
\[
        |I_h|=\frac{|c|\sqrt{2207}\,|L(E^\flat_{h'},1)|}{|\Omega^-_{\min}|}.
\]
Here \(\tau(\chi_{h'})\) has absolute value \(\sqrt{2207}\) and the old twisted symbol differs from \(I_h\) by a \(p\)-unit by the same homology period comparison.

The actual transformation \(x=4X,\ y=8Y+4X\) gives
\(Y^2+XY=X^3+19090 X^2-1952786X\), minimal at 2 because its \(c_4\) is odd; the original odd-prime models are already minimal. Its Néron differential is \(2\,dx/(2y)\) in old coordinates. The lift of the interval \([0,407]\) on the two imaginary branches makes a simple closed cycle, nonzero by its integral and hence primitive on a torus; conjugation reverses it. Thus
\[
 |\Omega^-_{\min}|
 =2\int_0^{407}\frac{dx}{\sqrt{x(x+76768)(407-x)}}
 \ \ge\ \frac{2\pi}{\sqrt{77175}}.
\]
The checker proves \(p\pi/\sqrt{77175\cdot2207}>100\) using rational Machin bounds for \(\pi\). Therefore \(0<|L(E^\flat_{h'},1)|<100\) forces \(0<|I_h|<p\), certifying the actual old unit.

## 2. Certified Mellin interval, not a sampled approximation

The fixed old twist has conductor \(C=N(2207)^2=998731202207970\) (coprime twist), and root number \(+1\): the old Atkin sign product is \(-1\) at the seven tame primes, and \(\chi_{h'}(-N)=+1\) by their exact symbols \((+,+,-,-,+,-,+)\) and the odd arch character. Splitting the weight-two Mellin integral at \(1/\sqrt C\) and using Fricke gives the exact formula
\[
       L(E^\flat_{h'},1)
        =2\sum_{n\ge1}\frac{a_n(E^\flat)\chi_{h'}(n)}{n}
                     \exp(-\lambda n),\qquad \lambda=2\pi/\sqrt C .
\]
At the seven tame bad primes the coefficients are the exact split/nonsplit signs, and at 2207 the twist kills the Euler factor. All other \(a_q\) are computed exactly by the Hasse interval and the literal elliptic curve group.

For each good odd \(q\), full \(E^\flat[2]\) makes \(\#E^\flat(\mathbb F_q)=4m\) for some integer \(m\) in the Hasse interval divided by 4. For each actual point \(P\), \(m[4]P=O\). The checker selects \(P\) by direct modular square-root test. For the first nonzero \([4]P\) it lists **all** annihilating integers in that interval by baby-step/giant-step: write \(m=L+i n+j\), and compare the negatives of \([L+i n][4]P\) with every stored \([j][4]P\); duplicates in the table are retained. For any additional chosen point it filters these integers by exact scalar multiplication. When a single integer survives it is the actual one, since the group order must be among the candidates throughout. If uniqueness fails in eight trials, use the full exact quadratic-character sum. The 64-million run's direct calls only concern the small starting primes. At every good prime at most 2000 the direct sum is also used as an audit: the output label compared_to_direct counts 297 good primes in the audit (49 direct-only small cases and 248 comparisons against the fast route). Prime powers and products then use the usual Euler-factor recursion. Arithmetic bounds: all finite-field products are below \(64\,000\,000^2<2^{63}\); all \(|a_n|\le d(n)\sqrt n\le2n\), including intermediate multiplicative factors.

The exponential sum itself uses **integer interval arithmetic** at scale \(2^{52}\). The exact rational runner bounds \(\pi\) by the alternating Machin identity, \(\sqrt N\) by scaled integer square root, then bounds \(e^{-\lambda}\) by the second/third partial Taylor sums. The two certified integer endpoints for the scaled ratio are \(4503598731974206,4503598731974207\). Compute lower and upper powers by fixed-point multiply with exact floor / ceil, and add each signed summand using rigorous signed floor / ceil. Signed 128-bit integers suffice. A machine approximation is used only to suggest an integer square root which the code corrects by exact integer comparisons, never for the interval.

For completeness, from Hasse and multiplicativity \(|a_n|\le d(n)\sqrt n\). On a block \(x<n\le x+U\), \(U=10^6\), the divisor hyperbola gives
\[
 \sum_{x<n\le x+U} d(n)
 \le 2U\,(1+\log\sqrt{x+U})+2\sqrt{x+U}.
\]
Indeed each pair has a divisor at most \(\sqrt{x+U}\); the count of multiples in the block is at most \(U/a+1\). Dividing this bound by \(\sqrt x\) gives a decreasing function in \(x\) (differentiate the logarithmic term and use \(x/(x+U)<1\)). For \(B=64\,000\,000\) its bound at \(B\) is \(C_0=20U/8000+4=2504\): use \(e^9>\sqrt{65\,000\,000}\) and \(\sqrt{(B+U)/B}<2\). The certified rational bound \(e^{-\lambda U}<41/50\) follows from \(\lambda U>0.1988\) and an upper fourth Taylor sum. The full two-sided tail is consequently \(<2C_0(41/50)^{64}/(1-41/50)<0.085\). The exact finite 64-million interval is \([1111569232644000,1111612588633292]/2^{52}\), which lies strictly between \(0.2468\) and \(0.247\) by integer comparison. Subtracting and adding the strict \(0.085\) tail proves \(0.161<L<0.332\) directly. The separate smaller 32-million replay gives the absolute upper also required for the unit, but not nonzero on its own.

Replay in an isolated scratch directory (only C++17/Python standard tools; no CAS):

    python3 -B check_exact_exponential_and_tail.py | cmp - EXACT-INTERVAL-CONSTANTS.txt
    c++ -O3 -std=c++17 exact_trace_pilot.cpp -o /tmp/exact_h2207
    /tmp/exact_h2207 32000000 | cmp - EXACT-FULL-32M.txt
    /tmp/exact_h2207 64000000 | cmp - EXACT-FULL-64M.txt

The second run alone suffices together with the rational constants and proof. No degree-\(Np^2\) modular form, no \(p^2\)-level trace preimage, and no varying production \(\chi_{d'}\) functional is evaluated in this packet.
