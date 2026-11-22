# Input zero: the optional exact-c secant test at 181 and a fresh-key retuning

This concerns only the optional degree-two specialization of the fixed t=18 secant. It distinguishes the old archived scalar from a new residue condition imposed **before** selection of a fresh shared detector key. It does not test the full secant, find a global square or companion, or make any inference for a previously selected key.

## 1. Exact archived obstruction and one passing lifted residue

Write $R_s=4376874610839020$, $L_s=114444R_s$, $c=12W/(1+L_s)$ and keep the native packed scalar $W$. For the two optional slope choices in the [exact degree-two family](https://github.com/doublemover/diophantine-z-q/tree/e1b7907bc834f0243da2287cfe3607880ec9fa5c/research/quartic-318-326/actual-common-index-t18-degree-two-specialization), the needed squares are

    F_±(c)=(2ac±2A)^2+B_0 c^2,

where $a,A,B_0$ belong to the fixed t=18 first point, not the native input symbol. At 181, the stripped denominator $(1+L_s)/181$ is the unit 132, and $(A,a,B_0)=(147,151,78)$ modulo 181 with no denominator trouble. If $v_{181}(W)\le0$, then $v_{181}(c)<0$ and $F_\pm(c)/c^2$ reduces to $4a^2+B_0=58$. Its quadratic character is minus. Thus neither prescribed slope produces a square at that scalar. Conversely, $v_{181}(W)\ge2$ gives $v_{181}(c)\ge1$, so both expressions reduce to the nonzero square $(2A)^2$ and pass **at 181**.

The exact original half-generator $R=(1+\sqrt2,2\sqrt2)$ on $y^2=x^3-(3-\sqrt2)^2x$ has order $909=3^2\cdot101$ in its inert reduction at 181. The replay checks the vanishing multiple and both prime-divided exclusions. Work with the original chart $U=2y/(x^2+(3-\sqrt2)^2)$, $H=\operatorname{Norm}U(hR)$, $I=\operatorname{Norm}U(iR)$, and the half-trace $\operatorname{Re}U(hR)^2$. The exact original $N,Q,W$ normalization is evaluated only in the following three rows:

- The old archived index $h_o=473592745039516333133760$ and its pinned **old** $i=6^{15}3^{65536}J$ have $(h_o,i)\equiv(378,171)\pmod{909}$. The replay gives $H,\operatorname{Re}(U_h^2),N,Q,W,I=(172,133,120,111,146,81)$ modulo 181. This rejects both optional signs there.
- For comparison only at the **same old h**, the exact newer compact label has $i=3^{32767}A_{\rm label}\equiv117\pmod{909}$. It gives $(H,\operatorname{Re}(U_h^2),N,Q,W)=(172,133,120,29,144)$ modulo 181, still rejecting both signs. It is not the old scalar value or a claim of all four Ready at that index.
- With those newer labels, $i\equiv123741\pmod{164529}$. The one passing class is $h\equiv8676\pmod{164529}$: modulo $181^2$, the chart of $h$ is $19336+7620\sqrt2$, and $(H,\operatorname{Re}(U_h^2),N,Q,W,I)=(21309,3419,6078,7201,0,26002)$. The good-reduction kernel from level $181^2$ to $181$ is killed by 181, so $164529=181\cdot909$ annihilates the lift in that group. The unit chart denominators of the replay persist throughout the indicated index class. Hence every such $h$ with these labels passes both optional square tests at 181. No other candidate index or slope is searched in this replay.

## 2. Actual pre-key refinement from the distinct certified sharp center

Use the **sharp certified scalar center** $h_s$ and its newer labels $(3723,s,3723,3723)$ from the full preparation packet, not $h_o$. The packet verifies $v_2(h_s),v_3(h_s),v_{17}(h_s)=(6,5,1)$, its whole scalar support, and the physical anchor on these same labels. Define $M$ as the least common multiple of all ten good odd support order values in that packet and the numbers $p^{v_p(h_s)+1}$ for every scalar support prime. Then

    M = 13315331113518436574832396171766859356800,
    gcd(M,164529)=9,
    h_s + 11422 M ≡ 8676 mod 164529.

The new seed progression is the exact compatible CRT class modulo $L_{\rm seed}=\operatorname{lcm}(M,164529)$ with residue $h_s+11422M$. It preserves $64\mid h$, all old support orders and the depths of $h_s$. At 2 and 3 the square-unit proof in the sharp packet uses exactly the retained depths and translated label; at every other support prime the invariant formal norm-depth difference uses only the saved two index valuations and the retained order divisibility. Therefore the same scalar preparation holds throughout this seed progression, not just at $h_s$. The scalar real-margin guard at a new index is recovered in the following step; it is not inferred from the arithmetic seed.

With fixed labels apply `JointSmallPrimePreparation318.adjust_center` directly to the seed residue and modulus. Its conclusion gives a guard-admissible $h_0$ still explicitly congruent to the seed modulo $L_{\rm seed}$ and with the required real scalar margin. Then `AllSmallPrimeProgression318.simultaneous` at that $h_0$ returns the 2/3/17 thresholds and a positive $L$ divisible by $L_{\rm seed}$, carrying all three literal local preparations. This is the order in the proof of `AllScalarDetectorJoin318.join`; the exposed adjustment theorem is used here because the outer `join` result does not separately expose the original center-congruence field. Now the exact retained class $h\equiv h_0\pmod L$ preserves both the earlier scalar preparation and the 181 lift. The physical anchor is unchanged: its equation depends only on the retained labels and the already fixed auxiliary power, not on $h_0$, the final $h$, or the detector key.

Only **after** this refinement fix the wheel of the published [linear Gaussian prime theorem](https://github.com/doublemover/diophantine-z-q/blob/f767adfb8eba61b98fc865e82f73776f4f095799/research/quartic-318-326/actual-linear-denominator-prime-route/original-linear-denominator-prime-route-r1/LINEAR-GAUSSIAN-PRIMES-TO-ORIGINAL-READY-POLES.md). Its base already contains all primes of $L$. At its new odd primes 101 and 181 the existing Gaussian residue $(0,1)$ is a unit of norm 1 and has both translated norms 2. This is the ordinary allowed ray, giving odd avoidance in both quarter LCMs. The fixed base exclusion ensures the actual contact product is coprime to $L$; choose the theorem's $Q$, rectangle and cutoffs only after $L$. Its fresh shared denominator and contact primes meet the existing five CRT conditions. `ThreeDetectorCRTWitness318.prepared_family` then retains $h\equiv h_0\pmod L$ while giving the exact detector and real guards. The purpose of taking the new modulus before the key is precisely that no old fixed-key quarter modulus is assumed to accommodate it.

This supplies one further necessary local condition for the optional exact-c family on a fresh simultaneous four-Ready/anchor source. It does not supply a numerical key, a selected scalar value, a global match to the degree-two family, or any of the four PointPairs. An alternate $c$ of the same complement squareclass, another slope choice, or another first twist is outside the archived obstruction.

## Exact pins and replay

- Published sharp preparation and four-Ready handoff at commit `8c12e21cc9c435448851848493892619b7336334`; handoff SHA `32586939c5d28abf22f63a54a8549ae5e5e07cf880dfadef162d765350d0d115`. Three unchanged replay donors are pinned by exact SHA in the script.
- Original native `JointSmallPrimePreparation318.lean` SHA `a592270f177c9742440c66ccf5548cfda2c07660b462cd87e203f43ef52046a1`, `AllSmallPrimeProgression318.lean` SHA `2de81b3053e3ad9677af02591fdfa901a0505613b8d5e4222dfda9e6fc5e0597`, `AllScalarDetectorJoin318.lean` SHA `36f345e2d74e522d46c20cd3a5cba49f31642355d5209dfbb0be6a71748f2c41`, and `ThreeDetectorCRTWitness318.lean` SHA `837caa15e52f368f9a2e98443e4b410bd64884fbf7b456dd9053eab9fd6812d0`.
- Exact Gaussian proof text SHA `29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0` at the immutable link above.

```sh
sha256sum -c SHA256SUMS
python3 -B replay_one_181_lift.py | cmp - EXACT-181-OPTIONAL-SECANT-CONTROLS.json
```
