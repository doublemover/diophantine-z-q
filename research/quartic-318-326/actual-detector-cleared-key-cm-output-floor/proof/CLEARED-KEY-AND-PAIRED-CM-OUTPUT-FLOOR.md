# Exact size barriers for the protected original detector and its paired CM orbit

These effective bounds concern the existing positive linear-$q$ key, 13/19 protection, and balanced three/four-helper twist selection on one of the three original detectors. They apply before the shared numerical preparation index and companion support are known. They do not cover all Ready inputs, decide a coefficient or rank, or preclude a compressed arithmetic evaluator. The scalar is not included in the numerical floor.

## 1. Clearing and the Gaussian ray force large genuine primes

Write $c=c_j$ for the actual nonzero rational scale of one detector. The five roots of the published quintic are
$$
\mathcal R=(0,-1/2,-1,1/2399,-32/407).
$$
The exact key uses a positive integer clearing $D$ and $t=u/(D^2 Q^2q)$, with row primes
$$
p_r=u-(D/c)^2Q^2q\,r\qquad(r\in\mathcal R).
$$
The order-only prime $q$ and all five row primes are positive, genuinely distinct in the row, and in the prescribed Gaussian ray. Merging equal slopes across different rows does not reduce this support. Put $A=|D/c|$. Clearing the slope of $r=-1$ makes $A^2$ integral, hence $A$ is integral. The other slopes force $2,2399,11,37\mid A$: $2399$ is prime, $407=11\cdot37$, and $32$ is coprime to $407$. Thus
$$
A_0=2\cdot11\cdot37\cdot2399=1952786\quad\mid\quad A.
$$

Let $m$ be the base Gaussian ray modulus, 16 times the distinct odd base primes. Its ray class field contains $\mathbf Q(\zeta_m)$. Indeed $4\mid m$, and over $\mathbf Q(i)$ the cyclotomic Artin symbol of an ideal coprime to $m$ is its ordinary rational norm modulo $m$. Principal ray generators congruent to 1 modulo $m$ have norm 1 modulo $m$, so this cyclotomic Artin map factors through the Gaussian ray. The cyclotomic subfield is rational abelian with conductor $m$ since $16\mid m$. Hence the conductor $F_0$ of the maximal rational-abelian subfield is divisible by $m$, and the published paper chooses $F_0\mid Q$.

The base contains $3,7,17$, all primes of $D$, and additionally $13,19$ in the protected refinement. The first row has scale 1 (the unscaled row 190); its slope clearing gives $A_0\mid D$. Thus $11,37,2399$ are base primes for every row. In particular
$$
m_0=16\cdot3\cdot7\cdot11\cdot13\cdot17\cdot19\cdot37\cdot2399
    =1377557733552\quad\mid\quad Q.
$$
So $AQ\ge S=A_0m_0=2690075456272075872$. Extra original denominators, the support wheel and deeper local protection can only increase this lower bound.

For every genuine prime the Gaussian ray gives norm $17\bmod32$ from $(9,0)\bmod16$, and $3\bmod7$ from $(1,3)\bmod7$. Combining with $1\bmod408$ gives the exact rational ray $8977\bmod11424$. Its two least primes are $P=54673$, $P'=77521$, by bounded trial division. Hence $q,p_*\ge P$ and $qp_*\ge PP'$, where $p_*$ is the row prime at the largest root $r_*=1/2399$. This does not assume which prime is smaller. The other four row primes obey
$$
p_r=p_*+(AQ)^2q(r_*-r)\ge P+S^2P(r_*-r).
$$
By the literal contact and order-only-$q$ calculation, $\beta=17q\prod_{r\in\mathcal R}p_r$. It follows that
$$
\beta\ge B(S):=17PP'\prod_{r\ne r_*}\bigl(P+S^2P(r_*-r)\bigr)>2.91\cdot10^{172}.
$$
This is a lower envelope, not an attainable key. Either balanced twist contains all of $\beta$, a new $q_0\ge7$ and at least three distinct type-one helpers congruent to $1\bmod24$. The least possible product of three such helpers is $73\cdot97\cdot193$. Repair primes and the factors in either companion side are positive integers. Consequently both absolute discriminants satisfy
$$
n_i\ge N(S):=7\cdot73\cdot97\cdot193\,B(S)>2.78\cdot10^{179}.
$$
The exact integers and complete bounded primality checks are in the JSON. The earlier rational-ray-only bound did not enforce that the five primes come from the same cleared linear key.

**Even without $F_0\mid Q$.** A future proof keeping the same positive row forms and rational prime ray still has $11424\mid(AQ)^2r$ for each nonzero root, by subtracting $u$ and removing the coprime $q$. In particular $v_2(AQ)\ge3$ from $r=-1/2$; $3,7,17$ divide $AQ$; and $11,37,2399$ already divide $A$. If it additionally keeps the same protected negative depths for $T=c^2t=u/((AQ)^2q)$ at $13,19$, then these primes divide $AQ$ because $u,q$ are units there. Thus $AQ\ge S'=m_0/2=688778866776$, and the same lower envelope gives $n_i\ge N(S')>5.14\cdot10^{126}$. This does not assert that any new prime argument realizes the relaxed recipe.

## 2. An unconditional orbit-output barrier for distinct selected twists

Choose the actual $q_0$ refinement for the 13/19 receivers, so the positive squarefree $n_i$ are $23\bmod24$. Then $d_i=-n_i$ are negative fundamental discriminants and $\chi_{d_i}$ are primitive nonprincipal real characters of conductor $n_i$. For $n_i>4$, the class-number formula gives
$$
h(d_i)=\frac{\sqrt{n_i}}{\pi}L(1,\chi_{d_i}).
$$
By [Tatuzawa, *On a Theorem of Siegel*, Theorem 2 and equation (1)](https://www.jstage.jst.go.jp/article/jjm1924/21/0/21_0_163/_pdf), pp. 163–164, for fixed $0<\epsilon<1/2$ the strict bound $L(1,\chi)>0.655\,\epsilon\,k^{-\epsilon}$ holds for primitive nonprincipal real characters of conductor $k\ge\max(e^{1/\epsilon},e^{11.2})$, with at most one exceptional character. Take $\epsilon=1/400$ and $k=n_i\ge N(S)$. The threshold follows already from $n_i>10^{179}$ and $\log 10>9/4$. At a nonexceptional member,
$$
h(d_i)>\frac{0.655}{400\pi}N(S)^{199/400}>8\cdot10^{85}.
$$
The last comparison uses $\pi<22/7$ and raises positive rationals to the 400th power before comparing integers. For the relaxed recipe, take $\epsilon=1/280$; the same exact procedure gives $h(d_i)>5\cdot10^{59}$ at a nonexceptional member.

If the relative class $\theta=[1-b/17]\ne1$, then $u'\ne v'$ for the chosen coprime squarefree factors $\theta=u'v'$ and the two selected $d_i$ are distinct. At least one member of that particular pair is nonexceptional. If $\theta=1$, a single fixed repeated pair could be exceptional. In that case two distinct admissible $q_0$ in the same final CRT class give two distinct discriminants, so at least one of those admissible choices is nonexceptional. This latter argument is not a bound for each fixed repeated pair.

A characteristic-zero oriented CM orbit has $h(d_i)$ distinct class indices. Thus any method taking one step or emitting one record per class uses more than $8\cdot10^{85}$ steps/records on at least one arm of every distinct pair in the published protected construction. Keeping only one balanced genus half leaves more than $4\cdot10^{85}$. Distinct classes need not give distinct finite chart labels. The simpler first-coordinate trial loops for the exact norm forms already have the other explicit bounds in the JSON: more than $7\cdot10^{88}$ candidates on the chosen parity/Lie residue branch both at 13 and for the $j=7$ row at 19. A compact abstract class group or class-number computation need not produce anything of this size, but its relations alone do not give the weighted oriented pushforward modulo 3. None of these bounds is a lower bound for an aggregate evaluator.

One precise caveat for a finite-state class-action shortcut: at an odd split prime $s$ away from the level, the local maximal order is a matrix algebra. Passage to a horizontal index-$s$ superlattice changes basis with elementary divisors $s,1$. For $\lambda^2=d_i$ in $\mathbf Z_s^\times$, the integral matrices
$$
V(t)=\begin{pmatrix}\lambda&0\\s^j t&-\lambda\end{pmatrix}
$$
have the same square $d_i I$, same reduction modulo $s^j$, and same selected eigenspace spanned by the first vector modulo $s$ for $j\ge1$. Enlarging the first lattice coordinate by $1/s$ conjugates by $\operatorname{diag}(s,1)$, so the lower-left entry becomes $s^{j-1}t$. The next orientation modulo $s^j$ is not determined by the old one modulo $s^j$. This local fact is not a counterexample with two globally identical CM records and does not rule out different aggregated states. It shows why fixed-precision local class action plus group relations is not an immediate replacement for the missing arithmetic.

## 3. Smallest rigorous next construction

1. Materialize one common source: bind the actual integer input, nonzero labels, prepared $h_*\bmod L'$, clearing and protected $Q$, one positive numerical $(u,q)$ and the required Gaussian prime generators. Verify the exact prime forms, primality and all translated-norm gcds. Exhibit the same $h$ satisfying the shared original CRT and strict real guards, then evaluate the literal pole in its own row.
2. If $b=B/C^2$ with integers $B,C$ and $C\ne0$, bind $\theta$ without factoring the whole denominator: give positive squarefree $\theta$ with prime certificates and an integer $R$ with $17(17C^2-B)=\theta R^2$. This certifies the precise squareclass of $1-b/17$, whether or not the rational presentation is reduced. The literal elliptic charts and rational identities can be supplied as arithmetic circuits; their exact verification, not a few unbounded modular shadows, is required.
3. For the actual pair made from that single source, accept either a proof of its two nonzero aggregate order-three coefficients, or exact nontorsion points with the same marked back-map. The latter avoid enumerating CM norms: rational torsion has exponent two by the split Tate place at 3 and full rational 2-torsion, so a verified nonzero good reduction of $[2]P$ is enough. Each selected 2-Selmer group has eight elements; rational rank at least one then saturates the actual marked Kummer class. A literal rational PointPair also bypasses rank.

This packet supplies neither step 1 numerically nor a paired nonzero coefficient or marked point. Seek aggregate relative arithmetic, an applicable theorem on the two true periods, or short rational witnesses; do not expand a per-class CM trace on this construction.

## Exact dependencies

- *Linear Gaussian primes suffice for the same original Ready poles*: SHA-256 29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0 (key, conductor, original CRT and valuation conditions). The original clearing owner is ClearedContactForms318.lean, SHA-256 1ed66c70b966ecf2b036c3efbc92e87999a981f92602dd318fd0993cacac875d.
- *Protect 13 and 19 before the original linear-q detector selection*: SHA-256 fc6f587769f884a2f39f1bbf9eefe69f8970a5cea895a18ea4615d27ee1f57ba (new base primes and negative even $T$).
- *A shared final prime retains the two Selmer eights under a detector split*: SHA-256 4b2d39bf6b4f5e9dda8e33482c723dfba02569f8a0e285c005c646aa35d5fe6e (same $\beta,\theta$, shared helper roster and final CRT).
- *Actual 13/19 order-three coefficient contract*: SHA-256 2b67bc37a0e5514d6acbc977094035a862249f33a42bea6c6cb085591706ac0e (actual oriented orbit, norm forms and rank back-map).
- *Actual CM genus half at inert thirteen*: SHA-256 563aa3228061fac5f6c3aa5f8c54fb4c17cbb3040e3833a7f5b20604a9b96844 (prior rational ray-only floor and genus half).

Replay:

    python3 -B replay_cleared_key_cm_floor.py | cmp - EXACT-CLEARED-KEY-CM-FLOORS.json
    sha256sum -c SHA256SUMS
