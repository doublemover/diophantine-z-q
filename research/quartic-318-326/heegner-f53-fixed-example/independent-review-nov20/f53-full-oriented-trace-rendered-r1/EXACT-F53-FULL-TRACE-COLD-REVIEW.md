# Independent cold review: fixed 323, discriminant −455, prime 53

This is a mathematical and executable audit of one fixed arithmetic
datum, not a native Lean result or a general selected rank theorem.

## Exact replay

- Full script b1d5ad6e6b879a1ca22e0551c8999777d16be2079fb5807290a9957db62226b1
  independently ran in 76.936 s (exit 0) and byte-matched the frozen
  JSON 8d172729d64384eb192e718573a317e691f7f0862a291eacc4248aea22550a64.
- Integer-lattice HNF schedule and Gauss/trace finalizer independently
  replayed byte-identically. Final JSON:
  8b47edaef8514e1ee554765cbdd4e10d03729b7a1ab889c8951fa3741e4c23d7.
- The attached stdlib checker imports no original evaluator: it
  independently checked all 416 ordered chart fibers, all 5,760
  signs and elliptic point values, 20 signed subtotals, the combined
  sum, both Gauss factors, and the exact order-13 test. It independently
  enumerated all 20 primitive proper reduced forms of discriminant −455.
  Repeated geometric reductions were not removed.

## Class orbit and common phase

Set \(N=48\cdot323^2,\beta=60875,u^2=22=-455\bmod53\).
The seed geometric \(\Omega\) satisfies \(T^2-T+114\) and acts on the
tangent by \((1+u)/2\). The two roots are distinct at every prime of
\(N\). The degree norm test gives valuation one, not two, at each
root; both eigenspaces occur, including at 2. The actual level
subgroup is the full prime-power cyclic \(\Omega\)-eigenkernel of
\((1+\beta)/2\), not an unmarked \(j\)-value match.

The maximal order embedding is optimal in the enhanced endomorphism
ring. [Cornut–Jetchev Cor. 4.1](https://webusers.imj-prg.fr/~christophe.cornut/papers/liftings.pdf#page=15)
applies to conductor one at the inert prime outside \(N\). The
normalized tangent sign in [Elkies–Ono–Yang, §3](https://people.math.wisc.edu/~tonghaiyang/deuring.pdf#page=7)
distinguishes the two conjugate embeddings. Indeed
\(\omega=(1+\sqrt{-455})/2=A\tau+(1+\beta)/2\) on a Heegner chart
with \(N\mid A\). Thus the marked level has the actual \(\beta\)
orientation. Its absolute seed class is not asserted or required.

At 29 root 2 is simple; at 5 and 7 repeated roots 3 and 4 give
rank-one nilpotents by the same degree test. Their transported
kernels give the actual prime ideals
\((29,\omega-2),(5,\omega-3),(7,\omega-4)\).
The endomorphism, chosen subgroup and prime-to-53 quotient
specialize compatibly along the same maps. The exact HNF schedule
uses each relative class once; an inverse Artin convention or a
seed shift merely permutes the complete unweighted trace.

The script aligns all classes' two basis pairings to the SAME
initial roots, then pushes both 19-entries through the 17-map within
each row (degree 17 on pairing). The common phase is
\(z_{17}^{19}z_{19}^{17}\), so the Gauss factors are \(21,4u\) and
\(s=31u\). The raw sum is \((21,31u)\) on \(E_{-1}\); applying
\(i_s(X,Y)=(-323X,s^3Y)\) gives \(S\bmod53=(1,25)\) on \(E_{323}\).
The checked \([224]\)-image is exactly \((42,42)\) of order 13.

## Literal rationality and nontorsion

For the signed translated map, conjugation of a \(\Gamma_0(N)\)
element by translations changes its unit slot by a square
\(a\mapsto a\delta^2\bmod323\); its character is unchanged. Its formal
\(q\)-parameter at the rational cusp changes by \(\zeta^a\).
Galois on the coefficients changes the weighted sum by \(\chi(k)\)
when \(\zeta\mapsto\zeta^k\), and the matched Gauss twist changes the
sign back. The q-expansion principle gives the map over \(\mathbf Q\).

The same evaluated low map satisfies \(\phi_0\circ W_{48}=-\phi_0+T\).
With \(C=2y-x^4-1\) in the [Colò chart](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf#page=266),
differentiate its literal quotient to obtain
\(\phi_0^*\omega=-(x^2+1)dx/C\).
Here \(W_{48}x=(x+1)/(x-1)\) and squaring forces
\(W_{48}C=\pm4C/(x-1)^4\). At the image of infinity \(x'=1\) and
\(t_{16}'=0\), so \(y'=3,C'=4\), fixing the plus sign.
The differential changes sign, and appending the two low-map values
is constant, as claimed.

For each unit \(a\), choose \(b\) with \(48ab\equiv-1\bmod323\).
Direct matrices give
\[
 T_a W_N=323\,\gamma W_{48}T_b,\qquad
 \gamma=\begin{pmatrix}(1+48ab)/323&a\\48b&323\end{pmatrix}\in\Gamma_0(48).
\]
Here \(\chi(b)=\chi(-48)\chi(a)=-\chi(a)\).
The low constant cancels because the character sums to zero, proving
that the literal twisted map is \(W_N\)-fixed. Complex conjugation
changes the level ideal to \(\overline{\mathfrak n}\); the dual kernel
after \(W_N\) gives the same conjugate ideal, since
\(\mathfrak n\overline{\mathfrak n}=(N)\). Hence conjugation permutes
the 20 \(W_N\)-translated inputs and fixes the true H/K trace.

The trace is thus rational. Good reduction at 5 has exactly four
points, so prime-to-5 torsion injection excludes rational 13-torsion;
the actual nonzero order-13 projection at 53 makes this trace
nontorsion. This argument already works over K since the prime
above 5 has residue field \(\mathbf F_5\). There is no claim for an
independently fixed parametrization, an old multiplier divisible by
13, other selected inputs, or native Lean.
