# Independent review: two exact receivers for the actual zero-ordinate boundary

Disposition: **PASS, exact conditional tests, not an evaluated obstruction**.

Exact author material:

- Positive aggregate norm admission **r2**: SHA256SUMS
  `aed5416b0de2838373cfb09648f6820c480c2fedef6c3285b6b5948759817ca3`;
  manuscript `2e58b9b74490eed5acbc6495d6a3e4887575013f1b1a04342f8c041295b53a52`;
  executable `f052501940d10175742da0c1fee3dff728aa3a6205c941ef469e1b3e4325a69b`;
  JSON `074914ceccfaade8e5953d1cd86f62062fe9c7b03ca944ea74fcb12cdc53f272`.
- Negative first-isogeny row **r1**: SHA256SUMS
  `958a9351c6f4cf94c71208484bdff56f1de657fc2c5d5ab62391228e2d1a266b`;
  manuscript `74da1c8ca50e64af094a4b739bcdf5f3111122c985a27d10e38ac6b4b814c5ca`;
  executable `28af7afe8503e7bda51986a84314f44c535d246780304f441789acfa2dacfb00`;
  JSON `09aba829d707ab7a65bc0c2402fc4bfb8dad2248ee806d981596cd5eb398232c`.

Both exact author replays reproduce their sealed JSON byte for byte.

**Positive row.** The two product relations at the unknown odd primes
use the actual whole unseen factor U. On aggregate-supported r and s,
the U factors cancel against the full torsion local classes before
products are taken; the diagonal contribution from beta times the
visible product T remains. Quadratic reciprocity then gives the
necessary aggregate kernel of dimension 4 in the stated 28 columns,
not a dimension bound for the unrestricted Selmer group. For each
fixed test combination, the two Hilbert symbols with
`D*=delta/(T*1186981)` are locally trivial exactly when the remaining
prime-by-prime admission holds. At the fixed places the ratio U/1186981
is square, at 1186981 both quadratic test fields split, and at each
unknown odd theta prime the two residues are exactly the required
quadratic characters. Independent x-only arithmetic on the pinned
original source checks the auxiliary reduction annihilator and
reproduces W=121437, c=322463, delta=557122. The two rational norm
equations are the precise admission test; none has been solved here.

A negative pairing of the chosen full mark alone does not exclude
the positive first-coordinate quartic. Its possible competitors
differ by a pure second class `(1,s,s)`. I checked the split-minus-three
support condition, the separate dyadic restriction, and the exact
quadratic norm criterion with right-hand side `-beta*delta/s).
The five fixed eligible columns give no extra class. Thus uniqueness
holds if there is no new split-minus-three theta prime, or under the
different one-unseen hypothesis, neither of which was verified for
the actual scalar.

**Negative row.** At 2 only unit classes 1 and 5 occur: nonzero depths
are even, and for x=3+4k the remaining square test is 5 modulo 8 for
both k parities and fails. The odd torsion local quotients and the
untwisted reciprocal split test match the stated signed support.
Use the genuine first-isogeny pushout on the negative quartic.
At a theta prime, the square beta and nonzero derivative allow an
actual point sufficiently close to t squared equal to beta, so the
function has square class there. At fixed old places its class is
3 beta; reciprocity yields exactly the product of (3/p) over the
selected odd theta support. Extension to Q(sqrt(-3)) kills the
nonsplit-place symbols and leaves exactly the prescribed split-place
admission equations. The standalone same-beta control checks a
nonzero sign only for its own negative boundary, not the linked
scalar. No actual negative test or sign is exhibited.

The two receivers do not assert an actual norm solution, Cassels
sign, rank bound, rational point, or rejection of a different chart.
No Lean run.

Signed: independent proof and source review, 2026-11-21.
