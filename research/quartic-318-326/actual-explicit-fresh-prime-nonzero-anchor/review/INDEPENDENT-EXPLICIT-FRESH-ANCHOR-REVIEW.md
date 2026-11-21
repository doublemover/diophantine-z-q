# Independent review: a specified nonzero supersingular anchor at fresh movers

I verified the author manifest
**ab8225515cea008dcb5353bfa5f580b36dc03fc7e760ca1edc166253159d5851**
and the paper **b0ac597f04487ad241df611439125541a2113926d9a5cd7918d4f31bc4a2faa9**, including the author arithmetic replay
byte-for-byte. This is a proof of a marked value being nonzero,
not a determination of that value.

* The horizontal option is the true primitive oriented form
  \([N,B,C]=[205042530,399254240,399397441]\) of discriminant
  \(-3080\cdot7389223^2\). Independently checked \(B^2-4NC\),
  \(\gcd(N,B,C)=\gcd(N,7389223)=1\), and the specified seven CRT
  residues; \(770\cdot7389223^2-N^2=35,629,870,430>0\).
  On the actual lattice \(L=\mathbb Z+\tau\mathbb Z\),
  \(\beta=N\tau\) acts by \(\beta\tau=-B\tau-C\), \(\beta\cdot1=N\tau\).
  On \((a\tau+b)/N\bmod L\), its vanishing means \(N\mid aB,aC\);
  primitiveness implies \(a=0\bmod N\). Thus the marked subgroup
  really is \(E[(N,\beta)]=\langle1/N\rangle\).
  The ideal is prime to the fixed conductor and invertible; the
  quotient of \(\mathbb Z[\beta]\) by \((N,\beta)\) has order \(N\).
  The simpler \(\sqrt{-770}\) option is a genuine cyclically marked
  point but need not be horizontal.
* At either chosen upper-half-plane point the imaginary part exceeds
  1, so the width-one q has absolute value below \(1/100\).
  Good-prime Hecke recurrences with Weil magnitude, the squarefree
  multiplicative bad-prime recurrences, and multiplicativity give
  \(|a_n|\le d(n)\sqrt n\le n^2\). Independently summing the ordinary
  power series gives the tail \(39701/970299<1\) for \(f_N/q-1\).
  Hence the **actual normalized** newform is nonzero at the specified
  characteristic-zero marked point. Comparison of complex differentials
  only uses a nonzero scale. The algebraic value is the algebraic
  weight-two section evaluated in a chosen algebraic Hodge frame; no
  assertion about algebraicity of analytic periods is involved.
* For both unchanged individual mover phase columns,
  \((-1,2,5,7,11)\) have symbols \((+,+,+,-,+)\); thus the prime is
  inert in \(\mathbb Q(\sqrt{-770})\). The detachment of 11/2399
  changes only order/Gaussian layers and retains the rational norm
  class. Removing the finitely many rational primes below bad model,
  frame and value places gives good étale cyclic reduction and
  nonzero residual evaluation throughout, with no splitting requirement
  in the field of definition of the fixed anchor. The prior actual
  Gaussian ray/two-tail selector can take every fresh prime arbitrarily
  large and avoid this finite set without adding any phase condition.
  This works at all four movers in the all-fresh branch, and at the
  fresh choices only in the branch with the historical fixed 415721.

This is compatible with the independently forced supersingular zero
from \(w_{770}\): the fixed nonzero anchor is not asserted to be that
fixed critical point. The marked CM field here is a construction for
an anchor, not the selected genus trace's field. No relation to that
trace, no full ramified jet, no saturation and no PointPair follow.

Signed: independent reviewer, 2026-11-21 UTC.
