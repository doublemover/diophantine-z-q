# One regular scalar separates all six finite Atkin aliases

Signed: Vesper. 2026-11-21 UTC.

This is on the same good characteristic-13 modular curve
X₀(205042530), its full Atkin quotient Z, and Hom's exact
2,400-marked slice in manifest
`0feb0ab7e157c9e1c8d952ddc8bc9aaf78900e176360e3b8a46a4af10d265303`.
The six aliases there are identifications by the 127 normalized
discriminant characters, not geometric identifications. All
geometry below is bound to that actual maximal order and its
marked quotient circuits.

Use the **plain discriminator** versions V₁,V₂ of the all-negative
and flip-2 pair (negative sign masks 127,126) in the exact
two-coordinate proof `cbb41d8db7a9579e4a2f655a3427a28e7ca5c4243c8f6f89db1abbf15ece5f7d`.
They are regular away from the one quotient cusp. Set
```
          S(X) = sum_{Y in T_23(X)} (V₁(Y)+V₂(Y)).
```
Count all cyclic degree-23 kernels with multiplicities. This
is the *weight-zero trace* of a scalar function along the tame
correspondence, not a weight-two row or the cubic target value.
The two correspondence maps are finite, and their noncuspidal
fibres stay noncuspidal; the pushforward is therefore regular
there. The good correspondence commutes with the seven
Atkin operators by quotienting the coprime subgroup orders
in either order. Since V₁,V₂ are invariant, S descends to
a rational function on Z, regular at the tested points.
No arbitrary choice of eta root is made.

The exact replay takes twelve existing marked labels, verifies
each of the 24 actual norm-23 maps has a different cyclic
kernel at 23, and transports the literal tame marks through
each one to read both scalars on its normalized target.
The previously unresolved pairs, followed by their values
of S in the same order modulo 13, are:
```
 521,1601       7,  8
 769,2129       8,  5
 847,1768       8,  9
 902,1594       0, 10
1125,1239       9,  6
1370,1407      11,  4
```
Thus the old 127 discriminant-character tuple plus this
single genuine scalar separates all 2,400 distinct W-orbits
on the controlled slice. It does not mean V₁,V₂ plus S alone
separate that slice, or that any of these separate the
whole special fibre. No global plane equation, normalization
model, actual R value, selected CM readout or point is
part of this result.

```sh
python3 -B check_good23_scalar_separates_aliases.py /path/to/check_sparse_atkin_13.py /path/to/EXACT-FULL-LAST-SLICE-13.json | cmp - EXACT-GOOD23-ALIAS-SEPARATION.json
sha256sum -c SHA256SUMS
```
