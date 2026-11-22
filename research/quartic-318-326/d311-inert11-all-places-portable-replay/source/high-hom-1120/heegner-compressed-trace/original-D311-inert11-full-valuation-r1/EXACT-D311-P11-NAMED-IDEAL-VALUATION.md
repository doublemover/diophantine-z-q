# Full named good-prime valuation for the bounded fixed-241 control

For \(D=-311,\ f=241,\ n=241\cdot311\), the entire oriented valuation of the eight-packet CM ratio \(R\) at one named prime over 11 is
\[
                              v_{\mathfrak P}(R)=-20 .
\]
This is a complete local valuation for the bounded control, not the entire fractional ideal and not a computation on the original detector. It does not infer the independently measured residue at 29 from this one prime.

## 1. The named prime and all moving flags

Use the same actual fixed functions as in the corrected real calibration (c763e955), and the same maximal-order moving 19-cycle (e82fc6e6) and marked two-arc constants (f4835b82) at 11. Normalize \(v_{\mathfrak P}(11)=1\); all involved local extensions are unramified. In the basis \(1,s\) with \(s^2=2\bmod11\), the named roots are
\[
 \sqrt D=2s,\quad \sqrt{241}=4s,\quad
 \sqrt{-n}=5,\quad \sqrt5=4,\quad \sqrt6=5s .
\]
The ordered 16/3 eigenvalues of \(\alpha=(1+\sqrt D)/2\) are \(2,0\). Both calibration field and moving field are inert at 11. The residue symbols are the chosen place, not independent sign choices in each summand.

There are exactly nineteen moving source lattice classes, traversed once by the even horizontal 2-prime in the verified 19-cycle. This remains true even when coarse residue \(j\)'s or flags coincide: the indexed CM source classes are not identified. The conductor prime 241 is inert in the moving field. For each actual source, the target conductor-241 flags are the 242 cyclic subgroups of its 241-torsion, with actual induced ordered 16/3 marks. None is a horizontal moving eigenline. The proper-order class fibre has size
\[
 |(\mathcal O_K/241)^\times/(\mathbb Z/241)^\times|=242,
\]
with units already factored (both CM orders have only \(\{\pm1\}\)). This is exactly the same fibre indexed by the 242 projective lines in the computation; it is not an unrestricted residue point set. The sum processes all \(19\cdot242=4598\) lines once.

## 2. Mark transport and coherent signs

Start from the literal \(Q'\)-source in the two-arc proof with the two independent 241 generators from its calibration-horizontal lines. In their ordered basis the exact action of \(V=2\alpha-1\) has columns
\[
                 (167,129),\ (28,74)\pmod {241}.
\]
The checker obtains both columns by geometric torsion operations, not from the signed output table. Its Miller pairing has Gauss sum the named \(+4s\). Along the 2-ideal arrows, the transported 241 basis retains this same matrix; the change in Weil pairing is by the degree \(2^j\), whose Legendre symbol at 241 is positive. Thus for each line \((a,b)=(1,b)\) or \((0,1)\) the actual character is the Legendre symbol of the determinant of that line against its \(V\)-image in the transported basis. No determinant is zero. This agrees with both earlier \(-1\) components on \((1,0),(0,1)\) of the initial source. The exact sequence of 242 signs is the same on each vertex in these transported basis coordinates, not an assumption of independent local signs.

The same normalized degree-two isogenies transport the actual 3-line. The checker verifies \(\alpha\) kills its residue generator on each source. The full cyclic 16-line must be selected anew at each source: on geometric 16-torsion the roots are \(2,15\), with unit difference. Applying \(\alpha-15\) to a trial exact torsion point and retaining a primitive result selects the unique \(2\)-eigenline. The resulting point is checked to have exact order 16 and scalar action \(2\). The \(x\)-map for this calculation is carried by the exact quadratic-invariance descent of the canonical-cycle proof; its \(y\)-map follows by the constant named \(\alpha\) differential through the normalized separable arrows.

## 3. Arithmetic and complete local sum

For each source lift its three relevant groups using the unit-derivative torsion equations of the two-arc proof. In particular only two 241 basis generators are lifted per source. Use a mod-\(11^5\) unramified degree-96 extension for torsion and Vélu. Both lifts end in the exact designated residue discs and satisfy their torsion equations. Take each of the 242 generators, generate its 120 \(x\)-coordinates up to sign by an exact Jacobian-coordinate walk, invert the unit \(Z\)-coordinates in one batch, and compute the normalized Vélu quotient. The two quotient \(t_{16}\) coordinates recover the actual \(X,Y\) flag by Hensel using the curve equation and the first \(t_{16}\) map, with the second chart checked as well. On every arc the coordinate pair descends to the degree-two subring in \(1,s\). The first-start marked calibrated pair is independently compared in both coordinates and valuation against the earlier two-arc computation.

Evaluate the eight signed packets, all forty indexed seed occurrences, and all four Atkin factors for each occurrence at that point. The checker preserves their signs and counts valuations before taking the quotient. A degree-96 division is not needed for the fixed-product computation after descent; modular integer pairs suffice. This obtains an exact scalar \(v_{11}(\mathcal U(Q))\) for each arc, not a count of vanishing residue factors. All 160 factors per arc have valuation below 5; the histogram of **largest** factor depths across the 4598 arcs is
\[
                1:2976,\quad 2:1576,\quad 3:20,\quad 4:26 .
\]
Thus there is no unresolved precision cutoff. Summing by genus sign gives
\[
 \sum_{\chi=+1}v_{11}(\mathcal U(Q))=-10,\qquad
 \sum_{\chi=-1}v_{11}(\mathcal U(Q))=+10 .
\]
The ratio uses the difference, so its normalized oriented exponent is \(-20\). The scalar sum without signs is zero and does not recover the answer. The literal earlier diagonal subtotal \(-4\) is a different object: those two complete arcs contribute zero after other factors cancel their diagonals.

The attached row file preserves every projective line, resulting scalar valuation, phase sign and largest factor depth, in source order. Run sh verify.sh for checksums and a standalone recomputation of all signs and the total from the recorded table. Run sh verify.sh --all for the full geometry/depth replay with Python 3 and python-flint 0.9.0. Each isolated child computes and checks one complete vertex before emitting its exact JSON line; the wrapper compares all nineteen lines byte for byte. The observed prototype used about 17–18 seconds per vertex with four workers. Scope is only this declared coefficient place and this one prime of the bounded discriminant.
