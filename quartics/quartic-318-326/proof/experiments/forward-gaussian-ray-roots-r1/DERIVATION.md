# Signed Gaussian ray through actual quarter-order preparation

## Historical connection

Read the complete original receipts/completeness-work/BRANCH-CERTIFICATE.md, especially section 1, alongside the original BranchHalving statements used in the preceding packet. Its ordinary quadratic-reciprocity argument already proves the needed special quartic supplement. Historical justification is found; this packet incorporates that argument into the actual Lean producer and final preparation consumer. It does not call the previously unformalized connection a newly discovered mathematical gap.

The actual norm/ray inputs are p=a²+b² with signed integers a,b, a≡9 mod16 and b≡0 mod16. No positivity of a or b is assumed. These imply p≡1 mod16 and p>2. The absolute values |a| and |a+b| are positive and strictly less than p; the latter follows from (a+b)²≤2p and p>2. Both are odd. Since a and a+b are 1 mod8, either absolute value is 1 or7 mod8. The integer-to-field transitions retain all signs.

## 1. Both ordinary quadratic residues

For q=|a|, the exact norm equation gives p≡b² modq. The prime p is coprime to q because 0<q<p. Consequently its Jacobi symbol at q is either +1 or−1. Congruence and multiplicativity identify it with the square of the integer Jacobi symbol of b, which is nonnegative; hence it is +1. This formulation avoids introducing a separate unproved gcd(a,b) certificate while deriving the same conclusion as the historical proof.

For q=|a+b|, the exact identity 2p=(a+b)²+(a−b)² gives 2p≡(a−b)² modq. The supplementary law gives (2/q)=1 because q≡±1 mod8. As before, (p/q) is ±1 and equals a nonnegative symbol square, hence equals1. The generic helpers include q=1 using the ordinary Jacobi convention; no exceptional denominator was dropped.

The pinned reciprocity theorem has direction J(p|q)=J(q|p), since p≡1 mod4 and q is odd. Its reverse identifies the desired prime-denominator symbol with the proved value1. The Legendre/Jacobi identity and nonzero residue give a square in ZMod p. For negative a or a+b, multiply the square of the absolute value by the actual square −1, since p≡1 mod4. Thus the actual residues a and a+b, not merely their absolute values, are squares.

## 2. Precise quartic Euler condition and concrete finite roots

In ZMod p let i=b/a. The actual norm equation and nonzero a give i²=−1, i⁴=1 and (a+b)²=2a²i. Since p≡1 mod16, p/4=4(p/16), so i^(p/4)=1. Euler's criterion for the two actual nonzero squares gives a^(p/2)=(a+b)^(p/2)=1. Raising the exact identity to p/4 and using p/2=2(p/4) gives 2^(p/4)=1. These floor quotients equal the historical (p−1)/4 and (p−1)/2 under the explicit ray.

To produce t⁴=2, first use the ordinary supplementary criterion p≡1 mod8 to choose r²=2. The just-proved quartic Euler condition gives r^(p/2)=1, so Euler's criterion produces t²=r. Hence t⁴=2. No abstract finite-field generator or unproved cyclicity interface is used.

To produce z⁸=−1, first choose i²=−1 by p≡1 mod4. From i⁴=1 and 4|p/2, Euler produces j²=i. Then j⁸=1 and 8|p/2 produce z²=j. The exact successive-square identities yield z⁸=−1. Nonzero elements required by Euler are proved from their positive powers being1.

## 3. All original positions and same preparation object

GaussianData has domain Fin3×Fin5 and supplies the actual signed norm/ray representation of each positive source prime's natural absolute value. Values supplies primality. actual_roots produces precisely the former RootData at every original position. There is no reindexing or omission of repeated positions. Each z,t works for either original residue root of2, so arbitrary primary/opposite orientation choices are retained.

The preceding exact quotient theorem now gives the actual primary and opposite LCM moduli dividing the respective LCMs of the literal finite-curve counts divided by4. The original R, original formal subgroup and original model are unchanged. The quarter factor still comes from an actual half of R and four actual torsion classes, not merely divisibility of the full count.

The final gaussian_preparation_family first obtains the prior Q from the existing source preparation theorem. Later it takes u,w, the actual prime pattern, divisibility Q|w, the rational 1 mod408 ray, the fixed prior prime bound, the signed Gaussian data, arbitrary root orientations, and a single h. The congruences are h≡0 modulo Pi³ times the literal primary quarter-count LCM and h≡1 modulo the opposite quarter-count LCM, together with the original continuity modulus. The proved divisibility transports those SAME congruences to the actual quotient-order moduli. Original h≠0,1, fixed guard signs and real pole inequalities are retained, and the exact earlier family yields Prepared at the same a,labels,h,parameter and stored coordinates190/241/292.

## 4. Validation and retained boundaries

All four new sources use the finite 1M budget. The packet retains 213 exact predecessor files and all original polynomial inputs. Source-policy/dependency closure is checked separately from Lean elaboration. Exact signed finite controls test all four sign quadrants, both Jacobi denominators, actual quartic Euler and explicit root witnesses; p17 is a negative control showing p≡1 mod16 alone does not imply the fourth-root input. Inherited checks retain actual halving coordinates, signs, quarter-order tests and all original source-position identities. These computations are not a proof of universal prime-pattern existence or Lean kernel acceptance.

No existence of the simultaneous signed Gaussian prime pattern or compatible h is asserted. The literal CM count formula remains unproved here; this result deliberately works with actual finite-curve counts. Four rational Realizations and the global rational-anchor implication remain unchanged downstream inputs. Hosted elaboration, recursive axiom audit and independent source review are separate acceptance stages.
