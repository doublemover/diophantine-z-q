# A shared final prime retains the two Selmer eights under a detector split

This is a paper extension of the actual linear-\(q\) marked Selmer selection. It applies to any of the original three detector Ready poles after fixing its literal \(b\), so neither its common preparation index nor its companion class changes. It uses new helper choices; it does not preserve a previously fixed final prime or prove rank.

## 1. Exact statement

Fix one actual detector. Let \(\beta=[17b]\), \(\theta=[1-b/17]\), the positive squarefree representatives. The established original detector profile is \(\beta=17p_0p_1p_2p_3p_4q\), with the six auxiliary contact/denominator primes \(1\bmod408\). The Ready hypotheses imply \(\theta\equiv1\bmod24\), \((\beta,\theta)=1\), \((\theta/p)=1\) at each \(p\mid\beta\), and \((\beta/t)=1\) at each \(t\mid\theta\).

For **any** partition \(\theta=uv\) into positive squarefree factors, one may choose a shared final prime \(q_0\), the same three/four type-one helpers \(I_j\) as in the original two phases, and at most one additional shared repair prime \(r\), such that the two twists
\[
  n_1=\beta q_0\Big(\prod I_j\Big)ru,\qquad
  n_2=\beta q_0\Big(\prod I_j\Big)rv
\]
have full \(2\)-Selmer groups of cardinality eight and the literal mark \((\beta,1)\) in \((x+3n,x-n)\) coordinates. Both are positive and squarefree, \(11\bmod12\); their root numbers are \(-1\) and their conductors \(48n_i^2\). We may take \(r=1\) if \(u\) is locally square at \(2,3\) and the primes of \(\beta\). The same conclusion then applies to \(v\) at those places. The relative character between the two twists remains exactly \(\theta\), not an independently selected companion. The primes being selected can avoid an arbitrary finite set and \(q_0\) can exceed any threshold.

## 2. Proof with no repair prime

Use the published 3/4-helper incidence patterns, with the additional CRT conditions that each helper be square at every prime of \(\theta\) and conversely. The latter direction follows from reciprocity because the helpers are \(1\bmod24\). Keep the old \(q_0\) symbols on \(\beta\) and the helpers, and keep the old \(7\bmod12\) condition (a chosen refinement to 7 or 19 modulo 24 is also allowed). For the old indexed support define \(\lambda_p=(3/p)\) in binary notation, \(a=e_{17}+e_{q_0}\), and the published sharp matrix \(L+\lambda a^{\mathsf T}\), with row and column \(q_0\) deleted. Its common old core \(C\) is invertible in either detector phase.

Extend the finite index separately by \(\operatorname{supp}(u)\) and \(\operatorname{supp}(v)\). On each old \(\beta\) row the new sum of binary incidences with the side is zero, by the stated local-square condition and \((\theta/p)=1\); on a helper row the sum is zero by choice. Thus the actual old block of each final matrix is \(C\), including its diagonals. All its off-diagonal entries, \(\lambda\), and the old entries of \(a\) are untouched.

Fix the primes of both side blocks first. Appending any vertex to an invertible block \(D\), with new off-diagonal column \(x\) and row \(y\), requires diagonal \(1+yD^{-1}x\) for Schur complement one. Here each new diagonal is freely toggled by the individual residue symbol \((q_0/t)\) of its vertex, with no other entry of the deleted core controlled by that symbol. Choose the bits on each side in this order. The sets of vertices are disjoint, so all chosen bits, the old \(q_0\) symbols and its type can be imposed on a single \(q_0\) by CRT and Dirichlet. The construction does not require symmetry of the extended matrix.

## 3. Repair for an arbitrary split

If needed, first choose \(r\) outside the fixed support by
\[
 r\equiv u^{-1}\pmod{24\beta},\qquad (r/t)=+1\quad(t\mid\theta).
\]
These conditions use coprime moduli, so allow a prime in one CRT class. In particular \(ru\equiv rv\equiv1\bmod24\). Choose the old helpers next, now also with both signs \(+1\) against \(r\). At any old \(\beta\) row the effect of the \(r\) symbol cancels that of either side, because their product has square character. Thus \(C\) is still the actual restriction on each side. Moreover \((\beta/r)=+1\): the unsigned positive \(\beta\) is \(1\bmod4\), so reciprocity and the inverse residue condition give \((\beta/r)=(r/\beta)=(u/\beta)=(\beta/u)=+1\).

All new off-diagonal entries to and from the common vertex \(r\) and the old core are identical on the two sides. The two \(r\)-diagonals, before selecting the common \((q_0/r)\) bit, differ by the sum of incidences from all of \(\theta\), namely the binary form of \((\theta/r)\). This is zero: \((r/t)=+1\) for every \(t\mid\theta\) and \(\theta\equiv1\bmod4\). Individual opposite-direction symbols \((t/r)\) need not be positive. The two old-plus-\(r\) principal submatrices hence have the same \(r\) pivot problem. Select the single bit \((q_0/r)\) by the Schur law before appending either side, then select the disjoint side bits independently as above. This gives one final \(q_0\), not two unrelated \(q_0\)'s.

## 4. Actual finite and local endpoint

In both cases the \(\beta\) indicator remains in the kernel of the full \(L\): old \(\beta\) rows retain the same diagonal and all \(\beta\)-columns; old other rows have no indicator at their own diagonal and their incidences with the \(\beta\)-support are unchanged. The \(q_0\) row also has zero indicator at its own diagonal, with its old directed symbols on \(\beta\) unchanged by reciprocity. Each side row has \((\beta/t)=+1\); the repair row has \((\beta/r)=+1\). The same \(a\) has sum zero, \(\langle a,\beta\rangle=1\), and is zero at every newly added index. Both members meet the exact residue condition; all primes are distinct and prime to 12. The two deleted sharp matrices are units by the preceding Schur proofs. These are the actual hypotheses of \(\mathsf{ActualTwoDescentFiniteConclusion318.actual\_finite\_conclusion}\), with the common \(q_0\) at the deleted \(\mathsf{none}\) position. Apply the published actual all-place interpretation and \(\mathsf{actual\_all\_places\_card\_eight}\) separately, retaining the same \(\beta\) indicator and its 17 and \(q_0\) entries. No conclusion about rational-point infinitude follows from this argument.

One can choose a split with much smaller \(\max(u,v)\) than \(\theta\), and the exact level formula is \(48(\beta q_0(\prod I_j)r)^2\max(u,v)^2\). In particular, without repair the \(\theta\) contribution to the pair maximum is reduced at fixed common part. Neither Dirichlet choice supplies a bound making the **absolute** conductor smaller than that of another previously chosen \(q_0\), and there is no such guarantee when \(r\) is too large. This is a stronger existence result than local mark transport for an already fixed pair; it is not a small conductor certificate or either derivative nonvanishing.

## Dependencies and replay

- *Companion Theta Paired Selection*, SHA-256 `21c692023d5085335ff0ff4a31a943906acd27dc44549560fe63e2f86431fd9f`: actual profile, old core and native hypotheses.
- `ActualTwoDescentFiniteConclusion318.lean`, SHA-256 `0753c3110ab20907e1391cd8dc6682da893c39fccf749be7b8f4c2e35ae409df`, and `ActualTwoDescentAllPlacesExactCardinality318.lean`, SHA-256 `d67a8a60e7e61be4807eca5397cb8c3236a36b2d5f7100044fed6b3031a29f85`.
- *Original Conductor Floor and Balanced Detector*, SHA-256 `4e24e31bd32c55e52caad81aaa2bf5e42cf2776e8aef3e34289d5d505b0d243d`: level formulas, already-fixed-pair transport and binary signature balancing.

The finite control tests both published deleted cores with asymmetric Schur fixtures. The small arithmetic control uses \(\beta=17\cdot73,\ u=7,\ v=31,\ r=63823\): both opposite-direction symbols on the \(r\) row are \(-1\) although each prescribed \((r/t)\) is \(+1\). It is a reciprocity fixture, not an original detector. No numerical \(b\) or hidden support is asserted.

    python3 -B replay_balanced_schur.py | cmp - EXACT-BALANCED-SCHUR.json
    sha256sum -c SHA256SUMS
