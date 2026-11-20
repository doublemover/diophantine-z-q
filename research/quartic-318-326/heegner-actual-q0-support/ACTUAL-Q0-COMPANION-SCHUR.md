# Exact companion-only selector and incremental diagonal completion

This is a strengthening of the frozen four-bit paper calculation ef793d67…. It does not identify any new factor of the literal companion θ, choose the actual retained q₀, or produce a modular coefficient.

## Cancel the old β and I rows exactly

With the original deleted K^sharp, use order (B,I,J), where J is any list of actual θ primes retained from the full support. Keep the diagonals computed from the *full* θ as in r1. The matrix is
```
M = [ D  C  P ]
    [ Cᵗ 0  0 ]
    [ Q  0  H ] .
```
Here C has seven columns e_i+e_8, 1ᵗD1=1, and the correction λaᵗ is included in the B-column block, so Q can be arbitrary. In P the q column consists of [q/b] for b∈B and q∈J; its column sum is zero. Indeed ∏b=β≡1 mod4, so quadratic reciprocity gives Σ_b[q/b]=[β/q]=0 by the actual mutual-square property. The zero blocks on the I–J edges, including the λ correction on the I rows, are exactly the original selected conditions, not a choice of numerical I probes.

Let U be the old 15×15 upper-left block. It is invertible by the original argument: the second block row forces the B-vector to be constant, the sum of first block rows then kills that constant, and C is injective. Moreover each solution of U·(x,y)=(P_j,0) has x=0, by the same two equations since 1ᵗP_j=0. Thus (Q 0)U⁻¹(P;0)=0. Elimination gives the exact determinant identity det M=det H over 𝔽₂, for the full companion or any of its principal restrictions with actual original diagonals retained. It is independent of Q and doesn't require that P itself vanish.

The theta-only H at p≠r is H_pr=[r/p]. On the diagonal H_pp=[θ/p at p]+[q₀/p]; the β contribution and the I contribution to this row are both zero. There is no λ term in the theta-only block. For the four known primes, in their frozen order, and the bits (0,1,0,0), the true local data reduce to only:
```
1010
1110
0001
1100
```
Its determinant is 1 over 𝔽₂: expand along row 3, then the minor is rows (1,0,1), (1,1,1), (1,1,0), of determinant 1. This provides a four-row check independent of the 19×19 elimination. All local diagonals are from the exact same scalar unit data, not from the product of a partial θ.

## A deterministic completion as each new factor is verified

If a new actual θ prime p has odd δ valuation v, obtain the bit [θ/p at p] from the unit δ/p^v. This holds also for v>1: δ=θz² and z/p^((v−1)/2) is a unit, so its contribution is a square. Compute the directed edges u (existing rows, p column) and v′ (p row, existing columns) by actual Legendre symbols. With the old invertible H and fixed diagonal constant d=[θ/p at p], the enlarged block is
```
[ H   u       ]
[ v′  d+x     ],   x=[q₀/p].
```
Its determinant is det(H)·(d+x+v′H⁻¹u). Pick x=1+d+v′H⁻¹u. This makes the new matrix invertible while preserving every previously selected bit, even before knowing the remaining factors. Iterate independently of the old core, using a deterministic discovery order if desired. This is a cubic elimination procedure (maintaining the inverse) once the necessary individual local factors are supplied, not an exponential Boolean search.

It is still not a factorization method, a global split test, or an arithmetic selected q₀. The actual CRT uses the full finite support, and fixing m requires the actual additional θ primes to split there. A negative mod-13 coefficient remains a separate arithmetic test.
