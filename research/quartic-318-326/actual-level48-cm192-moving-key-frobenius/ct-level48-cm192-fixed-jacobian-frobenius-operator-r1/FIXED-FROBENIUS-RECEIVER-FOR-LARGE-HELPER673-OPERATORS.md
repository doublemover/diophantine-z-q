# One fixed Jacobian $[2]$ receiver for the remaining helper-673 operators

The rigid parity product has a finite Galois carrier for the remaining operators. For a fixed helper $I$, it is independent of the moving size of the actual detector and keeps the exact framed character lattice. This is an arithmetic **reduction**: the $[2]$ carrier and the needed Frobenius elements have not been computed at $I=673$, and it asserts no mark.

## The exact fine-level curve and its torus

The frame $(Q_{32},V_2,Z_3)$ is equivalently a point $Q+Z$ of exact order 96 and an independent choice of the second 2-point $V$; both $Q,Z$ can be recovered by the corresponding coprime primary projections. Its geometric level is $H=\Gamma_1(96)\cap\Gamma(2)$. The determinant of its full congruence-subgroup stabilizer is surjective mod 96 (diagonal matrices $(1,d)$ with $d$ odd fix the first chosen point and the 2-frame), so this moduli curve is connected over $\mathbf Q$, without fixing a full Weil pairing. Let $X$ be the compactified $H\cap\Gamma_0(I)$ curve over $\mathbf Q$, and $A=\operatorname{Jac}(X)$.

At $I>3$, the Deligne–Rapoport model at that prime has two smooth geometric components given by the two degeneracy maps, meeting at the framed supersingular labels of the lower $H$-curve. The auxiliary level is prime to $I$ and the frame kills all elliptic automorphisms, so the supersingular nodes are the actual fine-level transverse nodes, not coarse stabilizer weights. One may obtain this version by imposing the same tame flag on the ordinary connected/étale and supersingular local charts. This is the familiar level-$\Gamma_0(I)$ two-component calculation in [Deligne–Rapoport and Raynaud's modular character-group construction, as used in Ribet §8](https://math.berkeley.edu/~ribet/Articles/motives.pdf). A model with extra cusp resolutions would have only rational dead-end chains there and the same torus; all required nodes are the supersingular ones.

Thus the dual graph has two vertices and all edges indexed by the exact set $\mathcal S_I$ of rigid frames. Orient each edge from the connected to the étale component. The character group of the special-fibre Néron torus $T$ is the rank-$\#\mathcal S_I-1$ lattice
$$
    X^0=\ker\big(\mathbf Z[\mathcal S_I]\xrightarrow{\text{sum}}\mathbf Z\big):
$$
this is also immediate by expressing line-bundle gluing as one nonzero scalar per node modulo the ratio of the two component scalars.

For $\ell\nmid 6I$ let $p_1,p_2$ be the maps from the degree-$\ell$ cyclic isogeny correspondence selecting its source and its quotient. Use the **transpose** Picard endomorphism $C_\ell=(p_1)_*p_2^*$ on $A$. On the special torus a pullback repeats an edge gluing factor, and a norm pushforward multiplies the factors over the target edge; the two components stay of the same types because the isogeny has prime-to-$I$ degree. Taking characters reverses these two functions. Consequently $C_\ell^*$ on $X^0$ is the outgoing adjacency $B_\ell:e_x\mapsto \sum_y (T_\ell)_{x,y}e_y$, the exact convention needed to advance a starting source delta under the ordered product. The maps are étale at the flagged nodes because $\ell$-subgroups are prime to $I$; their gluing multiplicities are one for each cyclic kernel.

## A finite generic $[2]$ realization, with no lost augmentation row

Work over the strict henselization at $I$. The special finite group $T[2]$ lifts canonically to a subspace $W$ of $A[2]$ over that unramified base: lift each point of $T[2]$ in the identity component of the Néron model using étaleness of multiplication by 2 and the zero section. Étaleness gives uniqueness in the specified special point, and specialization and uniqueness makes this identification compatible with all Néron-extended endomorphisms. Equivalently this is the toric step of Grothendieck's semistable filtration, [Ribet §7, (7.9) and the explanation immediately after it](https://math.berkeley.edu/~ribet/Articles/motives.pdf). We get a perfect pairing
$$
                W=\operatorname{Hom}(X^0/2X^0,\boldsymbol\mu_2).
$$
The required outgoing $B_\ell$ is dual to $C_\ell$ on $W$. The subspace $W$ depends on the chosen local embedding at $I$ and need not itself be stable under the **global** Galois group. Only the stated endomorphism preserves it.

The good-$\ell$ Eichler–Shimura relation can be read with exact orientation from the modular correspondence. With arithmetic Frobenius $F_\ell$ on the good reduction, its two characteristic-$\ell$ branches on the ordinary locus are $y=F_\ell(x)$ and $F_\ell(y)=d_\ell(x)$, where $d_\ell$ is the diamond multiplying the frame at 96 by $\ell$. The second equality follows by applying the dual of the separable isogeny, which is then relative Frobenius, and using dual composition $[\ell]$ on the original frame. Both graphs extend with multiplicity one in the tame-level correspondence (the standard Eichler–Shimura reduction). Thus on the **transpose** Jacobian correspondence the first branch is $F_\ell^*$, and the second is $(d_\ell^{-1})_*F_{\ell*}$. On generic $A[2]$, identified with its good reduction and arithmetic Frobenius, this reads
$$
        C_\ell\bmod2=F_\ell^{-1}+d_\ell^{-1}F_\ell
$$
since $F_\ell^*=\ell F_{\ell*}^{-1}$ and every permitted $\ell$ is odd. This formula makes sense on the *whole* torsion representation before restricting the sum to $W$; neither summand has to preserve that local subspace. Each $d_\ell$ depends only on $\ell\bmod96$ and is defined over $\mathbf Q$. Any Frobenius representative yields the same endomorphism sum: representatives conjugate it by the global action, which commutes with $C_\ell,d_\ell$.

Let $P=\mathbf Q(A[2],\zeta_{96})$. This is a fixed finite Galois field, unramified outside $2,3,I$. The finite certificate for a moving $\ell$ is now a certified Frobenius element in this field together with the finite precomputed comparison $W\simeq(X^0/2)^\vee$. It gives the operator on $X^0/2$ without listing the $\ell+1$ isogenies at every label. A complete fixed-level preload would have to exhibit the actual $[2]$ models, local toric comparison and diamond actions, not just the existence of a residual eigenform.

There is no missing Eisenstein-extension row in the stated algorithm. Every actual first-arm $n$ contains 17, and the separately computed $T_{17}$ on **all** frames has even row sum 18. Start each frame delta by this explicit $T_{17}$, landing in the full modulo-two augmentation kernel, identified with $X^0/2$ since the augmentation onto $\mathbf Z$ splits. The actual $T_I$ is the known Frobenius permutation and preserves that kernel. All subsequent odd-prime rows can be handled by the above operator restricted to $X^0/2$. Reordering prime factors is allowed by the unique prime-order filtration of their squarefree composed kernels. No value of a Hecke operator on the quotient is needed after the initial step.

For $I=673$ the framed graph has 344,064 states, so this finite field and its exact toric comparison cannot be treated as already computed or automatically small. The proved statement is a fixed-field representation of the missing arithmetic independent of the height of $n$, not a practical runtime guarantee, a compatible actual Frobenius selection, or a nonzero mark.
