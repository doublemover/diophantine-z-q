# The original helper parity is a product of rigid marked Hecke operators

Fix the actual first selected detector arm and one literal old helper $I$ with $I\mid n$, $I\equiv1\bmod24$ and $(17/I)=-1$. Write $D=-n$ fundamental, $n$ positive odd squarefree and prime to 3. Keep the **same** level $48$ orbit and the single-helper quartic residue criterion. For each supersingular reduced flag its required multiplicity modulo two is an entry of a product of finite rigid Hecke matrices at the prime factors of $n$. This eliminates enumeration of CM classes and of trace-zero norm representations at the large integer $n$. A producer for the matrices at large primes is a separate step.

## 1. A small rigid frame and its exact norm congruences

Work geometrically over $\overline{\mathbf F}_I$. A given reduced level-48 flag is an elliptic curve $A$ with cyclic subgroups $C_{16},C_3$. Choose one point $Q$ of exact order 32 such that $2Q$ generates $C_{16}$; choose $V\in A[2]$ independent of $16Q$, and a generator $Z$ of $C_3$. The triple $(Q,V,Z)$ is the frame. An automorphism fixing this frame is the identity: a nonidentity automorphism fixing $Q$ would make $\rho-1$ kill a group of order 32, while every nonidentity elliptic automorphism in characteristic $I>3$ has $0<\deg(\rho-1)\le4$.

Let $\omega_D=(1+\sqrt D)/2$. Write its actual chosen level eigenvalues as $r_2\bmod16$ and $r_3\bmod3$. The target frame on the **same** curve is
$$
             (L_2 Q,V,L_3 Z),\qquad
             L_2=2r_2-1\bmod32,\quad L_3=2r_3-1\bmod3 .
$$
Both $L_2,L_3$ are units, and their squares equal $D$ modulo 32 and 3 respectively. At 2 this follows by multiplying the minimal polynomial equation of $r_2\bmod16$ by four; it even gives the same square modulo 64 for any lift of $r_2$. Since $L_2$ is odd the induced basis $16Q,V$ of $A[2]$ is unchanged.

Consider the finite set of **actual morphisms** $u:A\to A$ of degree $n$ sending the given source frame to this target frame. Its elements need not have trace zero. On this set the involution
$$
                           u\longmapsto-\widehat u
$$
is well-defined, where $\widehat u$ is the dual isogeny for the canonical principal polarization on $A$. Indeed on the two selected generators the new actions are $-n/L_2\bmod32$ and $-n/L_3\bmod3$, equal to $L_2,L_3$ using $L_i^2\equiv-n$. On the full 2-division $u$ acts as 1 and so does $-\widehat u$, because $n$ is odd. Applying twice returns $u$.

The fixed morphisms are exactly those of trace zero: $u+\widehat u=[\operatorname{Trd}u]$ in the elliptic quaternion endomorphism algebra. For such a map $u^2=[-n]$. Moreover $(1+u)/2$ is integral precisely because $1+u$ kills the full 2-torsion and hence factors through $[2]$. Its action on $2Q$ is $(1+u)Q=r_2(2Q)$, which is the genuine degree-16 level eigenvalue rather than a weaker mod-eight test. At $Z$ the eigenvalue is $r_3$, since 2 is invertible on 3-torsion. Conversely an integral $\omega_D$ with these exact eigenvalues gives $u=2\omega_D-1$ in the prescribed morphism set: it fixes the 2-division, and $uQ=2\omega_D Q-Q=\omega_D(2Q)-Q=L_2 Q$. This equivalence holds for any choice of frame lifting the given flag.

As $D$ is fundamental this is an optimal embedding; the orientation of the cyclic subgroups is exactly the selected one. At $I\mid D$ there is only the ramified tangent normalization (both roots of $\sqrt D$ reduce to zero), so no additional residue sign filters the fixed points. By the actual marked normalized Deuring correspondence the count of the fixed morphisms is precisely the indexed CM multiplicity $r(q)$ at this flag. The only automorphisms of the coarser flag are the central $\{\pm1\}$, which conjugate an embedding trivially. Thus counting the fixed **signed** morphisms does not double count an embedding or call for division by a unit-group size. In particular the involution argument reads $r(q)\bmod2$ as the parity of the whole prescribed morphism set.

## 2. Factor the whole morphism set by degree

Let $\mathcal S_I$ be the finite set of geometric isomorphism classes of $(A,Q,V,Z)$ with $A$ supersingular, and with the exact frame conditions above. For each rational prime $\ell\nmid6$ define an adjacency matrix $T_\ell$ on $\mathcal S_I$: for source $x$ and target $y$ count the degree-$\ell$ subgroup schemes in $A_x$ whose quotient with the pushed-forward frame has class $y$. For $\ell\ne I$ these are the $\ell+1$ cyclic lines of the ordinary étale $\ell$-torsion. For $\ell=I$, every supersingular degree-$I$ isogeny is inseparable because the curve has no étale $I$-subgroup, and hence has the unique relative Frobenius kernel. Here $T_I$ is the Frobenius permutation on rigid frame classes (with every point pushed through the relative Frobenius map). This is **not** an $\ell+1$ line count in characteristic $I$.

For distinct $\ell_1,\ldots,\ell_j$, paths in $T_{\ell_1}\cdots T_{\ell_j}$ count the degree-$\prod\ell_i$ kernels with prescribed pushed-forward frame. In one direction compose the quotient maps. In the other direction a finite subgroup scheme of squarefree order decomposes into its coprime primary subgroup schemes, and so has a unique filtration in the specified prime order. This holds for the inseparable primary part too, by the coprime decomposition for finite commutative group schemes. At every intermediate vertex two chosen representatives of its **framed** quotient have a unique compatible isomorphism, so paths neither depend on arbitrary model identifications nor silently divide by automorphisms. At the target with the specified frame on the same $A$, that unique framed isomorphism turns each counted kernel into exactly one actual $A\to A$ morphism. Conversely each such morphism gives its kernel and the same unique final identification. Thus this remains valid for a path that returns to the same underlying unframed curve but a specified different frame.

Writing $x=[A,Q,V,Z]$ and $x'=[A,L_2Q,V,L_3Z]$, we obtain the exact formula, finishing with the ordinary unsigned supersingular weights of the helper receiver:
$$
             r(q)\equiv \left(\prod_{\ell\mid n}T_\ell\right)_{x,x'}
                   \pmod2 .
$$
The prime factors of the actual first arm are already the genuine contact primes, 17, the selected helpers and the shared final prime, not the possibly unknown factorization of the companion. The formula does not assume that the matrices for these large primes are known, give a time bound for constructing them, or evaluate the mark. It shows that a matrix coefficient on one fixed geometric state space replaces the primitive norm-representation count at the product $n$. No rational point follows before the actual coefficient is shown nonzero.
