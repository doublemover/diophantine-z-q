# The actual Abel map supplies the centered identity-chart derivative

Let $X$ be the original smooth proper curve, the same compact normalization identified with the filled fine modular curve in the reviewed compact comparison. Fix the same ordered differential frame $\omega_i$ already used for the rational Kähler coefficients and the complex period columns. Let $a_X:X\to J_X$ be the algebraic Abel map with its original basepoint. Write $a(\tau)=a_X(x(\tau))$, where $x$ is the actual parametrization on the upper half-plane through that compact comparison.

## Normalize any genuine chart, without prescribing a logarithm

The pullback of invariant forms by $a_X$ is an isomorphism onto the regular differentials of $X$. Use it to choose the **unique** invariant $\eta_i$ such that $a_X^*\eta_i=\omega_i$. Let

$$
E:T_0J_X(\mathbb C)\longrightarrow V=\mathbb C^g,
\qquad v\longmapsto(\eta_i(0)(v))_i .
$$

It is an isomorphism. Identify the source of the actual exponential with $V$ by this $E$; thus $q=\exp_{J_X}\circ E^{-1}$. The target retains the actual complex manifold topology, without assuming a topology transported from a second torus.

Choose **any** holomorphic chart $u$ of this manifold at its identity, with injective coordinate map on an open neighborhood $W$. Let $D=du_0$ and define, on $W$,

$$
\chi(y)=E D^{-1}\bigl(u(y)-u(0)\bigr).
$$

This is still a chart about $0$, with $\chi(0)=0$, $d\chi_0=E$, and
$d(\chi q)_0=E\,d(\exp)_0\,E^{-1}=1_V$. It may be extended arbitrarily off $W$; its germ and the germ of $\chi q$ at 0 are independent of that extension. The chart composition is holomorphic near 0, hence continuously differentiable there; in finite-dimensional complex coordinates its derivative at 0 is also the strict derivative. This supplies precisely the identity strict derivative used by the inverse function theorem, without requiring that $\chi$ already be an inverse of $q$.

## Translating the Abel map computes the required derivative

For each fixed $z\in\mathfrak H$, the actual map $w\mapsto a(w)-a(z)$ sends $z$ to $0$ and lands in $W$ for $w$ sufficiently near $z$. Its derivative followed by $d\chi_0$ is

$$
\begin{aligned}
d_w[\chi(a(w)-a(z))]_{w=z}(1)
 &= E\,d(T_{-a(z)})_{a(z)}\bigl(da_z(1)\bigr)\\
 &= \bigl(\eta_i(a(z))(da_z(1))\bigr)_i\\
 &= \bigl(\omega_i(x(z))(dx_z(1))\bigr)_i .
\end{aligned}
$$

The middle equality is exactly translation invariance of the same $\eta_i$, with translation by $-a(z)$. Pullback, rather than a comparison with another torus, is the last equality.

On the genuine ordinary arithmetic chart the rational comparison identifies

$$
\omega_i(x(z))(dx_z(1))=\operatorname{ev}_z(c_i)J'(z)=f_i(z).
$$

Here the map $\operatorname{ev}_z$ is the literal simultaneous specialization of the base generator and the selected monic root; $c_i$ is the coefficient in the same $dJ$-frame. The exact hosted readout computes the derivative without dividing by $J'$. At the finite omitted elliptic values use the actual fine-level parametrization and the canonical differential, not a claim that $dJ$ remains a generator: both $x^*\omega_i$ and the weight-two holomorphic differential $f_i(z)dz$ are defined on all of $\mathfrak H$ and already agree on the dense ordinary locus, so their coefficients agree everywhere. This includes the basepoint used to normalize the period primitive, whether or not its coarse $J$-value is ordinary.

In particular the same functions that occur in the ordered period/Gram matrix satisfy the **pre-logarithm** equation

$$
d_w[\chi(a(w)-a(z))]_{w=z}=(f_i(z))_i.
$$

No lift of $a$, chosen periods, or period-vanishing hypothesis was used to prove it.

## Construct the lift and identify the target

The analytic inverse function theorem applied to $\chi q$ at $0$ gives a local inverse $e^{-1}$. For a center $z_0$, choose any $v_0$ with $q(v_0)=a(z_0)$ by surjectivity of that actual exponential. On a sufficiently small disk put

$$
L(w)=v_0+e^{-1}\bigl(\chi(a(w)-a(z_0))\bigr).
$$

Shrink so both $q(e^{-1}(\chi(a(w)-a(z_0))))$ and $a(w)-a(z_0)$ lie in the chart $W$. They have the same coordinate by the inverse identity, so they are literally equal in $J_X(\mathbb C)$. Thus $qL=a$ on the disk. For **each** $z$ on that single disk, sufficiently near $z$ the increment $L(w)-L(z)$ lies in the same inverse neighborhood at zero and satisfies

$$
L(w)-L(z)=e^{-1}\bigl(\chi(a(w)-a(z))\bigr).
$$

Differentiating and using $d(e^{-1})_0=1_V$ proves $L'(z)=(f_i(z))_i$ throughout the disk. Different choices of $v_0$ differ by an element of the actual kernel, so do not affect this derivative.

The exact normalized primitive on $\mathfrak H$ consequently differs from these lifts by a constant on overlaps. Pushing to the actual $J_X$ gives the global identity with $a(\tau)-a(i)$ by continuity and connectedness. At $\gamma i$ it gives $q(\Phi(\gamma i))=0$, since $a$ is a map on the actual quotient. This removes the exact period-zero input with the same unchanged $q$. A separate integral comparison identifies the full period image with $\ker q$; that comparison, not real span alone, licenses writing $V/\Lambda$ for the same $J_X$.

## Provenance and scope

* [Milne, Jacobian Varieties, Proposition 2.2](https://jmilne.org/math/xnotes/JVs.pdf#page=6): actual invariant-form pullback by the algebraic Abel map.
* [Milne, Abelian Varieties, Proposition 2.1](https://www.jmilne.org/math/CourseNotes/AV.pdf#page=16): the exponential of the actual analytic abelian variety and its full lattice kernel.
* The accompanying provenance binds the reviewed original compact normalization, ordered rational frame, same-J period/Haar comparison, the strict green native chart readout, and the source-only local inverse/period consumer.
* This is a mathematical proof using the actual classical complex analytification and the actual algebraic Jacobian. It does not claim those constructions are implemented in Lean, that the chosen arithmetic center is globally regular, or that $J_X$ is the QM surface of the other direction.
