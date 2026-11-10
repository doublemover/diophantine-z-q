# Literal point counts through the actual conjugate twist

## Historical route and exact boundary

Read the original Version10 two-reductions lemma and proof at quartic_v10.tex lines11138–11165, as well as the full prime-pattern audit and branch certificate. The historical argument first proves opposite square classes from(7/p)=−1, then identifies Gaussian Frobenius through the order-four automorphism, integrality and Gaussian unique factorization. This packet incorporates the FIRST part by direct finite-coordinate counting and consumes its result in the actual orientation/index producer. It does not claim to have proved the later Frobenius-integrality or unique-factorization identification. Historical justification is present; the full CM producer remains partly incorporated.

## 1. Count the exact original affine carrier

For a finite field F and coefficient D, Curve D is the literal subtype of pairs(x,y) satisfying y²=x³−Dx. An explicit equivalence sends that pair to the dependent fiber(x,{y | y²=x³−Dx}) and back. This preserves both coordinates and the original equation. Cardinality of the dependent sum gives the sum of ordinate-fiber cardinalities.

The pinned quadraticChar_card_sqrts theorem applies in characteristic different from2 and includes zero, nonzero squares and nonsquares. Its finite-set cardinality is converted through Set.toFinset_card and Nat.card_eq_fintype_card to precisely the subtype cardinality used here. Including infinity yields

count(D)=|F|+1+sum_x chi(x³−Dx)

as an integer equality. No elliptic group cardinality or Frobenius trace is presumed. The identity also handles D=0 as a finite affine equation; later actual models are the original nondegenerate coefficients.

## 2. Actual quadratic-twist coordinate change

For nonzero c, construct the literal bijection x↦cx with inverse c⁻¹x. The exact polynomial identity is

(cx)³−Dc²(cx)=c³(x³−Dx).

Equiv.sum_comp reindexes the full finite field, not a restricted subset. Multiplicativity of the quadratic character and chi(c)=−1 give the negative character sum. The count formula then proves count(D)+count(Dc²)=2(|F|+1).

For the original rho²=2, set c=(3+rho)/(3−rho). The actual product(3−rho)(3+rho)=7 and chi(7)=−1 imply7 and both factors are nonzero. The coefficient identity(3−rho)²c²=(3+rho)² is exact. Also c(3−rho)²=7. Since the second factor is a nonzero square, applying chi gives chi(c)=−1. Thus the literal original conjugate coefficients have opposite character sums and complementary counts. No unnamed twist-isomorphism or arbitrary curve with the same j is substituted.

## 3. Character7 from the actual signed ray

The Gaussian mod7 ray a≡1,b≡3 gives p=a²+b²≡3 mod7. The mod16 ray gives p≡1 mod4. Ordinary Jacobi reciprocity has direction J(p|7)=J(7|p). Congruence identifies the left side with J(3|7). A complete seven-element check proves3 is not square in ZMod7; the pinned Legendre/Jacobi identities therefore give J(3|7)=−1. This proves the exact quadratic character of7 in ZMod p is−1.

Both Gaussian rays matter. The rational1 mod408 ray alone is not used as a substitute for the mod7 condition. The finite negative control p337 has the mod16 property but character7=+1; its two literal counts are356 and356, which do not sum to2(337+1).

## 4. Actual residue-root and count identity

The p-adic integral representatives of rho and−rho are negatives by subtype extensionality. Applying the actual PadicInt.toZMod map proves residueRoot(−rho)=−residueRoot(rho), including the original root proof and embedding choice. The original pointCount definition is literally1 plus the cardinality of the same finite pair subtype, so the generic count theorem applies without a curve replacement. It yields

pointCount(rho)+pointCount(−rho)=2(p+1).

At every original Fin3×Fin5 position, the actual norm equation gives N(pi−1)+N(pi+1)=2(p+1). Thus the two actual counts sum to the two actual neighboring Gaussian norms. Repeated positions and arbitrary initial root choices remain covered.

## 5. Produce the missing orientation and final same index

OneCount retains only the unordered count at the constructed base root: that count equals either the primary or opposite neighboring norm. This is still the genuine one-count CM/Frobenius input, not a renamed claim of proof. The opposite-count sum now forces the other count. If the first is primary, choose false; otherwise choose true. The actual oriented-root constructor is shown to swap the two literal counts when its Boolean bit is true, including the double-negative-root case.

Choosing independently at all15 positions produces an exact CMMatch for the original root family. There is no caller-supplied orientation or second-count equation. The final ConjugateIndexPreparation theorem first obtains the same prior real threshold T and local divisibility modulus Q. After the Gaussian prime data, mod7 rays and OneCount arrive, it constructs the bits and invokes the unchanged GaussianIndexPreparation family. It therefore produces the same arbitrarily large h with all three congruences, original scalar/guard margins, fixed emitted roots, prepared poles190/241/292, nonpole rows and conditional first263 certificate completion.

The global prime-pattern outputs, one-count CM theorem, actual rational Realizations and rational-anchor local-global implication remain explicit. This is not full288 unconditional existence.

## Validation

All222 predecessor sources are byte-identical. Six new modules use finite1M budgets. Static closure is228 modules with222 baseline dependencies. Exact checks cover8253 ordinate fibers,3987 nonsquare twists including D=0,10 reciprocity-at7 cases,7 literal original conjugate count pairs and12 actual orientation choices, together with the exact coordinate identities and missing-mod7 negative control. All inherited Gaussian norm/CRT/source checks pass.

These finite checks do not establish the universal CM/Frobenius input. Hosted Lean elaboration/recursive axiom audit and a distinct bounded source review are separate acceptance stages. No local Lean build was run.
