# Actual five-contact quotient and normal fiber field

## Status and proof boundary

The generic geometric quotient and the degree-576 fiber argument below have been independently reconstructed from the named primary inputs, rather than inferred from a finite numerical bound. Twelve Lean theorems check the centralizer, torsor transport, and actual finite-Galois degree conclusion. The arithmetic-geometric constructions in this note use standard curve, canonical-model, and finite-etale/Galois theory at mathematical application scope; they are not Lean constructions of schemes or quaternion Shimura varieties.

Section7 supplies the separate integral extension and ramification argument from Yuan’s actual model and standard stable-model extension. It is not inferred from the degree bound. None of these source/application proofs is a Lean construction of the model or a proof of the whole FiveContact49Height theorem.

## 1. Fresh actual quotient models

The published original González–Rotger, *Non-elliptic Shimura curves of genus one*, JMSJ58 (2006), 927–948, was freshly retrieved from the journal's J-STAGE copy. SHA256: e595d1a428f20e1c6b3695bc37be658ca12c517fb6600171f531fe931b796c3a. Theorem4.2 and Table2, printed938–939, explicitly identify the four quotients X_210/<w_m>, m=30,42,70,105, with exactly the quartics used in V10. The pages were rendered and visually checked. Proposition5.2 and the following Atkin–Lehner description supply the genus formula and W=(Z/2)^4 over Q with divisor-squareclass multiplication.

For D=210, the two elliptic corrections vanish because 5 splits in Q(i) and 7 splits in Q(sqrt(−3)); therefore g(X)=1+phi(210)/12=5. Each of the four published genus-one quotients has eight fixed points upstairs by Riemann–Hurwitz.

At a smooth characteristic-zero curve point, a finite stabilizer injects into the one-dimensional tangent representation: a finite-order automorphism with derivative one is identity, as its first nontrivial power-series coefficient would be multiplied by its order. Hence a W-stabilizer is cyclic and has order at most two. Every nonempty fixed locus is a union of W-orbits of size eight. The four known loci contribute32 to

8=16(2g(X/W)−2)+sum_(w≠1)#Fix(w).

The right side and g>=0 force g(X/W)=0 and total fixed count40. There is exactly one further orbit. The first four inertia labels are independent; their product is210. The product of the five inertia elements is one, from the fundamental-group relation on the punctured sphere. The remaining label is therefore210, distinct from the others. Each label occurs at a single branch point. As each involution is Q-defined, Galois preserves its label and hence fixes that unique branch point. All five branch points are rational; choosing three identifies the genus-zero quotient with P1 over Q.

## 2. The literal contact coordinates are forced

Normalize b_210=infinity, b_105=0, b_70=1, and write b_42=lambda, b_30=mu. For E_m=X/<w_m>, the residual W/<w_m> has order8 and exponent2. Over the algebraic closure choose an origin on E_m. Its translation subgroup has order4: the linear image has order at most2, whereas a translation subgroup of exponent2 has at most4 elements. Thus the translation subgroup is E_m[2], and its quotient has the same j-invariant, being multiplication by2 up to an isomorphism. The remaining double cover branches at exactly the four b-labels other than b_m. The four published quartic j-invariants therefore constrain the four actual branch subsets, not merely four unrelated elliptic curves.

`check_contact_coordinates.py` independently recomputes the exact quartic invariants, the six Legendre cross-ratios, and all36 candidate pairs. It verifies the given auxiliary Legendre parameters 1/2401,32/375,1/225,5/1029 and leaves exactly

(lambda,mu)=(2401,−343/32).

It also checks independence and the product210 of the four inertia labels. Computation uses exact Python rational arithmetic; it is not described as a Lean theorem. This fixes the actual branch line used by the metric and contact-radical packets.

## 3. Canonical adelic action and components

Deligne1979, Milne's corrected translation, section2.2.5 and criterion2.3.1, printed29, were freshly read through the primary PDF at https://www.jmilne.org/math/Documents/DeligneSV.pdf. Canonical models include the adelic right action over their reflex field; the stated criterion supplies existence for the symplectic-embedding case. The quaternion PEL datum here is of this type, and its cocharacter conjugacy class has weights(1,0), hence reflex field Q. This is the whole canonical model, not one selected complex component. In particular normalizer automorphisms on the principal-level-three scheme are Q-defined even when they permute components.

The moduli/PEL identification and the universal abelian surface are those of Yuan's actual maximal-order model. The standard alternating reduced-trace form supplies the symplectic representation; the positive involution specified by mu0²=−210 supplies the polarization. These are named model/theorem applications, not a conclusion about arbitrary curves from Deligne's definition alone.

## 4. Actual finite normalizer quotient

Put K=Ohat^*, U=U(3), Z=A_f^*, and N the adelic normalizer of Ohat. Conjugation by N preserves3Ohat, so U is normal in N. At all primes other than3, U has the same local factor as K.

Every central finite idele is q*u with q rational and u a unit idele: its finitely supported valuations are removed by a rational number. The scalar residue u_3 mod3 is +1 or−1. Adjusting q by that sign puts the remaining central unit in U. Thus Z is contained in Q^*U and acts trivially on the entire level-three canonical model. This argument does not require a chosen component to be stable.

Locally at the ramified prime3, O/3O has81 elements. Its radical has9 elements and its residue field is F9, so its unit group has81−9=72 elements. The central scalar units reduce to the two elements ±1. Thus the level kernel K/(K∩ZU) is (O/3O)^*/{±1}, of order36. The remaining quotient N/(ZK) is the four-generator Atkin–Lehner group of order16. Consequently

1→(O/3O)^*/{±1}→Gamma=N/(ZU)→W→1,
|Gamma|=36*16=576.

The local structure statements are the usual maximal-order structure for a ramified quaternion division algebra: radical P, residue F9, and3O=P². They explain both81 and9; these cardinalities are not inferred merely by subtracting a guessed number of nonunits. The adelic normalizer quotient agrees with the Q-defined W by the canonical maximal-level uniformization/strong-approximation identification.

## 5. Fiber really is a constant-group torsor

Take any rational s outside the five contacts. Its geometric fiber on X consists of16 points and is a free transitive W-set. Principal level three adds36 effective markings over each point: the full O/3O marking has72 choices, with the two automorphisms±1 identified. There are no additional quaternionic elliptic automorphisms on X, by the vanishing elliptic corrections above; full level three is fine. Therefore the fiber Omega on the whole principal-level scheme has576 points.

Gamma acts on Omega through Q-defined automorphisms. An element fixing a point maps to a W-element fixing the underlying point, so has trivial image in W. Its level-kernel element then fixes an effective marking, forcing it to be trivial. The action is free, and its group order equals the fiber size, so it is transitive. This verifies the actual regular-action premise used in the Lean theorem. A one-component fiber would generally not justify the same argument; no such restriction is made.

## 6. Normal field, faithful action, and degree

The fiber is a finite etale Q-scheme. The action of absolute Galois on its finite geometric point set is continuous. Let L be the fixed field of its kernel. This kernel is open and normal, so L/Q is finite Galois. It is the normal splitting field of the whole fiber, not just the residue field of one point. The induced Gal(L/Q) action on Omega is faithful by definition. It commutes with Gamma because every deck transformation is defined over Q.

Choose o in Omega and identify Gamma with Omega by g↦g o. Any commuting permutation f satisfies f(g)=g f(1). Evaluation at1 is therefore a homomorphism into Gamma^op, not Gamma with its original multiplication. It is injective on the faithful Galois image. Lagrange gives

[L:Q]=|Gal(L/Q)| divides |Gamma|=576,

and in particular [L:Q]<=576. This is exactly what `FiberCentralizer318.galois_torsor_degree_576` proves for an actual finite Galois extension, with the free-transitive orbit bijection, commutation, and faithful action explicit. The result does not assume the desired degree bound or use a factorial bound for arbitrary permutations.

All fiber points are L-rational. Pulling back the universal family on the fine level scheme gives the actual abelian surfaces and their full three-torsion markings over L. Section8 supplies the additional Hom-descent argument.

## 7. Actual integral extension and ramification support

Work over R0=Z[1/210]. Yuan's actual principal-level-three model Y is proper and smooth here; its maximal-order moduli stack is regular and semistable over Z. Only this stated theorem application, not a moduli space guessed from the quartic j-invariants, is used below.

Here is the precise tame lifting argument. At a special fixed point of an R0-automorphism sigma of finite order n invertible in the residue field, pass to a strict henselian completed base. Smoothness gives the completed local ring R[[u]]. Let lambda be the root of unity lifting the eigenvalue of sigma on the relative tangent space. The averaged parameter

z=(1/n) sum_(j=0)^(n−1) lambda^(−j) sigma^j(u)

has invertible derivative, is another formal relative coordinate, and satisfies sigma(z)=lambda*z. If lambda=1, sigma is identity on this completed neighborhood and hence on the connected generic curve. Otherwise lambda−1 is a unit and the fixed locus is the smooth section z=0. Thus a nontrivial tame automorphism cannot have an isolated special fixed point without generic fixed points. It also shows that every stabilizer acts faithfully on the tangent line.

Apply this first to the effective order36 level group. It acts freely on the generic level cover, so the preceding lifting excludes all special fixed points. The quotient X_R0=Y_R0/(level group) is consequently smooth, proper, and the forgetful map is finite etale of degree36.

The Q-defined W-action extends uniquely to the smooth stable model X_R0: the fibers have genus5, and the Isom functor for stable curves satisfies the valuative extension/uniqueness property. Tame fixed-point linearization shows that its nontrivial stabilizers remain cyclic. Since W has exponent2, a stabilizer has order at most2. Distinct involution fixed loci therefore never meet. For each of the five labels, its fixed locus is finite etale of degree8, as on the generic fiber. Dividing by the residual free order8 group gives one branch section over R0. No additional special fixed locus can occur by the same lifting argument.

The tame quotient X_R0/W is smooth; locally at a branch point its completed invariant ring is R[[z²]], and elsewhere the map is etale. It is a proper genus-zero curve with the five disjoint branch sections. Three of these identify it with P1_R0. The resulting coordinate agrees with the already determined generic coordinate because that normalization is unique. Thus the actual five rational contact sections, including infinity, are disjoint and exhaust branch support outside210.

Now fix a rational point outside the contacts and a prime p not dividing210. Its primitive homogeneous coordinates give an integral P1(Z_p)-point. If its reduction misses all branch sections, the fiber lies in the finite-etale locus, so it splits over a finite unramified extension. If it meets a branch section to even positive order2k, the local quotient is w=z² after an etale base change, with w=p^(2k)*u and u a unit. Over a strictly henselian unramified ring, u has a square root by Hensel's lemma because p≠2. The two roots z=±p^k*sqrt(u) are therefore unramified. The level-three cover is etale and adds no ramification. The identical argument uses the reciprocal projective coordinate at infinity.

Every geometric fiber point hence becomes integral on Y over an unramified extension whenever the normalized contact order is even (including zero). Pulling back its universal abelian scheme proves good reduction there. There is also a stronger good-reduction statement needed in the conductor application: at every p not dividing210, each L-point of Y extends over the corresponding valuation ring of L by properness of Y, even if L/Q is ramified there. The universal abelian scheme therefore gives good reduction of A over L at every such prime, not merely primes outside the odd-contact radical. Taking the splitting field of all fiber points does not add ramification at the even-contact primes: finite unramified local extensions are closed under compositum. Consequently every prime ramifying in L or giving bad reduction of a fiber surface lies either over210 or at a positive odd contact.

After enlarging the exceptional set to the literal15 bad primes used by the final source, this proves the claimed support statement rad(D_L*N_bad) divides B_bad*M, where M is the normalized odd-contact radical outside that set. Its exact equality to the primitive five-form support is checked separately in the conductor/contact arithmetic lane. This is a geometric argument using the actual model and all contact charts, not an inference from prime factors of pairwise determinants alone.

## 8. All geometric homomorphisms are defined over the same field

Let A and B be any two fiber surfaces over L. Their full three-torsion is L-rational by the fine markings. Put H=Hom_over_Lbar(A,B), a finite free Z-module. A finite basis of H is defined over a finite extension, so the absolute Galois action on H has finite image. The absolute Galois group itself need not be finite.

For sigma in Gal(Lbar/L) and phi in H, the difference sigma(phi)−phi kills A[3]: each input point is L-rational and its image belongs to the L-rational B[3]. In characteristic zero the torsion group scheme is reduced, so this is equality on the subgroup scheme, not just a formal pointwise analogy. The quotient of A by A[3] is the isogeny[3]:A→A; its universal property gives sigma(phi)−phi=psi composed with[3]=3psi for some psi in H. Thus Galois acts trivially on H/3H.

Choose an integral basis of H. The representation matrices have finite image in GL_n(Z) and reduce to identity mod3. The independently proved `HomLatticeDescent318.finite_image_representation_trivial` makes this representation trivial. Its underlying `MatrixCongruence318.finite_order_eq_one` is a strict-kernel proof by exact binomial/cubic expansion, lifting through every3-power, and prime-order reduction; no Minkowski theorem is assumed. Galois descent of morphisms now shows every element of H is defined over L.

The packet `hom-congruence-bridge/` has26 audited declarations in three modules. Its actual geometric application uses finite freeness/finite definition fields of abelian Hom groups, the quotient property of[3], and ordinary Galois descent. Those standard geometric facts are stated explicitly rather than represented by the matrix theorem itself. The construction works for homomorphisms between conjugate fiber surfaces as well as endomorphisms of one fiber, and it does not enlarge the degree576 field.

## Remaining boundary

The generic quotient, literal contacts, constant-group fiber, normal field degree, and integral support argument have now been independently traced at their source/application scope. The named canonical-model/PEL and stable-model results are not Lean-formalized. The all-geometric-Hom descent is now supplied by section8 and the independently checked mod3 congruence kernel. The modular representation, conductor theorem, cusp/Wronskian estimates, CM branch, and final global contact-height composition are handled separately; no complete FiveContact49Height theorem is asserted here.
