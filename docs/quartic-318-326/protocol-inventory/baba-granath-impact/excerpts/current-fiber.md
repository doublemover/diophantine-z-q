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

