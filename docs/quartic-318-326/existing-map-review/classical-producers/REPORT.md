# Retrospective audit of our classical identification claims

## Frozen target, role and decision

Target: `diophantine-z-q` commit `dea5d91b63e43d5f3ba9874c64463a0f28ff934b`, 8 November 2026. This is a retrospective inspection of work already contributed, not a new upstream source repair. The new minus-19 optimal-CM source investigation was paused for this audit.

Reviewer: internal model worker `/root/restart_contact_field`. The exact model identifier is not exposed in this task. Tools: shell file reading, SHA-256 and Git object comparison; mathematical source reading and derivation. No Lean replay, new external-primary-source revalidation, or computer other than the assigned cloud workspace is claimed.

**Authorship disclosure:** I authored contact field, character, affine-model and normalization-chart predecessors. This report does not provide independent acceptance of those contributions. A separate non-author retrospective by the Hodge worker covers the concrete contact maps. I read the three classical producer arguments below directly, rather than inferring their correctness from earlier PASS verdicts.

**Decision:** one concrete documentation-scope correction is required. At the bounded identification steps inspected in the three classical producer notes, I found no counterpart of the Baba–Granath error that treats a degree-four displayed isogeny as an isomorphism. This is not a new full acceptance of all external theorems, a proof that the dependency inventory is exhaustive, or an unconditional FiveContact49Height/318/326 proof. The actual formal producer assumptions remain exposed.

## 1. Concrete overstatement in our character packet

The frozen `receipts/contact-character-quotients/README.md`, line 5, calls the omitted and other root-sign flips “inertia flips.” Line 7 also calls the degree-eight objects “inertia quotients.” The actual `SourceCharacterFields318.lean` defines `flip` at line 67 and proves `omitted_flip_fixes` and `other_flip_negates` at lines 69–88 using `FourRootAutomorphisms318.signEquiv`. Those statements have no valuation, place, branch fiber or inertia-group identification.

The already-published non-author `reviews/contact-character-review/REVIEW.md`, lines 21–27, explicitly made precisely this qualification. Thus the historical finding is **prior limitation located, not incorporated into the README wording**. It is not evidence of a false field or automorphism theorem.

Required correction to active explanatory text: replace “inertia flip” with “root-sign flip,” and “degree-eight inertia quotients” with “degree-eight character quotients,” explicitly retaining the separate local valuation/geometric identification. Preserve the frozen receipt and review rather than silently rewriting their evidence. No Lean theorem change is requested. The coordinator has been notified; this audit does not make shared edits.

## 2. Actual five-contact geometry and degree-576 field

Read `receipts/fiber-field-bridge/FIBER-PRODUCER.md` in full. Its argument does not reconstruct a PEL surface merely from a matching j-invariant.

- Sections 1–2 start with the actual González–Rotger quotients of X_210. Four involution fixed loci each contribute eight points. A characteristic-zero finite curve stabilizer is cyclic, so in W = (Z/2)^4 a nontrivial stabilizer has order two. Riemann–Hurwitz forces genus zero for X/W and exactly five size-eight branch orbits. Independent first four labels and the product relation identify the fifth label as 210. Unique occurrence of each Q-defined label makes each branch point rational.
- For an actual genus-one quotient E_m, the order-eight exponent-two residual group has linear image of order at most two. Its translation subgroup has order at least four and at most four, hence equals E_m[2]. The quotient q:E_m→E_m/E_m[2] is degree four. Multiplication by two factors as q followed by an induced degree-one isogeny E_m/E_m[2]→E_m. **That induced map, not [2] or q, is an isomorphism.** This justifies equality of the relevant j-invariants for the same actual branch quotient. The exact finite cross-ratio calculation then selects the branch coordinates; a coincidence of invariants is not used to identify a polarized abelian surface.
- Sections 3–6 name the entire principal-level-three canonical model, including all components, and its actual normalizer action. The effective kernel has order 36 and W has order 16. The splitting field of the entire finite fiber is normal. Commuting faithful Galois permutations embed in the opposite regular group, giving degree dividing 576. No claim that an arbitrary permutation group has order 576 is made.
- Sections 7–8 give the separate integral and same-field Hom arguments. Tame fixed-point lifting, the actual smooth proper model outside 210, and all five contact charts are necessary inputs. The degree bound alone is not presented as proving ramification or reduction. Full three-torsion and the finite congruence-kernel argument imply all geometric homomorphisms are defined over that same field.

The formal `FiberCentralizer318.galois_torsor_degree_576`, lines 109–118, explicitly assumes a finite Galois extension, a bijective orbit map, group cardinality 576, and a faithful commuting Galois action. It constructs none of the actual Shimura objects. The classical note supplies the proposed mathematical application separately; this audit has not freshly rechecked every cited canonical-model/stable-model theorem against its primary final publication.

## 3. Same-field CM producer: isogeny remains an isogeny

Read `receipts/cm-height-producer/CM-PRODUCER.md` and its earlier non-author review in full.

The classification conclusion is A is **isogenous** to a square of a CM elliptic curve, not that a displayed map is an isomorphism. If A were simple, its division endomorphism algebra acts on rational H1 of dimension four, hence has dimension dividing four. Containment of the quaternion division algebra forces equality, incompatible with a commutative semisimple algebra of dimension four required by CM type. Nonisogenous elliptic factors or a repeated non-CM elliptic factor also cannot contain the quaternion division algebra. This gives the geometric isogeny class.

All geometric endomorphisms being defined over L makes rational idempotents, the images of their integral multiples, and factor homomorphisms defined over L. Differentiation embeds the imaginary quadratic endomorphism field F in the same L, because a nonzero elliptic endomorphism in characteristic zero is separable.

The maximal-order step is an explicit quotient, not an unsupported replacement. With f O_F contained in End(E) and a Z-basis alpha_i of O_F, the L-defined subgroup generated by (f alpha_i)(E[f]) has analytic preimage O_F Lambda. Its quotient E' has lattice O_F Lambda and multiplier ring exactly O_F. Thus A'=(E')² is L-isogenous to A. The proof does not identify A with A' or preserve a principal polarization by assertion. The degree bound for a suitable A'→A and half-log height variation are separately used.

The arbitrary good-reduction extension used for the stable-height average is distinguished from the original field L of degree at most 576 used by Gaudron–Rémond. The bound 854R is for the original-normalized **surface** height. The separate contact comparison yields 1708R+120.

`CMProducer318.original_surface_bound`, lines 13–24, retains the actual discriminant/support, reduced periods, Silverman equality, product equality, original field degree, isogeny-degree bound and half-log variation as hypotheses. Its arithmetic composition is not a Lean construction of an abelian variety or proof that these geometric hypotheses hold for every fiber. The classical argument is present and must not be described as absent just because that formal instantiation is absent.

## 4. Maximal-stack Kodaira–Spencer: the actual universal fiber

Read `receipts/maximal-ks-producer/MAXIMAL-KS-PRODUCER.md` in full.

The note fixes the actual discriminant-210 quaternion algebra, maximal order and positive involution. It uses the maximal moduli stack with n(U)=1 over Z. The map (A,i,eta)↦(A,i) forgets the level marking in the same PEL moduli problem. The universal surface pulled back along that object is canonically the same A, with its O-action, polarization and identity section. Smooth differentials and their determinant commute with this base change. This is stronger and different from identifying coarse invariants or an isogeny class.

The canonical sections are the actual functions t=32s and q0=(dt)²/product(t-a_i), q1=t q0 at a_i=0,32,76832,-343, with infinity separate. The independent extension and norm estimates remain dependencies. Pullback is of the maximal stack's canonical line; the argument does not replace it with the canonical line of the level cover. Consequently it introduces no level degree or relative ramification divisor.

The exact integral input is an isometry lambda²→omega_M² with image 210 omega_M². Evaluation on an integral number-ring object preserves this injectivity because 210 is a nonzerodivisor. The induced lattice has normalized degree h(210M)=h(M)-log210; therefore h_omega²=2 h_Yuan(A)+log210. The normalization ledger gives h_Yuan=h_original+log pi. No factor 1/2 from stack integration enters a pointwise arithmetic-degree evaluation.

`InducedLattice318.ks_degree` formally derives the degree identity from an equality of all frame norms. `RefinedContactRealization318.MetricSections`, lines 14–26, **assumes** the actual image-lattice equality `ks_image`, Hodge degree, section ratio and all local section bounds. The notes offer a classical route to these records but no Lean PEL universal object is silently constructed by that structure.

The source named in the frozen note is Yuan's English author version dated 30 April 2024. This retrospective does not upgrade that version to an independently checked final publication. Any existing later published-source route must retain its own current version-bound acceptance.

## 5. Nine-obligation retrospective comparison

1. **Source hypotheses.** The fiber note needs the actual X_210 quotients, canonical PEL model and integral stable-model statements. The CM note needs CM type, quaternion division action and all endomorphisms over L. The KS note needs Yuan's actual maximal stack and integral isometry. These are stated, not consequences of arbitrary field or invariant agreement. Fresh complete external-primary-source review is outside this bounded pass.
2. **Constructed objects.** The notes name the actual full level-three fiber, its normal splitting field L, its universal abelian surface A, the explicit same-field CM quotient E', and the forget-level object in the maximal stack. Formal records are distinguished from those classical objects.
3. **Domain/index coverage.** The full level scheme includes all components; the rational parameter excludes all five contacts; characteristic zero is used for the generic group action and same-field CM argument. The final realization quantifies over every primitive (u,v) with all five forms nonzero. This universal producer is still an explicit hypothesis, not supplied by selecting one favorable fiber.
4. **Comparison maps.** The maps inspected are the degree-four quotient followed by a degree-one map induced by [2], faithful Galois action into the opposite regular group, rational idempotent images and the L-defined CM subgroup quotient, and literal forget-level/universal base change. No displayed degree-four isogeny is promoted to an isomorphism.
5. **Identity of consumed object.** The bound 576 uses the whole-fiber normal field. The CM isogeny theorem uses its original L, not the larger good-reduction averaging field. KS uses the determinant of the same A, not a Jacobian inferred from identical j-invariants.
6. **Coefficients/normalizations.** W and level sizes are 16 and 36; the centralizer uses the opposite group. CM retains original surface height, Xi squared, the half-log variation and the factor four in the quadratic discriminant estimate. KS retains image 210, the positive log210 correction and h_Yuan=h_original+log pi.
7. **Local conditions.** The classical integral argument is away from 210, with odd-contact ramification and a reciprocal infinity chart; all geometric Hom descent uses full three-torsion. KS evaluates an integral number-ring object and does not claim arbitrary characteristic-p injective base change. These local geometric statements are not inferred from the group-cardinality theorem.
8. **Exceptional cases.** Generic contacts are excluded, including infinity; extra quaternionic elliptic automorphisms are ruled out in the source model. CM remains in characteristic zero and distinguishes the possible quadratic 2-adic discriminant exponent. Formal period/support/isogeny positivity assumptions and the nonzero section a0 are visible. No division by an unproved nonzero coordinate is hidden in the checked endpoints.
9. **Downstream consumption.** `RefinedGeometricRealization` is deliberately unasserted. `five_contact_of_refined_realization` requires it. The source, literal 318-coordinate and stored 326-coordinate soundness theorems each retain `GeometricRealization`. These formal signatures do not turn the classical notes into an unconditional final proof; completeness remains separate.

## 6. Coverage and next action

The exact files and selected raw-byte line spans are in BINDINGS.json. CHECKS.json verifies the target whole-file bytes against Git commit dea5d91 and recomputes excerpt hashes. These checks establish evidence identity only, not mathematical truth.

The concrete action is the narrowly scoped active README correction, with frozen history preserved. No false actual field/ring/Scheme map was identified here; their independent read belongs to the Hodge reviewer. Whole source/infinity intersection localization remained a separate unfinished draft. The actual chosen contact model's smooth/proper/normal results do not by themselves identify its twists, Jacobian, PEL action or polarization with the Shimura source. Neither the new minus-19 investigation nor a proof expansion was resumed.
