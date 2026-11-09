# Actual relative line-class prerequisite

This is an isolated continuation of commit
`5e483a2b186a83500f4b603f3ddfc514ae84a393`. It is not part of the 1,837-module
accepted-source manifest. Its compilation receipt and any non-author
review must be reported separately. No manuscript application is changed.

1. **Required inputs.** The construction takes arbitrary same-universe schemes,
   their actual morphisms, and the existing locally framed module-sheaf line
   objects. Neither flatness nor reducedness of test schemes is required. A
   relative construction additionally takes an actual structure map `p : X → S`.
2. **Constructed objects.** Tensor products are the original
   `IntrinsicTensorSheaf318.tensor`, pullbacks are the original
   `Scheme.Modules.pullback`, and classes are the original
   `LineSheafClass318.Class`. A relative class is the quotient of this group by
   the image of actual pullback from the base. No unrelated abstract group is
   substituted for these line classes.
3. **Index-set coverage.** Two independently presented lines are framed on the
   actual common refinement of both complete covering families. Pullback uses
   every full inverse-image open. `source_cocycle_eq` explicitly identifies the
   inverse image of a complete target intersection with the complete source
   intersection. It does not check only a dense subopen or the generic stalk.
4. **Maps and directions.** `comparison` maps `f*(M tensor N)` to
   `f*M tensor f*N`. Its transition identity comes from the existing actual
   pullback-cocycle theorem, actual tensor-transition product theorem and the
   multiplicativity of the structure-sheaf unit map. Reconstruction supplies
   both inverse laws. The group homomorphism is the unchanged class pullback.
   Composition is contravariant: `(f ≫ g)* = f* ∘ g*`.
5. **Object consumed downstream.** `RelativeClass p` is exactly the quotient by
   `(pullback p).range`. For a commuting square, the base-line representative
   `p*d` pulls to `p'*(b*d)`, so the original pullback descends to this exact
   quotient. Its identity and composition proofs use quotient representatives,
   rather than assuming a new functor law.
6. **Actual varying base.** `TestClass p t` evaluates the relative quotient on
   the actual categorical scheme fiber product `X ×_S T`, with projection to
   `T`. `totalMap` is the original universal-property-induced map, with both
   projection equations exposed. These maps give a contravariant functor from
   `S`-schemes to commutative groups, including nonaffine and nonreduced tests.
7. **Source identity and history.** The prerequisite sources are
   `LinePullbackTransitions318`, `TensorLineCocycle318`,
   `FramedLineCocycleIso318`, `LineSheafClassGroup318` and
   `LineClassPullbackLaws318`. The final application also imports
   `FifthCompletedGlobal318`, which contains the original four completed maps.
   The general four-module foundation uses 150 baseline modules; the complete
   six-module application uses 471 baseline modules at the pinned commit.
   The existing README explicitly
   excludes later pullback-tensor work; this packet does not claim that no
   earlier unpreserved proof existed. Mathlib's ring Picard group and elliptic
   Jacobian coordinates are not a representing relative Picard scheme.
8. **Original quotient consumers.** `RelativeLineFunctorPullback318` constructs
   the base change of any original morphism over the same base, exposes both
   projection identities, and proves that the actual map commutes with change
   of test scheme. This induces an actual natural transformation, in the
   pullback direction, on the naive relative class presheaves.
   `ContactRelativeLinePresheaf318` applies it to the original contact
   normalization and to all five original completed elliptic quotient maps,
   using their existing exact rational structure squares. The original-line
   formulas identify the actual pullback map on every test, rather than merely
   assigning a transformation of abstract groups.
9. **Validation and remaining joins.** The intake binds each new source hash and its exact
   imports. Source-policy validation is not Lean compilation. A strict kernel
   check and recursive audit of all new private/generated declarations are
   required before reporting a checked result. Reused predecessor artifacts
   must retain the exact verified source/dependency/toolchain/hash identity.
   No independent approval is authored here.
   This is the naive relative Picard
   presheaf, not its fppf sheafification or a proof of fppf descent, smallness,
   representability, smoothness, properness, degree-zero component, source
   Jacobian, polarization, or isogeny. The five existing line norms are over
   the original rational schemes; arbitrary-base norm construction and its
   base-change compatibility remain separate. The height theorem and complete
   integer-witness construction are unchanged.

The first next mathematical obligations are effective line-bundle descent and
the representability/degree-zero construction for the actual smooth proper
geometrically integral source. Field-point class groups alone do not discharge
them, nor does a norm-pullback eighth-power identity produce an isogeny without
represented finite-type group schemes and the remaining dimension/kernel data.
