# Application contract: actual open-chart module gluing

1. **Source requirements.** The unchanged matching-family construction requires
   linear transitions on every common subopen, original restriction naturality,
   identity and cocycle. The new source requires instead original sheaf isos on
   each pair open in the canonical over-open model and their actual triple
   cocycle after original overFunctorMap normalization. SheafOfModules.overMap,
   evaluation and Scheme.Modules.overEquiv/overFunctorEquiv use the original
   sheaves/ring maps. The chart direct-image counit requires the actual open
   immersion, supplied by each original chart inclusion.

2. **Constructed objects.** restrictIso uses the original overMap and both
   canonical endpoint comparisons. component evaluates those exact original
   isos at each actual common subopen. sectionData derives the full prior gluing
   inputs. sheaf/overIso/chartIso are the unchanged matching-family construction.
   ambient is the actual direct image of each original local module F i;
   chartRecovery and subchartRecovery use the original counit, composition and
   inclusion equality. pairTransition explicitly conjugates the original local
   pair iso through these same comparisons.

3. **Coverage.** All chart indices, original pair opens and original triple
   opens are retained. Their sheaf components cover every common subopen by
   evaluation; no selected frames or smaller overlap family is substituted.
   The global sheaf construction works for the stated chart family; any claim
   of a global line from rank-one frames still requires the original top-cover
   condition. The final chart module recovery is for every original chart.

4. **Transition directions.** Pair isos run from ambient M i to ambient M j
   over U i intersect U j. On the triple open, restricted i-to-j followed by
   j-to-k equals i-to-k. The recovered equation is restricted glued-to-i then
   original i-to-j equals restricted glued-to-j. chartRecovery runs from
   restriction of the original direct image to F i. pairTransition runs from
   ambient i via subchartRecovery to the original local transition, then the
   inverse subchartRecovery for j. No direction is dropped or inferred.

5. **Hypothesis checks.** Evaluation of the original sheaf iso derives linear
   components. Its original naturality proves all restriction squares. Identity
   and triple laws are obtained by evaluating the supplied sheaf equations after
   the actual normalized restrictions. Gluing uses those derived data, and
   transition_recovered applies the previously proved exact section comparison
   on all opens to establish equality of actual sheaf isos. Open immersion is
   available for every chart/subchart inclusion. The final module recovery uses
   original actual counit isomorphisms, not a new recovery assumption.

6. **Consumer identity.** The sheaf is the unchanged explicit matching-family
   sheaf. overIso and chartIso are the unchanged comparisons built from its
   actual section evaluations. transition_recovered returns the exact original
   input pair iso. For original chart modules, ambient is their actual direct
   image and comparison composes the exact same glued chart iso with the actual
   counit to recover the unchanged F i. No line class or unrelated presentation
   replaces these original module-sheaf objects.

7. **Scalars and normalization.** Evaluation is linear over the original
   Γ(X,V). Canonical overFunctorMap endpoints preserve the actual ring sheaf,
   and local-to-ambient comparison uses original restriction composition and
   Scheme.homOfLE_ι equality. No scalar correction, frame choice or rational
   normalization is inserted. The exact input transition is recovered as an
   actual sheaf isomorphism, not merely up to a unit factor.

8. **Downstream boundary.** Original coherent over-open sheaf data now feeds
   object gluing and exact overlap recovery. Original chart direct images and
   actual local pair-isomorphism conversion are supplied. Coherence of that
   conversion for an independently specified scheme-local triple datum still
   needs proof, as do arbitrary local-line frame refinement and changing-base-
   chart compatibility for affine fppf reconstruction. Prior accepted unit-
   cocycle line gluing is retained and is not classified as historically absent.
   General fppf/Picard/Jacobian and arithmetic completion are not claimed.

9. **Evidence and acceptance.** Eight sources, five exact predecessor bindings,
   the actual primary-source interfaces and all nine obligations are bound.
   Static checks and audit-history self-tests are structural only. No local
   Lean ran. Full hosted replay, recursive axiom audit and independent acceptance
   remain pending. Previous frozen sources and approval registers are unchanged.
