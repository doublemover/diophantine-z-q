# Application contract: actual affine Cech nerve comparison

Draft only; exact source and document bindings are in APPLICATION.json.

1. **Required inputs.** The original pullbackSpecIso applies to commutative
   R-algebras S and T and identifies the actual categorical scheme pullback
   with Spec(S tensor_R T), retaining the actual projections. It is applied
   first with T=S and then with T=S tensor_R S. The original ring endpoint
   identities are those of AffineCechRings318.
2. **Constructed objects.** The double object is ActualOverlapDiagram318.Double
   of the original Spec algebra map. The triple is its actual adjacent-double
   pullback, not a replacement product definition. toActual is the actual
   pullback.lift of12 and23 tensor maps through the same double inverse.
   toTensor is the actual outer pullback.lift of vertex0 and pair12 followed
   by the original outer Spec comparison.
3. **Coverage.** All commutative rings and every given R-algebra S are covered.
   The result is a scheme isomorphism with inverse equations, not a test only
   at fields, residue points, closed points or a generic locus. No flatness,
   finite presentation, reducedness or nontriviality premise is added.
4. **Transition directions.** The original categorical labels01,12,02 match
   the tensor labels12,23,13 respectively. The three actual vertices0,1,2 match
   tensor vertices1,2,3. The inverse triple comparison followed by each actual
   pair map is exactly the corresponding tensor Spec map followed by the
   inverse double comparison. The actual diagonal is Spec(tensor multiplication)
   followed by that same double inverse.
5. **Hypothesis checks.** The toActual lift equality is proved from the exact
   map12-right and map23-left identities. The toTensor lift equality is proved
   from actual double base projection, edge equality and triple middle equality.
   Both inverse equations use the actual pullback hom_ext universal property,
   with their original projections. No isomorphism or descent law is a hidden
   premise of the constructed triple comparison.
6. **Consumer identity.** tripleIso has hom literally toTensor and inv literally
   toActual. All_pairs simultaneously states the three exact actual pair-map
   identities using the unchanged ActualOverlapDiagram318 names. The double
   comparison is literally the original Mathlib pullbackSpecIso, and all
   tensor ring maps are the unchanged AffineCechRings318 maps consumed by
   geometric affine line reconstruction.
7. **Scalars and normalization.** Original algebra maps, tensor ring
   multiplication, inclusion maps and their Spec directions are retained.
   No scalar sheaf comparison, chosen trivialization, twist or coefficient
   is inserted. The result is solely an exact scheme-level diagram comparison;
   it does not silently identify subsequent module-sheaf pullbacks.
8. **Downstream boundary.** Transport of actual sheaf overlap data and its
   diagonal/triple equations through this comparison remains further work,
   requiring canonical module-sheaf pullback coherence. General geometric
   descent-category identification, reconstruction across base charts,
   non-affine gluing, rigidification, Picard representation and the full
   arithmetic theorem are not claimed. No arithmetic premise is replaced.
9. **Evidence and acceptance.** Three new sources and five exact producer
   copies are bound. Static hashes/imports/placeholders and audit-history
   checks pass. No local Lean ran. Complete eight-source hosted strict replay,
   recursive axiom audit and independent acceptance remain pending. Earlier
   producer validation does not approve this new consuming application.
