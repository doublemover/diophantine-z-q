# Application contract: original scheme-transition coherence

1. **Source requirements.** Original scheme restriction uses restrictFunctorComp,
   restrictFunctorCongr and Scheme.homOfLE_ι at both endpoints. The actual over
   model uses original overFunctorMap and overEquiv/overFunctorEquiv. The existing
   module/line gluing requires coherent over-open data. The new restriction
   comparison derives that coherence from original scheme-local pair isos and
   the original normalized scheme triple equation. All source definitions and
   consuming passages are exactly bound.

2. **Constructed objects.** path and schemeRestrict retain the actual scheme
   inclusion and original restriction composition. map_toOver_hom and
   toOver_hom_app identify the exact original section map of toOverIso.
   schemeRestrict_hom_app computes both endpoint equality transports explicitly.
   restriction_compatible proves equality with the actual over restriction.
   overData derives the prior gluing inputs. The final sheaf, comparison, line
   and lineComparison are the actual prior constructions on those derived data.

3. **Coverage.** Every ambient module, original pair open and original triple
   open is retained. The restriction comparison covers every inclusion V ≤ U
   and every subopen of V. Its image-open equality is the actual composite-image
   equality, not a generic-point or frame restriction. Full chart/local-frame
   coverage remains explicit for the global line consumer. No part of a required
   overlap or local-frame index family is omitted.

4. **Transition directions.** schemeRestrict maps an actual iso on U to V via
   original source path, restriction of the iso, and inverse target path.
   Its over counterpart uses the inverse source overFunctorMap, original overMap,
   and target overFunctorMap. The comparison proves these directions agree.
   Original scheme triples compose i-to-j then j-to-k to i-to-k. The recovered
   global equation is restricted comparison-to-i then the unchanged original
   i-to-j iso equals restricted comparison-to-j on the exact pair scheme.

5. **Hypothesis checks.** The open-image equality follows from original
   Scheme.Hom.comp_image and homOfLE_ι. Original sheaf naturality along that
   equality proves the compatibility of both restriction routes. toOverIso
   preserves identity and composition by exact canonical comparison cancellation
   and reflects iso equality through the faithful original equivalence.
   Evaluating the supplied original scheme cocycle through this proven transport
   supplies overData; no new over/scalar cocycle is assumed. The original
   module gluing and local-frame cover proofs then apply to these exact inputs.

6. **Consumer identity.** The comparison on each original open subscheme is
   the prior explicit matching-family chartIso. comparison_toOver identifies
   it with the same original overIso, not an arbitrary alternative. The final
   transition_recovered theorem returns the unchanged original scheme pair iso.
   The line consumer keeps the unchanged glued module and original local frame
   families and recovers the unchanged original local line objects.

7. **Scalars and normalization.** Both original equality-transport restrictions
   on sections are computed; their inverse composite is cancelled through
   original presheaf functoriality. Original rings and module actions are
   retained. No scalar, unit correction, rationalization or class-only identity
   is substituted. Original scheme and over comparisons are related by an
   actual proved equation of sheaf isos.

8. **Downstream boundary.** Actual ambient scheme-local pair/triple data now
   supplies coherent over-open data, exact scheme overlap recovery and global
   local-line gluing. For original chart modules Fi, the direct-image adapter
   and actual pair conversion are retained, but compatibility of that conversion
   with separately specified Fi-only triple normalizations remains further work.
   Changing-base-chart compatibility of the affine fppf reconstruction and the
   final application to that datum remain separate. Historical accepted unit-
   cocycle line gluing is unchanged, and full Picard/Jacobian/arithmetic claims
   are not made.

9. **Evidence and acceptance.** Thirteen sources, ten exact predecessor bindings
   and all nine obligations are hash-bound. Static import/hash/placeholder and
   audit-history checks are structural only. No local Lean ran. Full hosted
   replay, recursive axiom audit and independent acceptance remain pending.
   Frozen packets and formal acceptance registers remain unchanged.
