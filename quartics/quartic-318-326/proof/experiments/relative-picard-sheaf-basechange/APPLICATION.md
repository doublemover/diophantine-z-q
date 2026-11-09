# Actual associated-fppf-sheaf base change

Three new sources compare the original relative line-class presheaf and its
actual associated fppf sheaf under arbitrary scheme base change. Unchanged
producer copies only close the imports against the pinned 1,837-source
baseline; they are not additional results.

1. **Original relative group.** `relativeIso` uses the original pullback maps
   along an actual scheme isomorphism and its actual inverse, over the same
   base. Both inverse laws reduce to the original class pullback laws after
   the actual quotient map. No replacement group is introduced.
2. **Full fiber products.** `fiberIso` is the canonical actual isomorphism
   `(X ×[S] S') ×[S'] T ≅ X ×[S] T`. Both projection identities and naturality
   for the exact earlier `totalMap` are proved. All schemes and scheme maps
   are allowed, not only field points or flat base maps.
3. **Presheaf comparison.** `presheafIso` compares precomposition of the
   original presheaf with `Over.map b` against the original presheaf of
   `pullback.snd p b`. Its components are precisely the original relative
   pullbacks through `fiberIso`, with actual naturality squares.
4. **Exact topologies.** Both sites are literally the original fppf topology
   over the respective bases. The continuity and cocontinuity instances come
   from the proved over-site theorems for `Over.map b`; they are not supplied
   as hypotheses by a caller.
5. **Derived sheafification compatibility.** The current pinned library's
   continuous/cocontinuous right-Kan-extension adjunction proves compatibility
   of precomposition with associated sheafification. The required right Kan
   extensions and sheafifications are resolved from the actual group-category
   limit instances and the earlier constructed sheafification instance.
   No independent compatibility premise is added.
6. **Exact sheaf isomorphism.** `sheafIso` composes that adjunction comparison
   with sheafification of the proved original `presheafIso`. Its target is
   the associated fppf sheaf of the actual base-changed family, not a sheaf
   merely named to have the desired property.
7. **Universal-unit preservation.** `sheafification_unit` and
   `unit_basechange` prove the exact original-unit diagrams. The final
   isomorphism therefore respects the original relative class maps and
   actual fiber-product pullbacks, rather than being an unspecified abstract
   isomorphism of group sheaves.
8. **Original contact consumer.** `original_structure_identity` is the
   definitional equality between the section producer's original structure
   map at the published source units and the rational fppf packet's source.
   `sourceIso` identifies restriction of that same rational-base source
   sheaf with the actual field-base-changed family sheaf. `actual_cover` and
   `actual_section` bind the exact earlier finite etale fppf cover and exact
   original point section. No Q-rational section is assumed.
9. **Boundary.** This is base change for the actual relative-class presheaf
   and its associated fppf sheaf. It is not effective descent of chosen line
   objects, a degree construction, degree-zero component, representability,
   a Jacobian or Poincare bundle, arbitrary-base norm compatibility,
   polarization, a cotangent identification, or an isogeny.
