# Independent source review: rational infinity map normalization

Internal source review only; no local Lean/Lake/compiler/proof build and no kernel or whole-theorem acceptance claim.

Exact base b3d76fb41c03f9194b0613eac0a9b4cb04b2576c; run 43564923898; center-r60 artifact 14102460547. The before source and RESULT predecessor intake were compared directly with the published Git bytes. Own RESULT records this module failing 10.081s, after OtherRootCoordinates passed 15.242s.

Before 868e4abf61f8ef5ec9840296b83871789ab7102eccd6e2e283a52a1d349a07fa; candidate a58993f3349ec7a045d92b1d2f226ef5f16b504d84d2af27a414b21498d708f9. Exact log ab4b04a4b829cf45e97dbd65f02a150266d9205221a3cc61449035ad142cba83; RESULT 2f76c0931e3e1430b12fe293707a2a1aec88d4a395e6b502b0e2c7201f472688.

The only changes add AlgHom.toRingHom_eq_coe to two existing simpa-only lemma lists in field_restriction. Both errors explicitly show the expected side still using (infinityMap Q c).toRingHom applied to the same coordinate/root, while the witness uses the AlgHom application directly. Pinned Mathlib Algebra/Algebra/Hom.lean at 56a005855ea17e0b0958f73ec801ae140b0a1679 (file SHA 839f7471fed0a18fbe9d132c70eee788f5003e621ba59e649c8d7ea7bfbc34d8) lines 157 and 161 supplies the two rfl identities: structure projection to ring-hom coercion, then coercion to function. The new first rewrite exposes exactly the syntax matched by the existing second lemma. No substitute hom or unproved equality is introduced.

The required source is the entire integral infinity Order Q c, for every c : Fin 4 -> Q-units. The helper still checks the full localized polynomial base through its coordinate and every j : Fin 3 root. Rational constants/localization remain handled by the unchanged extensionality chain. The native infinityMap, originalFieldEmbedding, originalEmbedding and their composite retain identical definitions and directions. Signs and normalization y_j/y_0 are unchanged; no scalar or exceptional locus is dropped.

The unchanged downstream infinity_restriction applies original open-embedding injectivity and RingHom.congr_fun(field_restriction c) at arbitrary a in the entire original order, then the original toOpen_embedding equation. It therefore consumes this exact equality of maps, not an abstract isomorphic field map or coordinate-only conclusion. All theorem signatures, hypotheses, helper declarations and options are byte-unchanged.

No source-level blocker found. This bounded syntactic normalization targets exactly the two observed residual goals, but whether the candidate elaborates within hosted resource limits remains for CI. This report is not full packet/application acceptance; propagation and final metadata require their own exact bindings.
