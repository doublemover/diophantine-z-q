# Actual open/affine pushforward comparison: bounded non-author review

Decision: accepted for the two exact sources and nine-obligation application. No required correction was found. Neither new source nor the immediate PushforwardStructureSheaf318 interface was authored by this reviewer. Group's initial generic source and checkpoint's correction/specialization are treated as one joint-author producer, not as mutual independent review. No reviewer compile or dependency replay was performed.

Target receipt: 06f002fc40eb3f88c6fc3cf3cb688d7f6a47870c0cfa325005eb68cb11850179. APPLICATION.json: c6be4686f6e8e8e6103b22bda7fa18407f52fe2cf0ed96774adee783c9e53528.

## Exact module objects and all opens

PushforwardStructureSheaf318.object f is literally Scheme.Modules.pushforward f of the original structure sheaf unit. Its sections at U are the original sections on the entire f inverse image U, with scalar action multiplication by f.app U. Its restriction maps are the original source presheaf restrictions. The predecessor definitions were read; no section basis, reduced point functor or substitute free module defines this object.

The generic new comparison retains the actual square q:P→U, k:P→X, j:U→Y, f:X→Y, both stated open immersions and the actual IsPullback q k j f. For every open W of U, the pinned open-pullback theorem gives k(image of q inverse W)=f inverse(j image W). The library proof uses the actual categorical pullback and original open immersions, so it is not a claim of scheme equality from point coincidence alone. The new ringIso transports along this exact open equality, contravariantly, then applies the original k.appIso. Its direction is from sections on the complete source inverse image to sections on q inverse W. ringIso_hom identifies that hom with the exact k.appLE and the proved inclusion. It works for every W, including the empty open, and preserves all ring structure and nilpotents.

## Actual scalar compatibility

The restricted O-module's scalar action is not silently replaced by the source's old coefficient ring. The inspected Scheme.Modules.restrictFunctor uses j.appIso inverse on scalars. Accordingly the new module-iso proof explicitly compares multiplication by q.app W a on the destination with multiplication by f.app(j image W)((j.appIso W).inv a) on the source. scalar_square is proved before promoting the ring/additive comparison to a module comparison; it follows from the original Scheme square via both appLE composition identities. Applying that square to (j.appIso W).inv a and its actual inverse law gives precisely the scalar equation required by ModuleCat.isoMk. The explicit section-type cast fixes elaboration only; it changes no ring map or scalar action.

## Naturality and both inverses

natural proves compatibility with every further open restriction by original appLE naturality. PresheafOfModules.isoMk takes these actual component module isomorphisms and that naturality. Its implementation was inspected: its inverse components are the original component inverses, with inverse naturality obtained by the proven forward square and inverse equations. SheafOfModules.fullyFaithfulForget simply restores the same natural module morphisms; its preimageIso does not select a new map from a pointwise existence argument.

Thus OpenPullbackStructure318.iso is an isomorphism of actual O_U-module sheaves. iso_component is definitionally the original ringIso hom on every section, and iso_hom_inv/iso_inv_hom are the two genuine categorical inverse equations. The result does not merely compare top-open sections.

## Exact affine specialization

AffinePullbackStructure318 assumes only IsAffineHom f and an actual affine open hU. Its source chart is the entire affine inverse image hU.preimage f. The square uses precisely Spec.map(f.app U), the original source and target fromSpec maps, and f. The pinned SpecMap_appLE_fromSpec theorem supplies the commuting square in the correct contravariant direction, while both original opensRange_fromSpec equalities identify the entire inverse image. The inspected IsOpenImmersion.isPullback theorem then supplies the actual universal property, not just square commutativity.

The affine iso is a literal specialization of the generic comparison. Its component is still the specified ringIso, and both inverse equations remain explicit. No finite-flat, smooth, reduced, connected or nonempty hypothesis is introduced. Nilpotent schemes are included because all objects and maps are actual section rings/module sheaves and the open-pullback construction imposes no reducedness assumption.

## Evidence and retained limit

All target artifact hashes and exact dependency pins match. Both short strict logs contain the designated CHECK and RELEASED markers and no errors; the producer reports strict success, and this review does not invent exit-code markers absent from those logs. The fresh audit imports all target declarations, verifies twelve named endpoints, scans the target modules including generated/private declarations and recursively allows only the three stated standard axioms. Its log contains exactly twenty AXIOM_CHECK rows and the two-module PASS marker. Hosted integration remains pending/separate. No local replay was performed.

Accepted: actual open-cartesian and affine fromSpec restriction isomorphisms for the original structure-sheaf pushforward, with every-open scalar compatibility, naturality, exact components and both inverses. Not established by this packet: actual local rank-eight freeness or frames, global freeness, determinant-line construction, norm/Picard/Jacobian/PEL operations or the full arithmetic theorem. Those consuming constructions remain separately owned. No source change is required.
