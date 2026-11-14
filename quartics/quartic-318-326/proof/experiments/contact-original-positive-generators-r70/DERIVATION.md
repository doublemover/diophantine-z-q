# Original affine-line dual frame: typed categorical transport

Basis: run 43568616769 at e3d4f3341daf299c5658e7e9fe2f276f2e6aa58e, predecessor contact-original-positive-generators-r69, artifact 14104370311, ZIP SHA-256 55f81000e369c47563a1ad1df91b61f78ebf464746f3a6870e76d056429f5a27. FiniteProjectiveDualFrame318 now passes 1.417 s. The next first failure OriginalAffineLineDualFrame318 takes 1.467 s. Exact log/RESULT and original bytes are retained.

## Source requirements and observed elaboration failures

transport_total is the same additive-functor transport of a finite identity decomposition. It takes arbitrary categories C,D with their Preadditive structures, additive F:C⥤D, objects M,N,A,B, e:F.obj M≅A, u:F.obj N≅B, every finite index type ι, families out_i:M⟶N and back_i:N⟶M, and sum_i out_i≫back_i=id_M. The original unparenthesized binder `ι → M ⟶ N` parses with a type-valued function domain and reports 'type expected' on M. Parenthesize exactly the morphism-valued codomains, preserving the intended universal families and their full finite sum. The inverse-direction family is corrected identically.

The existing naturality/cancellation calculation retains all original map order and identities. Its final Functor.map_id is explicitly qualified as CategoryTheory.Functor.map_id, the actual categorical functor law rather than the similarly named applicative law. No functor, isomorphism or identity decomposition is changed.

## Original bundled module, scalars and maps

OriginalLineAffineModel318.sections R L is the original moduleSpecΓFunctor object, carrying the original structural R action; canonicalIso is the actual tilde-Gamma counit. The finite-presentation/flat-to-projective proof, moduleFrame, selected finite index n and its original out/back linear maps are unchanged. No rank-one basis or global triviality is asserted.

The concrete out definition's untyped ModuleCat.ofHom fails to synthesize Module R on an unfolded raw section carrier. The candidate specifies X := OriginalLineAffineModel318.sections R L and Y := R explicitly for out, and the reversed X/Y for back. These are exactly the original type arguments and stored action, not a new Module instance or a scalar restriction. The same explicit parameters are used in the two corresponding transport_total arguments. Pinned ModuleCat.Basic defines ofHom from an R-linear map with given X,Y and shows the of/coercion roundtrip is definitionally the original bundled object.

The actual sheaf out map remains canonicalIso.inv, then tilde.functor R applied to the original module-frame out, then tildeSelf.hom. Back remains tildeSelf.inv, then the original back image, then canonicalIso.hom. Thus out followed by back has the same domain and codomain L.object and the same original coefficient ring. The sums run over ALL Fin(moduleFrame R L).n, including a possible empty Fin 0; no generator subset replaces the full identity.

## Exact consumer identity

After the generic binder is corrected, total again consumes the moduleFrame identity. Its ModuleCat.hom projection of the finite sum is now explicitly rewritten with ModuleCat.hom_sum and ModuleCat.hom_id before the unchanged change and exact Frame.total. Finite-sum projection is a theorem, not definitional reduction. This supporting step is part of the repaired total application; the former run did not reach it after transport_total failed to elaborate. It does not claim a separately observed new failure.

The resulting statement is still sum_i out_i≫back_i=id of the SAME original line L.object. OriginalAffineLineLocalHOne318 forgets scalars on that line, transports the same factors to the original additive structure sheaf, and applies ExtFiniteRetractVanishing318.eq_zero on every affine open. These consumers and the source finite-frame theorem remain unchanged. No alternate sheaf, rationalization, local condition or normalization is introduced.

## Verification boundary

Before 7eb0e2ca44e95d362b2f13e5ebe25cc4237d910f43f626acf1e4bfb60d53dccc; candidate 3fbdde87897c3d9717a66718a699166919fbfd69142db085cc350bdc4b00ec42. Only this source changes in the unchanged 107-module closure. Existing resource/transparency options are untouched. Current internal review must check all revised applications anew; no local Lean/Lake, candidate hosted pass, kernel acceptance or full arithmetic theorem claim is made.
