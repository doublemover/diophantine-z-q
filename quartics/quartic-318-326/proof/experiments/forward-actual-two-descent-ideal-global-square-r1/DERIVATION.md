# Ambient local data from actual native chart adjoints

## Exact ambient coefficient ring
For j:Y->X an open immersion and V<=range(j),the exact identity j(image preimage V)=V identifies the original ambient section ring with the section ring on that image. Compose its native presheaf equality-isomorphism with j.appIso(preimage V). The resulting ambientRingIso has hom exactly j.app(V),as follows from j.app_appIso_inv. Thus its inverse is not a new coordinate choice.

## Linear chart value and naturality
For f:M|j->O_Y,use the native restriction adjoint A:M->j_*O_Y. On V define coordinate(s)=ambientRingIso.inv(A.app(V)(s)). The adjoint is linear over the original ring via the actual j.app(V) action;the ring inverse transports that scalar back literally. This proves original-ring linearity. Applying j.app(W) to a restriction equation reduces it to naturality of A and of StructurePushforwardSplit.unitMap(j),both on the same original opens. Injectivity of the actual ring isomorphism then proves all-subopen coordinate naturality.

## Bijectivity,not generic detection
If f is an actual chart isomorphism,A.app(V) is f.app(preimage V) after the native adjunction unit. Since V is contained in the chart image,that unit is M.presheaf.map along an EQUALITY of opens,and is bijective. The actual chart isomorphism and ambient ring inverse are bijective too. Their composition therefore gives ambient-coordinate bijectivity on EVERY subopen. No affine/global-section or stalk test is substituted.

## Exact refinement invariance
For k:Z->Y and m:Z->X with k>>j=m,the predecessor defines the actual refined value using native restriction composition and equality transport. Its adjoint is A followed by the old pushed structure restriction and pushforwardCongr. Applying m.app(V) to both candidate ambient coordinates reduces their equality to this exact adjoint formula and the actual composition of scheme.app maps. This identifies the original chart coordinate with the same common-chart coordinate on all ambient subopens inside m's full image.

## Actual original compatible atlas
Index the old three charts by Option Bool: infinity and the two principal affine charts. The chartSquare is literally the old infinitySquareChart or affineSquareChart. Their factor maps from the complete original common chart are the old intoInfinity/intoRootChart maps;their ambient equality transports are the old original chart square/refinement equations. The previous packets prove each actual refined square equals matchedSquareIso.hom. Every distinct pair has EXACTLY the common-chart image as full intersection. Hence any ambient subopen in both charts is in the common image,where refinement invariance proves the two coordinates equal. Identical chart indices use the same map and proof-irrelevance. This supplies actual LocalData,including naturality and compatibility,with no matching hypothesis.

## Global construction and exact normalization
The original actual_open_cover theorem gives top<=sup opens for n!=0. Native ModuleLocalIsomorphism318.iso takes the constructed LocalData and produced every-subopen bijectivity. It glues the map and inverse separately using ModuleLocalGluing318,proves their two compositions by equality on the same full cover,and returns the actual original tensor-square-to-O isomorphism. Its value_subopen formula proves the global map has exactly the old chart coordinate on every original ambient subopen,so no scalar normalization is forgotten.

## History and boundary
ModuleLocalIsomorphism318 already provides map/inverse gluing;this packet reuses it rather than presenting generic gluing as a new mathematical gap. The new bridge constructs the required ORIGINAL ambient LocalData from actual old chart compatibility. No integral-model normality,global divisor identity,theta group,geometric Weil pairing,Brauer invariant or Cassels--Tate conclusion is claimed. In the standard divisor section-sheaf convention the earlier fractional ideal suggests O(O-Ta),not O(Ta-O);formal divisor identification remains a separate next step. No local Lean was run.
