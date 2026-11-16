# Actual line-lifting singleton universe repair

1. inputs: Same CommRingCat Type0 R, original line L, short exact S and actual kernel isomorphism e. No new premise.

2. objects: Same full additive sheaves and original Ext class y.comp hS.extClass.

3. domain: The finite retract index is the one-element PUnit at Sort1 = Type0, instead of an unconstrained universe metavariable. No index removed or added.

4. maps: Exactly same e.hom/e.inv constant family and finite identity sum; same Ext vanishing and section recovery maps.

5. scalars: No action, coefficient or sheaf dictionary change. Only the auxiliary proof index universe is pinned.

6. signatures: Only PUnit becomes PUnit.{1} in the existing fun binder. All public theorem types, proof steps, imports, options and resources unchanged.

7. consumer: Actual ExtFiniteRetractVanishing318.eq_zero quantifies an independent Type* finite index. Constant family supplies no constraint on its universe, matching actual own diagnostics.

8. limits: Source-only existing failure repair. No local Lean or claimed full module resolution, no proof expansion/current packet/publication.

9. verification: Own ed412/run43795160702 has96 full passes including HOne5.430s and LineRestriction2.120s; Lifting fails6.836s solely with unresolved PUnit universe at22–23,1202unreached. Retained native Prelude defines PUnit:Sort u and Unit:Type:=PUnit.

