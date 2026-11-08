module
public import RegularUnitMultiple318
public section
noncomputable section
namespace KaehlerModuleMultiple318
/-- The scalar action inherited from the supplied module structure. -/
@[expose] def projectedMultiple {K V:Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (ω ξ:V):Prop:=∃a:K,ω=a • ξ
/-- Compare inherited module scalars with the original direct Kähler action
while the base and algebra rings are still abstract. -/
theorem to_direct {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]
    (ω ξ:KaehlerDifferential R S) (h:projectedMultiple (K:=S) ω ξ):
    ∃a:S,ω=a • ξ:=h
end KaehlerModuleMultiple318
