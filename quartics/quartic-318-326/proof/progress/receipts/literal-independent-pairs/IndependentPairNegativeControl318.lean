module
public import F3PairIndependence318
public section
namespace IndependentPairNegativeControl318
abbrev V:=ZMod 3×ZMod 3
/-- A two-component vector model. This is a negative control, not a
claim to have constructed a further elliptic Scheme example. -/
def p : Fin 2→V:=fun _=>(1,0)
def q : Fin 2→V:=![(0,1),(1,0)]
theorem globally_distinct : p≠0 ∧ q≠0 ∧ q≠p ∧ q≠ -p:=by decide
theorem globally_independent : LinearIndependent (ZMod 3) ![p,q]:=
  (F3PairIndependence318.pair_iff p q).mpr globally_distinct
theorem second_component_dependent : ¬LinearIndependent (ZMod 3) ![p 1,q 1]:=by
  rw [F3PairIndependence318.pair_iff]
  decide
/-- Even global linear independence of sections is insufficient to replace
the pointwise condition on a disconnected test. -/
theorem not_fiberwise_independent : ¬∀i:Fin 2,LinearIndependent (ZMod 3) ![p i,q i]:=by
  intro h
  exact second_component_dependent (h 1)
end IndependentPairNegativeControl318
