module
public import OriginalR40ActualOldChartMaps318
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public section

namespace OriginalR47TrueNodeSite318
open AlgebraicGeometry CategoryTheory
open OriginalThickCentralReesChart318 (O I)

/-- The exact local datum a stable mixed-characteristic curve must
supply at each chosen thick node. The DVR and its uniformizer remain
the same in the derived successor, and its new point is the one the
previous actual Rees round produces. The actual thickness is d+2. -/
structure Site (X : Scheme) (x : X) (d : ℕ) where
  R : Type
  [comm : CommRing R]
  [domain : IsDomain R]
  [dvr : IsDiscreteValuationRing R]
  q : R
  q_irred : Irreducible q
  U : Scheme
  u : U
  into : U ⟶ X
  split : U ⟶ Spec (CommRingCat.of (O q d))
  [flat : Flat into]
  [unram : FormallyUnramified into]
  [finite : LocallyOfFiniteType into]
  [flatSplit : Flat split]
  [unramSplit : FormallyUnramified split]
  [finiteSplit : LocallyOfFiniteType split]
  read : into u = x
  literal : (split u).asIdeal = I q d

attribute [instance] Site.comm Site.domain Site.dvr Site.flat Site.unram Site.finite
  Site.flatSplit Site.unramSplit Site.finiteSplit

end OriginalR47TrueNodeSite318

#print axioms OriginalR47TrueNodeSite318.Site
