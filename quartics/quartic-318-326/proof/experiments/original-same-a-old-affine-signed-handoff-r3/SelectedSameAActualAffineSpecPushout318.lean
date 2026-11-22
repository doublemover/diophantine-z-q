module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# A genuine affine scheme fibre gives the literal algebra pushout

The two ordered legs are recovered by fully faithful Spec, so the actual
old cotangent fibre uses the named ring maps and not only an isomorphic ring.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace SelectedSameAActualAffineSpecPushout318

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (T k C B : Type u) [CommRing T] [CommRing k] [CommRing C] [CommRing B]
  [Algebra T k] [Algebra T C] [Algebra T B] [Algebra k B] [Algebra C B]
  [IsScalarTower T C B] [IsScalarTower T k B]

/-- Reflect the genuine pullback along Spec with its actual two projections;
unop makes the represented k-leg the first pushout input. -/
theorem actual_algebra_pushout
    (H : IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap C B)))
      (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      (Spec.map (CommRingCat.ofHom (algebraMap T C)))
      (Spec.map (CommRingCat.ofHom (algebraMap T k)))) :
    Algebra.IsPushout T k C B := by
  have h : IsPullback
      (CommRingCat.ofHom (algebraMap C B)).op
      (CommRingCat.ofHom (algebraMap k B)).op
      (CommRingCat.ofHom (algebraMap T C)).op
      (CommRingCat.ofHom (algebraMap T k)).op :=
    IsPullback.of_map_of_faithful (F := Scheme.Spec) H
  exact CommRingCat.isPushout_iff_isPushout.mp h.unop

end

end SelectedSameAActualAffineSpecPushout318
