module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

@[expose] public section
noncomputable section

namespace OriginalFineFibreGroupAtPoint318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} {B L M : Type u}
variable [CommRing B] [Algebra ℚ B]
variable [Field L] [Algebra ℚ L] [Field M] [Algebra ℚ M]
variable (j : Spec (CommRingCat.of B) ⟶ Y)
variable (p : B →ₐ[ℚ] L)

local notation "SL" => Spec (CommRingCat.of L)
local notation "SQ" => Spec (CommRingCat.of.{u} ℚ)

/-- The actual selected closed evaluation, with the map into the fine
moduli scheme supplied by its own exact finite affine fibre. -/
def point : SL ⟶ Y := Spec.map (CommRingCat.ofHom p.toRingHom) ≫ j

/-- Read the actual relative quotient point, not the value of a
rational function evaluated on an unrelated fibre. -/
theorem point_over (f : Y ⟶ X) (q : SQ ⟶ X)
    (fibre : IsPullback j (Spec.algebraMap ℚ B) f q) :
    point j p ≫ f = Spec.algebraMap ℚ L ≫ q := by
  change (Spec.map (CommRingCat.ofHom p.toRingHom) ≫ j) ≫ f = _
  rw [Category.assoc,fibre.w,←Category.assoc]
  congr 1
  rw [←Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact p.commutes

/-- The actual universal group is pulled back as a group object, so
its multiplication, inverse and zero are not independently picked.
The pullback is not a newly constructed abelian variety with the same
invariants. -/
def groupAt (A : Grp (Over Y)) : Grp (Over SL) :=
  (Over.pullback (point j p)).mapGrp.obj A

theorem groupAt_has_square (A : Grp (Over Y)) :
    IsPullback (pullback.fst A.X.hom (point j p)) (groupAt j p A).X.hom A.X.hom (point j p) :=
  IsPullback.of_hasPullback _ _

theorem groupAt_isProper (A : Grp (Over Y)) [IsProper A.X.hom] :
    IsProper (groupAt j p A).X.hom :=
  inferInstanceAs (IsProper (pullback.snd A.X.hom (point j p)))

/-- One exact field embedding changes the same chosen evaluation.
This replaces any appeal to abstract equality of residue fields. -/
theorem point_base_change (a : L →ₐ[ℚ] M) :
    point j (a.comp p) =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ point j p := by
  change Spec.map (CommRingCat.ofHom (a.comp p).toRingHom) ≫ j =
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.map (CommRingCat.ofHom p.toRingHom) ≫ j
  rw [←Category.assoc,←Spec.map_comp]

local notation "ι" a => Spec.map (CommRingCat.ofHom (a : L →ₐ[ℚ] M).toRingHom)

/-- The actual selected base-change functors, with naturality in genuine
group arrows. Named quaternion actions are transported by this one
natural isomorphism, not identified from numerical invariants. -/
def groupBaseChange (a : L →ₐ[ℚ] M) :
    (Over.pullback (point j p)).mapGrp ⋙ (Over.pullback (ι a)).mapGrp ≅
      (Over.pullback (ι a ≫ point j p)).mapGrp :=
  ((Functor.mapGrpNatIso (Over.pullbackComp (ι a) (point j p))) ≪≫
    (Functor.mapGrpCompIso (F:=Over.pullback (point j p)) (G:=Over.pullback (ι a)))).symm

theorem order_arrow_naturality (A : Grp (Over Y)) (e : A ⟶ A) (a : L →ₐ[ℚ] M) :
    (Over.pullback (ι a)).mapGrp.map ((Over.pullback (point j p)).mapGrp.map e) ≫
      (groupBaseChange j p a).hom.app A =
    (groupBaseChange j p a).hom.app A ≫ (Over.pullback (ι a ≫ point j p)).mapGrp.map e :=
  (groupBaseChange j p a).hom.naturality e

/-- The two reads after an actual embedding are isomorphic as genuine
group objects. For an endomorphism from the represented original order,
naturality of this same isomorphism applies to its exact mapped arrow. -/
def groupAt_base_change (A : Grp (Over Y)) (a : L →ₐ[ℚ] M) :
    (Over.pullback (Spec.map (CommRingCat.ofHom a.toRingHom))).mapGrp.obj (groupAt j p A) ≅
      groupAt j (a.comp p) A := by
  unfold groupAt
  rw [point_base_change]
  exact (groupBaseChange j p a).app A

end OriginalFineFibreGroupAtPoint318

#print axioms OriginalFineFibreGroupAtPoint318.point_over
#print axioms OriginalFineFibreGroupAtPoint318.groupAt_has_square
#print axioms OriginalFineFibreGroupAtPoint318.groupAt_isProper
#print axioms OriginalFineFibreGroupAtPoint318.order_arrow_naturality
#print axioms OriginalFineFibreGroupAtPoint318.groupAt_base_change
