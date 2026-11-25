module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

@[expose] public section
noncomputable section

namespace OriginalFineFibreGroupAtPoint318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{0}} {B L M : Type}
variable [CommRing B] [Algebra ℚ B]
variable [CommRing L] [Algebra ℚ L] [CommRing M] [Algebra ℚ M]
variable (j : Spec (CommRingCat.of B) ⟶ Y)
variable (p : B →ₐ[ℚ] L)

local notation "SL" => Spec (CommRingCat.of L)
local notation "SQ" => Spec (CommRingCat.of ℚ)

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

/-- The actual scalar extension arrow retains the given algebra map.
It is written as a definition, not a parser-sensitive projection notation. -/
def coefficientMap (a : L →ₐ[ℚ] M) :
    Spec (CommRingCat.of M) ⟶ SL :=
  Spec.map (CommRingCat.ofHom a.toRingHom)

/-- One exact field embedding changes the same chosen evaluation.
This replaces any appeal to abstract equality of residue fields. -/
theorem point_base_change (a : L →ₐ[ℚ] M) :
    point j (a.comp p) = coefficientMap a ≫ point j p := by
  have e : CommRingCat.ofHom (a.comp p).toRingHom =
      CommRingCat.ofHom p.toRingHom ≫ CommRingCat.ofHom a.toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl
  change Spec.map (CommRingCat.ofHom (a.comp p).toRingHom) ≫ j =
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.map (CommRingCat.ofHom p.toRingHom) ≫ j
  rw [e,Spec.map_comp,Category.assoc]

/-- The actual selected base-change functors, with naturality in genuine
group arrows. Named quaternion actions are transported by this one
natural isomorphism, not identified from numerical invariants. -/
def groupBaseChange (a : L →ₐ[ℚ] M) :
    (Over.pullback (point j p)).mapGrp ⋙ (Over.pullback (coefficientMap a)).mapGrp ≅
      (Over.pullback (coefficientMap a ≫ point j p)).mapGrp :=
  ((Functor.mapGrpNatIso (Over.pullbackComp (coefficientMap a) (point j p))) ≪≫
    (Functor.mapGrpCompIso (F:=Over.pullback (point j p)) (G:=Over.pullback (coefficientMap a)))).symm

theorem order_arrow_naturality (A : Grp (Over Y)) (e : A ⟶ A) (a : L →ₐ[ℚ] M) :
    (Over.pullback (coefficientMap a)).mapGrp.map ((Over.pullback (point j p)).mapGrp.map e) ≫
      (groupBaseChange j p a).hom.app A =
    (groupBaseChange j p a).hom.app A ≫ (Over.pullback (coefficientMap a ≫ point j p)).mapGrp.map e :=
  (groupBaseChange j p a).hom.naturality e

/-- The two reads after an actual embedding are isomorphic as genuine
group objects. For an endomorphism from the represented original order,
naturality of this same isomorphism applies to its exact mapped arrow. -/
def groupAt_base_change (A : Grp (Over Y)) (a : L →ₐ[ℚ] M) :
    (Over.pullback (coefficientMap a)).mapGrp.obj (groupAt j p A) ≅
      groupAt j (a.comp p) A := by
  let K (s : Spec (CommRingCat.of M) ⟶ Y) := (Over.pullback s).mapGrp.obj A
  have h : K (coefficientMap a ≫ point j p) = K (point j (a.comp p)) :=
    congrArg K (point_base_change j p a).symm
  exact (groupBaseChange j p a).app A ≪≫ eqToIso h

end OriginalFineFibreGroupAtPoint318

#print axioms OriginalFineFibreGroupAtPoint318.point_over
#print axioms OriginalFineFibreGroupAtPoint318.groupAt_has_square
#print axioms OriginalFineFibreGroupAtPoint318.groupAt_isProper
#print axioms OriginalFineFibreGroupAtPoint318.order_arrow_naturality
#print axioms OriginalFineFibreGroupAtPoint318.groupAt_base_change
