module
public import ContactRelativeFppfSheaf318
public import RelativeFppfLineSheaf318
public section
noncomputable section
namespace ContactNaiveFppfIdentification318
open AlgebraicGeometry CategoryTheory Opposite
open ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ)

/-- The unchanged relative Picard group presheaf is a sheaf, not merely
its underlying set with an unrelated group structure. -/
lemma group_isSheaf : Presheaf.IsSheaf (RelativeFppfLineSheaf318.topology (FieldBase t))
    (RelativeLineClassBaseChange318.presheaf (q t)) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat),
    isSheaf_iff_isSheaf_of_type]
  exact ContactRelativeFppfSheaf318.isSheaf t

/-- The existing original relative groups themselves, as a sheaf on the
same old big fppf site. This does not assert a representing scheme. -/
@[expose] def naiveSheaf : Sheaf (RelativeFppfLineSheaf318.topology (FieldBase t)) CommGrpCat.{1} :=
  ⟨RelativeLineClassBaseChange318.presheaf (q t),group_isSheaf t⟩

@[expose] def inverse : RelativeFppfLineSheaf318.sheaf (q t) ⟶ naiveSheaf t :=
  RelativeFppfLineSheaf318.lift (q t) (naiveSheaf t) (𝟙 _)

lemma unit_inverse : RelativeFppfLineSheaf318.unit (q t) ≫ (inverse t).hom = 𝟙 _ :=
  RelativeFppfLineSheaf318.unit_lift (q t) (naiveSheaf t) (𝟙 _)

lemma inverse_unit : (inverse t).hom ≫ RelativeFppfLineSheaf318.unit (q t) = 𝟙 _ := by
  apply sheafify_hom_ext (RelativeFppfLineSheaf318.topology (FieldBase t)) _ _
    (RelativeFppfLineSheaf318.sheaf (q t)).property
  change RelativeFppfLineSheaf318.unit (q t) ≫
    ((inverse t).hom ≫ RelativeFppfLineSheaf318.unit (q t)) =
      RelativeFppfLineSheaf318.unit (q t) ≫ 𝟙 _
  rw [← Category.assoc,unit_inverse,Category.id_comp,Category.comp_id]

/-- The actual old sheafification unit is an isomorphism. Its forward
map is literally the previous universal map, not a replacement chosen
by an abstract existence or representability hypothesis. -/
@[expose] def presheafIso : RelativeLineClassBaseChange318.presheaf (q t) ≅
    (RelativeFppfLineSheaf318.sheaf (q t)).obj where
  hom := RelativeFppfLineSheaf318.unit (q t)
  inv := (inverse t).hom
  hom_inv_id := unit_inverse t
  inv_hom_id := inverse_unit t

@[expose] def sheafIso : naiveSheaf t ≅ RelativeFppfLineSheaf318.sheaf (q t) where
  hom := ⟨RelativeFppfLineSheaf318.unit (q t)⟩
  inv := inverse t
  hom_inv_id := by apply Sheaf.hom_ext; exact unit_inverse t
  inv_hom_id := by apply Sheaf.hom_ext; exact inverse_unit t

/-- The same original classes and original canonical unit on every test,
including arbitrary non-affine and nonreduced tests. -/
@[expose] def testIso {T : Scheme} (b : T ⟶ FieldBase t) :=
  (presheafIso t).app (op (Over.mk b))

lemma testIso_hom {T : Scheme} (b : T ⟶ FieldBase t) :
    (testIso t b).hom = (RelativeFppfLineSheaf318.unit (q t)).app (op (Over.mk b)) := rfl
end ContactNaiveFppfIdentification318
