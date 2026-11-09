module
public import RelativeFppfRigidifiedLocal318
public import RelativeFppfLineNeutral318
public import ContactFieldRigidification318
public section
noncomputable section
namespace ContactFppfRigidifiedLocal318
open AlgebraicGeometry CategoryTheory Opposite
open ContactFieldSection318 ContactFieldRigidification318
open RelativeFppfLineSheaf318 RelativeFppfRigidifiedLocal318
variable (c : Fin 4 → ℚˣ) (t : ℚ)

/-- The associated fppf sheaf of the actual contact family after the explicit
section-giving field cover. No site-base-change comparison is silently used. -/
@[expose] def sourceSheaf :
    Sheaf (topology (FieldBase c t)) CommGrpCat.{1} := sheaf (family c t)

/-- Every section of this actual source sheaf is fppf-locally represented by
an actual line rigidified along the actual field point, on the full base test. -/
lemma locally_rigidified (T : Over (FieldBase c t))
    (s : (sourceSheaf c t).obj.obj (op T)) :
    Presheaf.imageSieve (unit (family c t)) s ∈ topology (FieldBase c t) T ∧
      ∀ (V : Over (FieldBase c t)) (g : V ⟶ T),
        Presheaf.imageSieve (unit (family c t)) s g ↔
          ∃ L : RelativeRigidifiedLine318.RigidifiedLine
              (RelativeSectionBaseChange318.sectionOn (family c t) (pointSection c t)
                (pointSection_snd c t) V.hom),
            rigidifiedImage (family c t) (pointSection c t) (pointSection_snd c t) V L =
              (sourceSheaf c t).obj.map g.op s :=
  ⟨local_rigidified_cover (family c t) T s,
    fun _ g => local_rigidified_iff (family c t) (pointSection c t)
      (pointSection_snd c t) s g⟩
end ContactFppfRigidifiedLocal318
