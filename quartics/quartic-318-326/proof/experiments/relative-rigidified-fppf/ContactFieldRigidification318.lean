module
public import RelativeSectionBaseChange318
public import ContactFieldSection318
public section
noncomputable section
namespace ContactFieldRigidification318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactFieldSection318
variable (c : Fin 4 → ℚˣ) (t : ℚ)

/-- The actual source structure map after the explicit field extension. -/
@[expose] def family : pullback (sourceStructure c) (fieldMap c t) ⟶ FieldBase c t :=
  pullback.snd (sourceStructure c) (fieldMap c t)

/-- The original source has section-normalized line classes after an actual
finite etale fppf field cover. This is an equivalence for the full relative
class group, not a degree-zero or representability assertion. -/
@[expose] def relativeEquivalence :
    RelativeLineClassQuotient318.RelativeClass (family c t) ≃*
      (LineClassPullbackHom318.pullback (pointSection c t)).ker :=
  RelativeLineSectionNormalization318.equivalence (family c t) (pointSection c t)
    (pointSection_snd c t)

lemma actual_cover :
    Sieve.generate (Presieve.singleton (fieldMap c t)) ∈ Scheme.fppfTopology Base :=
  fppf_sieve c t

/-- Every original relative class on the actual field-base-changed source
has an actual line representative with an actual section trivialization. -/
lemma actual_rigidified_representatives : Function.Surjective
    (fun L : RelativeRigidifiedLine318.RigidifiedLine (pointSection c t) =>
      RelativeLineClassQuotient318.classMap (family c t)
        (LineSheafClass318.classOf L.line)) :=
  RelativeRigidifiedLine318.relativeClass_surjective (family c t) (pointSection c t)
    (pointSection_snd c t)

/-- The same normalization is available on every further scheme test over
the explicit extension field, not merely over its field-valued points. -/
@[expose] def relativeEquivalenceOn {T : Scheme} (a : T ⟶ FieldBase c t) :
    RelativeLineClassBaseChange318.TestClass (family c t) a ≃*
      (LineClassPullbackHom318.pullback
        (RelativeSectionBaseChange318.sectionOn (family c t) (pointSection c t)
          (pointSection_snd c t) a)).ker :=
  RelativeSectionBaseChange318.equivalenceOn (family c t) (pointSection c t)
    (pointSection_snd c t) a

lemma actual_rigidified_representatives_on {T : Scheme} (a : T ⟶ FieldBase c t) :
    Function.Surjective
      (fun L : RelativeRigidifiedLine318.RigidifiedLine
          (RelativeSectionBaseChange318.sectionOn (family c t) (pointSection c t)
            (pointSection_snd c t) a) =>
        RelativeLineClassQuotient318.classMap (pullback.snd (family c t) a)
          (LineSheafClass318.classOf L.line)) :=
  RelativeSectionBaseChange318.rigidified_representatives_on (family c t)
    (pointSection c t) (pointSection_snd c t) a
end ContactFieldRigidification318
