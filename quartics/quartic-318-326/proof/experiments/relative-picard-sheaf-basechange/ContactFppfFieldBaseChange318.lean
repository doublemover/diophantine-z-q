module
public import RelativeFppfBaseChangeIso318
public import ContactFppfLineSheaf318
public import ContactFieldSection318
public section
noncomputable section
namespace ContactFppfFieldBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeFppfLineSheaf318
open ContactRelativeLinePresheaf318

lemma original_structure_identity :
    ContactFieldSection318.sourceStructure SourceTwistArithmetic318.units =
      ContactRelativeLinePresheaf318.sourceStructure := rfl

/-- The actual associated fppf line-class sheaf of the actual original source
after the explicit finite field base change used to produce its section. -/
@[expose] def sourceAfterField (t : ℚ) :
    Sheaf (topology (ContactFieldSection318.FieldBase SourceTwistArithmetic318.units t))
      CommGrpCat.{1} :=
  sheaf (pullback.snd sourceStructure
    (ContactFieldSection318.fieldMap SourceTwistArithmetic318.units t))

/-- The sheaf on the section-giving field base is the restriction of the same
original rational-base fppf sheaf, via a proved actual base-change isomorphism. -/
@[expose] def sourceIso (t : ℚ) :
    (RelativeFppfBaseChangeIso318.restriction
        (ContactFieldSection318.fieldMap SourceTwistArithmetic318.units t)).obj
          ContactFppfLineSheaf318.source ≅ sourceAfterField t :=
  RelativeFppfBaseChangeIso318.sheafIso sourceStructure
    (ContactFieldSection318.fieldMap SourceTwistArithmetic318.units t)

lemma actual_cover (t : ℚ) :
    Sieve.generate (Presieve.singleton
        (ContactFieldSection318.fieldMap SourceTwistArithmetic318.units t)) ∈
      Scheme.fppfTopology Base :=
  ContactFieldSection318.fppf_sieve SourceTwistArithmetic318.units t

lemma actual_section (t : ℚ) :
    ContactFieldSection318.pointSection SourceTwistArithmetic318.units t ≫
      pullback.snd sourceStructure
        (ContactFieldSection318.fieldMap SourceTwistArithmetic318.units t) = 𝟙 _ :=
  ContactFieldSection318.pointSection_snd SourceTwistArithmetic318.units t
end ContactFppfFieldBaseChange318
