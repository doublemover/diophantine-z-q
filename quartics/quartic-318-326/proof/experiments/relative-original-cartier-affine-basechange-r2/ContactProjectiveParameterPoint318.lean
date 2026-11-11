module
public import ContactProjectiveParameterIntersection318
public section
noncomputable section
namespace ContactProjectiveParameterPoint318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
abbrev Point := {f : Spec S ⟶ ContactProjectiveQuotientParameter318.scheme c n //
  f ≫ ContactProjectiveParameterStructure318.structureMap c n=VaryingSourceCoefficientPullback318.base ℚ S}
@[expose] def ofIdeal (a : Chart) (I : Ideal c a S n) : Point c n S :=
  ⟨(VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) S I).val ≫
    ContactProjectiveQuotientParameter318.into c n a,by
      rw [Category.assoc,ContactProjectiveParameterStructure318.into_structureMap]
      exact (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) S I).property⟩
variable (T : CommRingCat.{0}) [Algebra ℚ T] (φ : S →ₐ[ℚ] T)
@[expose] def map (x : Point c n S) : Point c n T :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ x.val,by
    rw [Category.assoc,x.property]
    exact VaryingSourceCoefficientPullback318.coefficient_base ℚ S T φ⟩
lemma ofIdeal_natural (a : Chart) (I : Ideal c a S n) :
    ofIdeal c n T a (ContactQuotientChartCoefficient318.extended c a S T φ n I)=
      map c n S T φ (ofIdeal c n S a I) := by
  apply Subtype.ext
  change (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) T
    (VaryingProjectiveQuotientNaturality318.mapIdeal ℚ (ring c a) (Fin n) S T φ I)).val ≫ _=_
  rw [VaryingProjectiveQuotientNaturality318.classify_natural]
  exact Category.assoc _ _ _
end ContactProjectiveParameterPoint318
