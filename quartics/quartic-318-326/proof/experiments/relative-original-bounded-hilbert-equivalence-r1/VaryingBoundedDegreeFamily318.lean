module
public import VaryingFreeIdealClassifyingMap318
public import Lean.Elab.Tactic.Omega
public section
noncomputable section
namespace VaryingBoundedDegreeFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
abbrev Index (d : ℕ) := ULift.{u} (Fin d)
abbrev degreeParameter (d : ℕ) : Scheme.{u} := VaryingWordChartGluing318.scheme R A (Index.{u} d)
abbrev degreeFamily (d : ℕ) : Scheme.{u} := VaryingWordFamilyGluing318.scheme R A (Index.{u} d)
abbrev degreeProjection (d : ℕ) : degreeFamily R A d ⟶ degreeParameter R A d :=
  VaryingWordGlobalFamilyProjection318.projection R A (Index.{u} d)
abbrev degreeStructure (d : ℕ) : degreeParameter R A d ⟶ Spec (CommRingCat.of R) :=
  VaryingWordParameterStructure318.structureMap R A (Index.{u} d)

/-- The finite disjoint union of ranks zero through n. It allows different
ranks on different open-and-closed test components; no connectedness assumed. -/
@[expose] def parameter : ℕ → Scheme.{u}
  | 0 => degreeParameter R A 0
  | n+1 => parameter R A n ⨿ degreeParameter R A (n+1)
@[expose] def family : ℕ → Scheme.{u}
  | 0 => degreeFamily R A 0
  | n+1 => family R A n ⨿ degreeFamily R A (n+1)
@[expose] def projection : ∀ n, family R A n ⟶ parameter R A n
  | 0 => degreeProjection R A 0
  | n+1 => coprod.map (projection R A n) (degreeProjection R A (n+1))
@[expose] def structureMap : ∀ n, parameter R A n ⟶ Spec (CommRingCat.of R)
  | 0 => degreeStructure R A 0
  | n+1 => coprod.desc (structureMap R A n) (degreeStructure R A (n+1))

/-- Bounded-degree family is genuinely finite flat, by locality on each
actual disjoint parameter component. This does not assert representability. -/
theorem properties (n : ℕ) : IsFinite (projection R A n) ∧ Flat (projection R A n) := by
  induction n with
  | zero => exact VaryingWordGlobalFiniteFlat318.properties R A (Index.{u} 0)
  | succ n ih =>
    exact ⟨IsZariskiLocalAtTarget.coprodMap (P:=@IsFinite)
      (projection R A n) (degreeProjection R A (n+1)) ih.1 inferInstance,
      IsZariskiLocalAtTarget.coprodMap (P:=@Flat)
      (projection R A n) (degreeProjection R A (n+1)) ih.2 inferInstance⟩

@[expose] def inclusion : (n d : ℕ) → d ≤ n → (degreeParameter R A d ⟶ parameter R A n)
  | 0,0,_ => 𝟙 _
  | 0,d+1,h => False.elim (by omega)
  | n+1,d,h => if he : d=n+1 then
      eqToHom (congrArg (degreeParameter R A) he) ≫ coprod.inr
    else inclusion R A n d (by omega) ≫ coprod.inl
@[reassoc] lemma inclusion_structure (n d : ℕ) (h : d ≤ n) :
    inclusion R A n d h ≫ structureMap R A n=degreeStructure R A d := by
  induction n generalizing d with
  | zero =>
    have hd : d=0 := by omega
    subst d
    simp only [inclusion,structureMap,Category.id_comp]
  | succ n ih =>
    by_cases he : d=n+1
    · subst d
      simp only [inclusion,dif_pos rfl,eqToHom_refl,Category.id_comp,structureMap,coprod.inr_desc]
    · rw [inclusion,dif_neg he,Category.assoc]
      change inclusion R A n d _ ≫ (coprod.inl ≫ coprod.desc _ _)=_
      rw [coprod.inl_desc]
      exact ih d (by omega)
end VaryingBoundedDegreeFamily318
