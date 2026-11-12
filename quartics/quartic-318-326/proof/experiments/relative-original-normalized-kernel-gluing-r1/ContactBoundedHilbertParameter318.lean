module
public import SchemeSigmaFamilyCartesian318
public section
noncomputable section
namespace ContactBoundedHilbertParameter318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ)
abbrev component (d : Fin (N+1)) := ContactProjectiveQuotientParameter318.scheme c d.val
abbrev familyComponent (d : Fin (N+1)) := ContactProjectiveUniversalGluing318.family c d.val
abbrev componentProjection (d : Fin (N+1)) := ContactProjectiveUniversalProjection318.projection c d.val
/-- Actual disjoint union of ranks zero through N. Test schemes may
meet different rank components; connectedness is NOT assumed. -/
abbrev scheme : Scheme.{0} := ∐ component c N
abbrev family : Scheme.{0} := ∐ familyComponent c N
abbrev into (d : Fin (N+1)) : component c N d ⟶ scheme c N := Sigma.ι (component c N) d
abbrev familyInto (d : Fin (N+1)) : familyComponent c N d ⟶ family c N := Sigma.ι (familyComponent c N) d
abbrev projection : family c N ⟶ scheme c N :=
  SchemeSigmaFamilyCartesian318.map (familyComponent c N) (component c N) (componentProjection c N)
@[expose] def structureMap : scheme c N ⟶ Spec (CommRingCat.of ℚ) :=
  Sigma.desc (fun d => ContactProjectiveParameterStructure318.structureMap c d.val)
@[reassoc] lemma into_structure (d : Fin (N+1)) : into c N d ≫ structureMap c N=
    ContactProjectiveParameterStructure318.structureMap c d.val := Sigma.ι_desc _ _
lemma cartesian (d : Fin (N+1)) : IsPullback (familyInto c N d) (componentProjection c N d)
    (projection c N) (into c N d) := SchemeSigmaFamilyCartesian318.cartesian _ _ _ d
abbrev cover : (scheme c N).OpenCover := Scheme.sigmaOpenCover (component c N)
instance finite : IsFinite (projection c N) := by
  apply IsZariskiLocalAtTarget.of_openCover (cover c N)
  intro d
  rw [← (cartesian c N d).isoPullback_inv_snd]
  infer_instance
instance flat : Flat (projection c N) := by
  apply IsZariskiLocalAtTarget.of_openCover (cover c N)
  intro d
  rw [← (cartesian c N d).isoPullback_inv_snd]
  infer_instance
instance presentation : LocallyOfFinitePresentation (projection c N) := by
  apply IsZariskiLocalAtTarget.of_openCover (cover c N)
  intro d
  rw [← (cartesian c N d).isoPullback_inv_snd]
  infer_instance
lemma rank_component (d : Fin (N+1)) (x : component c N d) :
    (projection c N).finrank (into c N d x)=d.val := by
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ (cartesian c N d)]
  exact ContactProjectiveUniversalRank318.rank c d.val x
lemma rank_bound (x : scheme c N) : (projection c N).finrank x≤N := by
  obtain ⟨d,y,rfl⟩ := (cover c N).exists_eq x
  rw [rank_component]
  exact Nat.le_of_lt_succ d.isLt
lemma rank_iff_component (d : Fin (N+1)) (x : scheme c N) :
    (projection c N).finrank x=d.val ↔ x∈Set.range (into c N d) := by
  constructor
  · intro h
    obtain ⟨e,y,rfl⟩ := (cover c N).exists_eq x
    rw [rank_component] at h
    have he : e=d := Fin.ext h
    subst e
    exact ⟨y,rfl⟩
  · rintro ⟨y,rfl⟩
    exact rank_component c N d y
end ContactBoundedHilbertParameter318
