module
public import FamilyIntrinsicDifferentials318
public section
noncomputable section
namespace IntrinsicHodgeComparison318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
section CategoryEvaluation
variable {C D : Type u} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C}

/-- Restriction through an adjunction and a specified section of its left functor. -/
@[expose] def evaluation (adj : F ⊣ G) (α : F ⋙ H ≅ 𝟭 C) : G ⟶ H where
  app M := α.inv.app (G.obj M) ≫ H.map (adj.counit.app M)
  naturality {M N} f := by
    have h := α.inv.naturality (G.map f)
    have hc := congrArg (fun k => H.map k) (adj.counit.naturality f)
    simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h
    simp only [Functor.map_comp, Functor.comp_map, Functor.id_map] at hc
    rw [←Category.assoc, h, Category.assoc, hc, Category.assoc]

/-- The unit normalization follows from the actual adjunction triangle identity. -/
theorem unit_evaluation (adj : F ⊣ G) (α : F ⋙ H ≅ 𝟭 C) (N : C) :
    adj.unit.app N ≫ (evaluation adj α).app (F.obj N) = α.inv.app N := by
  have h := α.inv.naturality (adj.unit.app N)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h
  change _ ≫ (_ ≫ _) = _
  rw [←Category.assoc, h, Category.assoc, ←Functor.map_comp]
  simp
end CategoryEvaluation

variable {X S : Scheme.{u}}

/-- Pulling back along a genuine section cancels pulling back along the structure
map. This is the actual Scheme.Modules functor comparison. -/
@[expose] def sectionPullbackIso (p : X ⟶ S) (e : S ⟶ X)
    (he : e ≫ p = 𝟙 S) :
    Scheme.Modules.pullback p ⋙ Scheme.Modules.pullback e ≅ 𝟭 S.Modules :=
  Scheme.Modules.pullbackComp e p ≪≫
    Scheme.Modules.pullbackCongr he ≪≫ Scheme.Modules.pullbackId S

/-- The canonical restriction of global relative sections to a section. It is
formed from the actual pullback/pushforward counit, not an assumed Hodge map. -/
@[expose] def evaluateAtSection (p : X ⟶ S) (e : S ⟶ X)
    (he : e ≫ p = 𝟙 S) (M : X.Modules) :
    (Scheme.Modules.pushforward p).obj M ⟶ (Scheme.Modules.pullback e).obj M :=
  (evaluation (Scheme.Modules.pullbackPushforwardAdjunction p)
    (sectionPullbackIso p e he)).app M

/-- Restriction to the identity respects every actual O-module morphism. -/
theorem evaluateAtSection_naturality (p : X ⟶ S) (e : S ⟶ X)
    (he : e ≫ p = 𝟙 S) {M N : X.Modules} (f : M ⟶ N) :
    (Scheme.Modules.pushforward p).map f ≫ evaluateAtSection p e he N =
      evaluateAtSection p e he M ≫ (Scheme.Modules.pullback e).map f :=
  (evaluation (Scheme.Modules.pullbackPushforwardAdjunction p)
    (sectionPullbackIso p e he)).naturality f

/-- On a pulled-back sheaf, restriction to the section is normalized by the
actual adjunction unit. This is a triangle-identity theorem, not a chosen frame. -/
theorem unit_evaluateAtSection (p : X ⟶ S) (e : S ⟶ X)
    (he : e ≫ p = 𝟙 S) (N : S.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N ≫
      evaluateAtSection p e he ((Scheme.Modules.pullback p).obj N) =
        (sectionPullbackIso p e he).inv.app N :=
  unit_evaluation (Scheme.Modules.pullbackPushforwardAdjunction p)
    (sectionPullbackIso p e he) N

/-- A genuine splitting of evaluation for sheaves pulled back from the base. -/
@[expose] def pullbackEvaluationSection (p : X ⟶ S) (e : S ⟶ X)
    (he : e ≫ p = 𝟙 S) (N : S.Modules) :
    (Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback p).obj N) ⟶
      (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj N) :=
  (sectionPullbackIso p e he).hom.app N ≫
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N

theorem pullbackEvaluationSection_evaluate (p : X ⟶ S) (e : S ⟶ X)
    (he : e ≫ p = 𝟙 S) (N : S.Modules) :
    pullbackEvaluationSection p e he N ≫
      evaluateAtSection p e he ((Scheme.Modules.pullback p).obj N) = 𝟙 _ := by
  unfold pullbackEvaluationSection
  rw [Category.assoc, unit_evaluateAtSection]
  exact (sectionPullbackIso p e he).hom_inv_id_app N

variable {R : Type u} [CommRing R]

/-- The Hodge pushforward is now the pushforward of the intrinsic universal
relative differential sheaf of the actual glued family. -/
@[expose] def hodge (A B : R) : (Spec (CommRingCat.of R)).Modules :=
  (Scheme.Modules.pushforward (WeierstrassGluing318.structureMap A B)).obj
    (FamilyIntrinsicDifferentials318.familyOmega A B)

/-- Intrinsic relative cotangent at the genuine global identity. -/
@[expose] def identityCotangent (A B : R) : (Spec (CommRingCat.of R)).Modules :=
  (Scheme.Modules.pullback (WeierstrassGluing318.infinity A B)).obj
    (FamilyIntrinsicDifferentials318.familyOmega A B)

/-- The actual, unconditional comparison morphism pi_*Omega -> e^*Omega.
Its invertibility is deliberately not asserted here. -/
@[expose] def hodgeToIdentity (A B : R) : hodge A B ⟶ identityCotangent A B :=
  evaluateAtSection (WeierstrassGluing318.structureMap A B)
    (WeierstrassGluing318.infinity A B) (WeierstrassGluing318.infinity_section A B)
    (FamilyIntrinsicDifferentials318.familyOmega A B)

@[expose] def literalHodge (N : ℕ) := hodge (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
@[expose] def literalIdentityCotangent (N : ℕ) :=
  identityCotangent (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
@[expose] def literalHodgeToIdentity (N : ℕ) :=
  hodgeToIdentity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
end IntrinsicHodgeComparison318
