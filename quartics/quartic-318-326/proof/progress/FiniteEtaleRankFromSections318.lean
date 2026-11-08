module
public import FiniteEtaleGeometricRank318
public section
noncomputable section
namespace FiniteEtaleRankFromSections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme} (f : X ⟶ S) [IsFinite f] [Etale f]
/-- Rank descends from actual geometric sections via an algebraic closure of each residue field
and the actual cartesian section equivalence. No pointwise map-isomorphism claim is used. -/
theorem rank_eq (d : ℕ)
    (h : ∀ (F : Type) [Field F] [IsAlgClosed F] (b : Spec (CommRingCat.of F) ⟶ S),
      Nat.card {s : Spec (CommRingCat.of F) ⟶ X // s ≫ f = b} = d)
    (x : S) : f.finrank x = d := by
  let F := AlgebraicClosure (S.residueField x)
  let b : Spec (CommRingCat.of F) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) F)) ≫ S.fromSpecResidueField x
  let y := IsLocalRing.closedPoint F
  have hb : b y = x := Scheme.fromSpecResidueField_apply x _
  have hc : Nat.card {s : Spec (CommRingCat.of F) ⟶ pullback f b //
      s ≫ pullback.snd f b = 𝟙 _} = d :=
    (Nat.card_congr (CartesianSectionPoints318.equiv (IsPullback.of_hasPullback f b))).trans (h F b)
  calc
    f.finrank x = (pullback.snd f b).finrank y := by
      rw [Scheme.Hom.finrank_pullback_snd,hb]
    _ = Nat.card {s : Spec (CommRingCat.of F) ⟶ pullback f b //
        s ≫ pullback.snd f b = 𝟙 _} :=
      (FiniteEtaleGeometricRank318.card_sections_eq_rank F (pullback.snd f b)).symm
    _ = d := hc
end FiniteEtaleRankFromSections318
