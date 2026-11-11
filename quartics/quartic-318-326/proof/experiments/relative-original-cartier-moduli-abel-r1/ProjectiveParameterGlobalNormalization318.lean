module
public import ProjectiveParameterPrincipalIntersection318
public section
noncomputable section
namespace ProjectiveParameterGlobalNormalization318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "U" => ProjectiveParameterPrincipalCover318.cover R P
local notation "W" => ProjectiveParameterPrincipalCover318.locus R P
local notation "n" => ProjectiveParameterPrincipalNormalization318.map R P
local notation "j" => ProjectiveParameterPrincipalCover318.into R P

lemma compatible (i k : Fin F.size) : pullback.fst (j i) (j k) ≫ n i=
    pullback.snd (j i) (j k) ≫ n k := by
  let h := ProjectiveParameterPrincipalIntersection318.cartesian R P i k
  apply (cancel_epi h.isoPullback.hom).mp
  simpa only [← Category.assoc,h.isoPullback_hom_fst,h.isoPullback_hom_snd] using
    ProjectiveParameterPrincipalIntersection318.normalization R P i k

/-- The genuine normalization MORPHISM from the ORIGINAL nonzero
section parameter open to the actual glued projective parameter scheme.
It is glued on a proved full affine cover with genuine Cartesian
intersection identities, not constructed from geometric points. -/
@[expose] def map : W.toScheme ⟶ ProjectiveParameterSliceGluing318.scheme R P :=
  U.glueMorphisms n (compatible R P)
@[reassoc] lemma on_chart (i : Fin F.size) : j i ≫ map R P=n i :=
  U.ι_glueMorphisms n (compatible R P) i

/-- The global quotient candidate retains the ORIGINAL coefficient base
projection on the whole scheme, including all nilpotent structure. -/
lemma over_base : map R P ≫ ProjectiveParameterSliceBase318.projection R P=
    W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  apply U.hom_ext
  intro i
  change j i ≫ map R P ≫ ProjectiveParameterSliceBase318.projection R P=
    j i ≫ W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
  rw [← Category.assoc,on_chart,ProjectiveParameterPrincipalNormalization318.over_base,
    ← Category.assoc,ProjectiveParameterPrincipalCover318.into_affine,
    ProjectiveParameterPrincipalCover318.affineInto,← Spec.map_comp]
  rfl

lemma unique (g : W.toScheme ⟶ ProjectiveParameterSliceGluing318.scheme R P)
    (hg : ∀ i,j i ≫ g=n i) : g=map R P := by
  apply U.hom_ext
  intro i
  exact (hg i).trans (on_chart R P i).symm
end ProjectiveParameterGlobalNormalization318
