module
public import OriginalActualKSEtaleRestriction318
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
The final ordinary Scheme-level gluing for the actual corrected
Kodaira–Spencer overlaps. R106 and R107 compute the matched overlap
arrows from the literal cochain; this file assembles those arrows and
their inverses without manipulating global automorphism at the point.
-/
@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace OriginalActualKSSchemeGlue318

universe u
variable {X Y : Scheme.{u}} (U : Scheme.OpenCover.{u} X) (V : Scheme.OpenCover.{u} Y)
variable (idx : U.I₀ ≃ V.I₀)

abbrev indexed := V.reindex idx

/-- The two actual open-cover diagrams after applying Spec to the
cochain corrections. Both overlap projections are part of the data,
not merely equality of the induced topological images. -/
structure Corrected where
  chart : ∀ i : U.I₀, U.X i ≅ (indexed U V idx).X i
  overlap : ∀ i j : U.I₀,
    pullback (U.f i) (U.f j) ≅
      pullback ((indexed U V idx).f i) ((indexed U V idx).f j)
  first_read : ∀ i j,
    pullback.fst (U.f i) (U.f j) ≫ (chart i).hom =
      (overlap i j).hom ≫ pullback.fst ((indexed U V idx).f i) ((indexed U V idx).f j)
  second_read : ∀ i j,
    pullback.snd (U.f i) (U.f j) ≫ (chart j).hom =
      (overlap i j).hom ≫ pullback.snd ((indexed U V idx).f i) ((indexed U V idx).f j)

variable (D : Corrected U V idx)

private theorem first_inverse (i j : U.I₀) :
    pullback.fst ((indexed U V idx).f i) ((indexed U V idx).f j) ≫ (D.chart i).inv =
      (D.overlap i j).inv ≫ pullback.fst (U.f i) (U.f j) := by
  rw [← cancel_mono (D.chart i).hom]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,D.first_read]
  rw [← Category.assoc,Iso.inv_hom_id,Category.id_comp]

private theorem second_inverse (i j : U.I₀) :
    pullback.snd ((indexed U V idx).f i) ((indexed U V idx).f j) ≫ (D.chart j).inv =
      (D.overlap i j).inv ≫ pullback.snd (U.f i) (U.f j) := by
  rw [← cancel_mono (D.chart j).hom]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,D.second_read]
  rw [← Category.assoc,Iso.inv_hom_id,Category.id_comp]

private def forwards (i : U.I₀) : U.X i ⟶ Y :=
  (D.chart i).hom ≫ (indexed U V idx).f i

private def backwards (i : U.I₀) : (indexed U V idx).X i ⟶ X :=
  (D.chart i).inv ≫ U.f i

private theorem forwards_agree (i j : U.I₀) :
    pullback.fst (U.f i) (U.f j) ≫ forwards U V idx D i =
      pullback.snd (U.f i) (U.f j) ≫ forwards U V idx D j := by
  calc
    _ = (D.overlap i j).hom ≫
        (pullback.fst ((indexed U V idx).f i) ((indexed U V idx).f j) ≫
          (indexed U V idx).f i) := by
        simpa only [forwards,Category.assoc] using
          congrArg (fun e => e ≫ (indexed U V idx).f i) (D.first_read i j)
    _ = (D.overlap i j).hom ≫
        (pullback.snd ((indexed U V idx).f i) ((indexed U V idx).f j) ≫
          (indexed U V idx).f j) := by rw [pullback.condition]
    _ = _ := by
        simpa only [forwards,Category.assoc] using
          congrArg (fun e => e ≫ (indexed U V idx).f j) (D.second_read i j).symm

private theorem backwards_agree (i j : U.I₀) :
    pullback.fst ((indexed U V idx).f i) ((indexed U V idx).f j) ≫ backwards U V idx D i =
      pullback.snd ((indexed U V idx).f i) ((indexed U V idx).f j) ≫ backwards U V idx D j := by
  calc
    _ = (D.overlap i j).inv ≫
        (pullback.fst (U.f i) (U.f j) ≫ U.f i) := by
      simpa only [backwards,Category.assoc] using
        congrArg (fun e => e ≫ U.f i) (first_inverse U V idx D i j)
    _ = (D.overlap i j).inv ≫
        (pullback.snd (U.f i) (U.f j) ≫ U.f j) := by rw [pullback.condition]
    _ = _ := by
      simpa only [backwards,Category.assoc] using
        congrArg (fun e => e ≫ U.f j) (second_inverse U V idx D i j).symm

def forward : X ⟶ Y :=
  U.glueMorphisms (forwards U V idx D) (forwards_agree U V idx D)

def backward : Y ⟶ X :=
  (indexed U V idx).glueMorphisms (backwards U V idx D) (backwards_agree U V idx D)

theorem forward_chart (i : U.I₀) :
    U.f i ≫ forward U V idx D = (D.chart i).hom ≫ (indexed U V idx).f i :=
  U.ι_glueMorphisms _ _ i

theorem backward_chart (i : U.I₀) :
    (indexed U V idx).f i ≫ backward U V idx D = (D.chart i).inv ≫ U.f i :=
  (indexed U V idx).ι_glueMorphisms _ _ i

/-- The actual global isomorphism on the original deformed scheme
and its undeformed product, not an equality tested only at points. -/
def correctedIso : X ≅ Y where
  hom := forward U V idx D
  inv := backward U V idx D
  hom_inv_id := by
    apply U.hom_ext
    intro i
    rw [← Category.assoc,forward_chart,Category.assoc,backward_chart,← Category.assoc,
      Iso.hom_inv_id,Category.id_comp,Category.comp_id]
  inv_hom_id := by
    apply (indexed U V idx).hom_ext
    intro i
    rw [← Category.assoc,backward_chart,Category.assoc,forward_chart,← Category.assoc,
      Iso.inv_hom_id,Category.id_comp,Category.comp_id]

/-- The actual dual-base arrow is preserved globally when its literal
chart maps are preserved. The R106 correction fixes ε, not merely its
specialization to zero. -/
theorem global_base_read {S : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S)
    (local_reads : ∀ i : U.I₀,
      (D.chart i).hom ≫ (indexed U V idx).f i ≫ y = U.f i ≫ x) :
    (correctedIso U V idx D).hom ≫ y = x := by
  apply U.hom_ext
  intro i
  change U.f i ≫ forward U V idx D ≫ y = U.f i ≫ x
  rw [← Category.assoc,forward_chart,Category.assoc]
  exact local_reads i

section CorrectedAffineLegs
open OriginalActualKSCotangentOverlap318 OriginalActualKSCoboundary318
  OriginalActualKSEtaleRestriction318 TrivSqZeroExt

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

def specArrow (h : Sq A →ₐ[R] Sq B) :
    Spec (.of (Sq B)) ⟶ Spec (.of (Sq A)) :=
  Spec.map (CommRingCat.ofHom h.toRingHom)

theorem specArrow_comp (f : Sq A →ₐ[R] Sq B) (g : Sq B →ₐ[R] Sq C) :
    specArrow (g.comp f) = specArrow g ≫ specArrow f :=
  Spec.map_comp (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)

theorem specArrow_id : specArrow (AlgHom.id R (Sq A)) = 𝟙 (Spec (.of (Sq A))) :=
  Spec.map_id _

def affineGauge (d : Derivation R A A) : Spec (.of (Sq A)) ≅ Spec (.of (Sq A)) where
  hom := specArrow (shear d)
  inv := specArrow (shear (-d))
  hom_inv_id := by rw [←specArrow_comp,shear_add,neg_add_cancel,shear_zero,specArrow_id]
  inv_hom_id := by rw [←specArrow_comp,shear_add,add_neg_cancel,shear_zero,specArrow_id]

variable [Algebra A B] [IsScalarTower R A B] [Algebra.FormallyEtale A B]
  [Algebra C B] [IsScalarTower R C B] [Algebra.FormallyEtale C B]

/-- Specialize both original ring-read identities to the actual Spec
arrows needed to instantiate the two chart conditions in Corrected. -/
theorem spec_corrected_overlap_legs (F : Sq B →ₐ[R] Sq B)
    (red : ∀ x : Sq B, (F x).fst=x.fst) (base : F (epsilon B)=epsilon B)
    (di : Derivation R A A) (dj : Derivation R C C)
    (boundary : difference (constantLift R B) (backLift F red) =
      extend (B:=B) dj-extend (B:=B) di) :
    specArrow (sqRestriction R A B) ≫ (affineGauge (-di)).hom =
      (affineGauge (-(extend (B:=B) di))).hom ≫ specArrow (sqRestriction R A B) ∧
    specArrow F ≫ specArrow (sqRestriction R C B) ≫ (affineGauge (-dj)).hom =
      (affineGauge (-(extend (B:=B) di))).hom ≫ specArrow (sqRestriction R C B) := by
  obtain ⟨h₁,h₂⟩ := corrected_overlap_legs F red base di dj boundary
  constructor
  · simpa only [affineGauge,specArrow_comp] using
      congrArg (fun h : Sq A →ₐ[R] Sq B => specArrow h) h₁
  · simpa only [affineGauge,specArrow_comp] using
      congrArg (fun h : Sq C →ₐ[R] Sq B => specArrow h) h₂

end CorrectedAffineLegs

end OriginalActualKSSchemeGlue318

#print axioms OriginalActualKSSchemeGlue318.forward_chart
#print axioms OriginalActualKSSchemeGlue318.backward_chart
#print axioms OriginalActualKSSchemeGlue318.correctedIso
#print axioms OriginalActualKSSchemeGlue318.global_base_read
#print axioms OriginalActualKSSchemeGlue318.spec_corrected_overlap_legs
