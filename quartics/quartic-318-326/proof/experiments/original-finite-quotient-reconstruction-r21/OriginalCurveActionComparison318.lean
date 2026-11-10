module
public import OriginalCandidateCurveIso318
public import SourceSignFieldComparison318
public import SchematicEqualityExtension318
public section
noncomputable section
namespace OriginalCurveActionComparison318
open AlgebraicGeometry CategoryTheory ContactKummerOrder318

local instance actualField (c : Fin 4 → ℚˣ) : Field (ContactFieldNormalization318.Field c) :=
  (KummerTensorField318.source_raw_field c).toField

private lemma extend_square {A B C : Scheme} (g : A ⟶ B) (i : B ⟶ C)
    (a : A ⟶ A) (b : B ⟶ B) (c : C ⟶ C)
    (hi : i ≫ c = b ≫ i) (hg : g ≫ b = a ≫ g) :
    (g ≫ i) ≫ c = a ≫ (g ≫ i) := by
  rw [Category.assoc,hi,←Category.assoc,hg,Category.assoc]

/-- Exact generic restriction of the EXISTING whole Contact sign map. -/
@[reassoc] theorem contact_generic_sign (c : Fin 4 → ℚˣ) (b : Fin 4 → Bool) :
    ContactFieldNormalization318.genericSource c ≫ ContactGlobalSigns318.map c b =
      Spec.map (CommRingCat.ofHom
        (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b).toRingHom) ≫
          ContactFieldNormalization318.genericSource c := by
  let U : Scheme := Spec (CommRingCat.of (OpenOrder c))
  let into : U ⟶ ContactProjectiveModel318.model c := ContactProjectiveModel318.sourceOpen c
  let f : U ⟶ U := ContactGlobalSigns318.openMap c b
  let g : Spec (CommRingCat.of (ContactFieldNormalization318.Field c)) ⟶ U :=
    AffineFractionGeneric318.map (OpenOrder c) (ContactFieldNormalization318.Field c)
  let a := Spec.map (CommRingCat.ofHom
    (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b).toRingHom)
  have hi : into ≫ ContactGlobalSigns318.map c b = f ≫ into :=
    ContactGlobalSigns318.on_open c b
  have hg : g ≫ f = a ≫ g := by
    dsimp [g,f,a]
    unfold AffineFractionGeneric318.map ContactGlobalSigns318.openMap
    rw [←Spec.map_comp,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact SourceSignFieldComparison318.open_embedding c b x
  change (g ≫ into) ≫ ContactGlobalSigns318.map c b = a ≫ (g ≫ into)
  exact extend_square g into a f (ContactGlobalSigns318.map c b) hi hg

variable {L : Type} [Field L] [Algebra (RatFunc ℚ) L] (c : Fin 4 → ℚˣ)
variable (e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L)

@[reassoc] theorem field_spec_square (σ : L ≃ₐ[RatFunc ℚ] L) (b : Fin 4 → Bool)
    (he : ∀ z, σ (e z) = e (FourRootAutomorphisms318.signEquiv
      (SourceKummerField318.parameter c) b z)) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ReconstructedFieldNormalization318.specIso L c e).hom =
      (ReconstructedFieldNormalization318.specIso L c e).hom ≫
        Spec.map (CommRingCat.ofHom
          (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b).toRingHom) := by
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) =
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact he

variable {Y : Scheme} [IsIntegral Y]
  (g : Spec (CommRingCat.of L) ⟶ Y) (p : Y ⟶ ProjectiveJLine318.scheme ℚ)
  [IsDominant g] [IsIntegralHom p] [IsIso (DominantFunctionField318.map g)]
  (hbase : g ≫ p = ReconstructedFieldNormalization318.base L)
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

/-- The SAME reconstructed curve isomorphism intertwines the actual supplied
candidate action and the EXISTING whole Contact sign action. Equality is
extended from the original generic morphism by schematic density, not asserted
from dimensions, group cardinalities or an abstract choice of isomorphism. -/
theorem original_action (σ : L ≃ₐ[RatFunc ℚ] L) (b : Fin 4 → Bool)
    (he : ∀ z, σ (e z) = e (FourRootAutomorphisms318.signEquiv
      (SourceKummerField318.parameter c) b z))
    (a : Y ⟶ Y) (ha : a ≫ p = p)
    (hg : g ≫ a = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ g) :
    a ≫ (OriginalCandidateCurveIso318.iso g p hbase V hcover hnormal c e).hom =
      (OriginalCandidateCurveIso318.iso g p hbase V hcover hnormal c e).hom ≫
        ContactGlobalSigns318.map c b := by
  let E := OriginalCandidateCurveIso318.iso g p hbase V hcover hnormal c e
  letI : IsIntegralHom (ContactProjectiveModel318.modelMap c) :=
    ContactProjectiveModel318.modelMap_integral c
  letI : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isDominant g
  have hE : E.hom ≫ ContactProjectiveModel318.modelMap c = p :=
    OriginalCandidateCurveIso318.iso_base g p hbase V hcover hnormal c e
  have hG : g ≫ E.hom = (ReconstructedFieldNormalization318.specIso L c e).hom ≫
      ContactFieldNormalization318.genericSource c :=
    OriginalCandidateCurveIso318.iso_source g p hbase V hcover hnormal c e
  apply SchematicEqualityExtension318.ext (ContactProjectiveModel318.modelMap c) (i := g)
  · change (a ≫ E.hom) ≫ _ = (E.hom ≫ ContactGlobalSigns318.map c b) ≫ _
    simp only [Category.assoc, hE, ha, ContactGlobalSigns318.over_line]
  · change g ≫ (a ≫ E.hom) = g ≫ (E.hom ≫ ContactGlobalSigns318.map c b)
    rw [← Category.assoc, hg, Category.assoc, hG, ← Category.assoc,
      field_spec_square c e σ b he, Category.assoc, ← contact_generic_sign,
      ← Category.assoc, ← hG, Category.assoc]
end OriginalCurveActionComparison318
