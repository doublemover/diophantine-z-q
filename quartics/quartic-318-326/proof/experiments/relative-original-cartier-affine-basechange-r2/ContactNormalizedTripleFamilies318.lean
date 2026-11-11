module
public import ContactNormalizedPointZeroFamily318
public section
noncomputable section
namespace ContactNormalizedTripleFamilies318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ProjectiveParameterSliceTriplePoints318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "P" => Γ(L.object,⊤)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
variable {i j k : Fin F.size}

/-- Pullback of the original normalized zero CHART FAMILY to the full
coefficient test. Unlike a fiberwise point set, it retains its whole
scheme structure and original projection. -/
abbrev family (a : Point R P S i j k) : Scheme :=
  pullback (ContactNormalizedChartZeroFamily318.projection R c L hz i)
    (ContactNormalizedPointZeroFamily318.testMap R c L hz S f i a.point a.first_eq)
@[expose] def comparison (a : Point R P S i j k) :
    ContactNormalizedZeroTriple318.zero R c L hz S f a ≅ family R c L hz S f a :=
  ContactNormalizedPointZeroFamily318.iso R c L hz S f i a.point a.first_eq
@[expose] def embedding (a : Point R P S i j k) : family R c L hz S f a ⟶ curve S c :=
  (comparison R c L hz S f a).inv ≫ ContactNormalizedZeroTriple318.into R c L hz S f a
instance embedding_mono (a : Point R P S i j k) : Mono (embedding R c L hz S f a) := by
  unfold embedding
  infer_instance

/-- Transport the actual unit-normalization isomorphism to the original
chart-family pullbacks, not to separately chosen zero models. -/
@[expose] def rotation (a : Point R P S i j k) :
    family R c L hz S f (rotate R P S i j k a) ≅ family R c L hz S f a :=
  (comparison R c L hz S f (rotate R P S i j k a)).symm ≪≫
    ContactNormalizedZeroTriple318.rotation R c L hz S f a ≪≫ comparison R c L hz S f a
@[reassoc] lemma rotation_embedding (a : Point R P S i j k) :
    (rotation R c L hz S f a).hom ≫ embedding R c L hz S f a=
      embedding R c L hz S f (rotate R P S i j k a) := by
  simp only [rotation,embedding,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    Iso.hom_inv_id_assoc,ContactNormalizedZeroTriple318.rotation_into]
private lemma equality_embedding {a b : Point R P S i j k} (h : a=b) :
    eqToHom (congrArg (family R c L hz S f) h) ≫ embedding R c L hz S f b=
      embedding R c L hz S f a := by
  subst b
  simp only [eqToHom_refl,Category.id_comp]

/-- Full cyclic coherence for the ACTUAL pulled-back finite-flat chart
families on any affine triple test. Monicity is inherited from the same
original closed zero immersion, so every comparison choice is eliminated. -/
lemma cycle (a : Point R P S i j k) :
    (rotation R c L hz S f (rotate R P S j k i (rotate R P S i j k a))).hom ≫
      (rotation R c L hz S f (rotate R P S i j k a)).hom ≫
      (rotation R c L hz S f a).hom=
    eqToHom (congrArg (family R c L hz S f) (rotate_three R P S i j k a)) := by
  apply (cancel_mono (embedding R c L hz S f a)).1
  rw [Category.assoc,Category.assoc,rotation_embedding,rotation_embedding,
    rotation_embedding,equality_embedding]
end ContactNormalizedTripleFamilies318
