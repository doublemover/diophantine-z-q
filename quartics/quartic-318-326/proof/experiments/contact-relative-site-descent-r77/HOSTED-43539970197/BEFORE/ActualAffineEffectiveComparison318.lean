module
public import ActualCanonicalOverlap318
public section
noncomputable section
namespace ActualAffineEffectiveComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ActualAffineDoubleNerve318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
/-- Cancel a displayed conjugation before specializing the category to the
actual nerve, so hidden limit-carrier projections are not simp patterns. -/
private lemma conjugation_commutes {C D : Type*} [Category C] [Category D]
    (P Q : C ⥤ D) {M N : C} (e : M ≅ N)
    (a : P.obj M ⟶ Q.obj M) (b : P.obj N ⟶ Q.obj N)
    (h : P.map e.inv ≫ a ≫ Q.map e.hom = b) :
    a ≫ Q.map e.hom = P.map e.hom ≫ b := by
  have hc : P.map e.hom ≫ P.map e.inv = 𝟙 _ := by
    calc
      _ = P.map (e.hom ≫ e.inv) := (P.map_comp _ _).symm
      _ = P.map (𝟙 _) := congrArg (fun k => P.map k) e.hom_inv_id
      _ = 𝟙 _ := P.map_id _
  calc
    a ≫ Q.map e.hom = (P.map e.hom ≫ P.map e.inv) ≫ a ≫ Q.map e.hom := by
      rw [hc, Category.id_comp]
    _ = P.map e.hom ≫ b := by
      rw [Category.assoc, h]

/-- Reflect conjugation on abstract scheme carriers before substituting the
actual categorical double. Both normalized endpoint paths are retained. -/
private lemma reflect_conjugation {U X Y : Scheme.{u}} {M N : U.Modules}
    (d : Y ≅ X) (e : M ≅ N) (p₀ p₁ : X ⟶ U) (v₀ v₁ : Y ⟶ U)
    (h₀ : d.hom ≫ p₀ = v₀) (h₁ : d.hom ≫ p₁ = v₁)
    (a : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M)
    (a' : (Scheme.Modules.pullback v₀).obj M ⟶ (Scheme.Modules.pullback v₁).obj M)
    (b : (Scheme.Modules.pullback p₀).obj N ⟶ (Scheme.Modules.pullback p₁).obj N)
    (ha : SheafPathTransport318.transport M d.hom p₀ p₁ v₀ v₁ h₀ h₁ a = a')
    (h : (Scheme.Modules.pullback v₀).map e.inv ≫ a' ≫
      (Scheme.Modules.pullback v₁).map e.hom =
        SheafPathTransport318.transport N d.hom p₀ p₁ v₀ v₁ h₀ h₁ b) :
    (Scheme.Modules.pullback p₀).map e.inv ≫ a ≫
      (Scheme.Modules.pullback p₁).map e.hom = b := by
  apply SheafIsoTransport318.transport_injective N d p₀ p₁ v₀ v₁ h₀ h₁
  exact (SheafIsoTransport318.conjugation e d.hom p₀ p₁ v₀ v₁ h₀ h₁ a).trans
    ((congrArg (fun k => (Scheme.Modules.pullback v₀).map e.inv ≫ k ≫
      (Scheme.Modules.pullback v₁).map e.hom) ha).trans h)

/-- Check the genuine affine-nerve specialization while its base module and
cover comparison remain abstract, before substituting the reconstructed coalgebra. -/
private lemma affine_original_overlap (R S : CommRingCat.{u}) [Algebra R S]
    (M : ModuleCat R) (L : Line (Spec S))
    (e : (Scheme.Modules.pullback (baseMap R S)).obj (tilde M) ≅ L.object)
    (τ : ActualAffineSheafData318.firstObject R S L ⟶ ActualAffineSheafData318.secondObject R S L)
    (h : (Scheme.Modules.pullback (Spec.map (AffineModuleBaseChange318.leftMap R S S))).map e.inv ≫
      CanonicalTildeOverlap318.sheafOverlap R S M ≫
      (Scheme.Modules.pullback (Spec.map (AffineModuleBaseChange318.rightMap R S S))).map e.hom =
        ActualAffineTensorTransport318.overlap R S L τ) :
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map e.inv ≫
      CanonicalSheafOverlap318.actual (tilde M) (baseMap R S) ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map e.hom = τ := by
  exact reflect_conjugation (doubleIso R S).symm e
    (ActualOverlapDiagram318.first (baseMap R S)) (ActualOverlapDiagram318.second (baseMap R S))
    (Spec.map (AffineModuleBaseChange318.leftMap R S S))
    (Spec.map (AffineModuleBaseChange318.rightMap R S S))
    (inverse_first R S) (inverse_second R S) _ _ τ
    (ActualCanonicalOverlap318.transport R S M) h

variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]
  (L : Line (Spec S))
  (τ : ActualAffineSheafData318.firstObject R S L ⟶ ActualAffineSheafData318.secondObject R S L)
  (hdiag : ActualAffineSheafData318.Diagonal R S L τ)
  (htriple : ActualAffineSheafData318.Cocycle R S L τ)
abbrev line := ActualAffineLineReconstruction318.line R S L τ hdiag htriple
abbrev comparison :
    (Scheme.Modules.pullback (baseMap R S)).obj (line R S L τ hdiag htriple).object ≅ L.object :=
  ActualAffineLineReconstruction318.pullbackIso R S L τ hdiag htriple

/-- The exact reconstruction comparison carries the canonical overlap on
the genuine categorical double to the unchanged original input overlap.
The original scheme isomorphism reflects the tensor-spectrum calculation. -/
lemma original_overlap :
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map
        (comparison R S L τ hdiag htriple).inv ≫
      CanonicalSheafOverlap318.actual (line R S L τ hdiag htriple).object (baseMap R S) ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map
        (comparison R S L τ hdiag htriple).hom = τ := by
  let M : ModuleCat R := ReconstructedOverlapCompatibility318.descendedModule R S L
    (ActualAffineTensorTransport318.overlap R S L τ)
    (ActualAffineTensorLaws318.diagonal R S L τ hdiag)
    (ActualAffineTensorLaws318.triple R S L τ htriple)
  let e : (Scheme.Modules.pullback (baseMap R S)).obj (tilde M) ≅ L.object :=
    comparison R S L τ hdiag htriple
  change (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map e.inv ≫
    CanonicalSheafOverlap318.actual (tilde M) (baseMap R S) ≫
    (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map e.hom = τ
  exact affine_original_overlap R S M L e τ
    (ReconstructedOverlapCompatibility318.original_overlap R S L
      (ActualAffineTensorTransport318.overlap R S L τ)
      (ActualAffineTensorLaws318.diagonal R S L τ hdiag)
      (ActualAffineTensorLaws318.triple R S L τ htriple))


/-- The actual displayed isomorphism is compatible with the original
geometric descent datum on the actual categorical fiber product. -/
lemma comparison_commutes :
    CanonicalSheafOverlap318.actual (line R S L τ hdiag htriple).object (baseMap R S) ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map
        (comparison R S L τ hdiag htriple).hom =
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map
      (comparison R S L τ hdiag htriple).hom ≫ τ := by
  exact conjugation_commutes
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S)))
    (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S)))
    (comparison R S L τ hdiag htriple) _ τ
    (original_overlap R S L τ hdiag htriple)

/-- Effective descent with its exact original geometric compatibility
square, for a faithfully flat morphism of affine schemes. The diagonal
and triple laws are the original categorical-scheme laws; no module or
scalar-extension coalgebra law is an input. -/
theorem effective (hdiag : ActualAffineSheafData318.Diagonal R S L τ)
    (htriple : ActualAffineSheafData318.Cocycle R S L τ) : ∃ (K : Line (Spec R))
    (e : (Scheme.Modules.pullback (baseMap R S)).obj K.object ≅ L.object),
    CanonicalSheafOverlap318.actual K.object (baseMap R S) ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map e.hom =
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map e.hom ≫ τ :=
  ⟨line R S L τ hdiag htriple, comparison R S L τ hdiag htriple,
    comparison_commutes R S L τ hdiag htriple⟩
end ActualAffineEffectiveComparison318
