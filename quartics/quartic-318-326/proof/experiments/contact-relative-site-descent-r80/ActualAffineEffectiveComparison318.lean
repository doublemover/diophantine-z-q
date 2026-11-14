module
public import ActualCanonicalOverlap318
public section
set_option stderrAsMessages false
noncomputable section
namespace ActualAffineEffectiveComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ActualAffineDoubleNerve318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "PICARD_SITE_FRONTIER_00_POSITIVE_CONTROL_BEFORE_HELPERS"
  out.flush

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

run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "PICARD_SITE_FRONTIER_01_AFTER_conjugation_commutes"
  out.flush

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

run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "PICARD_SITE_FRONTIER_02_AFTER_reflect_conjugation"
  out.flush

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

run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "PICARD_SITE_FRONTIER_03_AFTER_affine_original_overlap"
  out.flush

/-- Transfer canonical compatibility across an explicit base-sheaf equality.
All dependent comparison transport is checked on abstract sheaf carriers. -/
private lemma original_overlap_of_object_eq {B U : Scheme.{u}} (f : U ⟶ B)
    (V W : B.Modules) (h : V = W) (N : U.Modules)
    (e : (Scheme.Modules.pullback f).obj V ≅ N)
    (d : (Scheme.Modules.pullback f).obj W ≅ N)
    (he : (Scheme.Modules.pullback f).mapIso (eqToIso h) ≪≫ d = e)
    (τ : (Scheme.Modules.pullback (ActualOverlapDiagram318.first f)).obj N ⟶
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second f)).obj N)
    (hd : (Scheme.Modules.pullback (ActualOverlapDiagram318.first f)).map d.inv ≫
      CanonicalSheafOverlap318.actual W f ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second f)).map d.hom = τ) :
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first f)).map e.inv ≫
      CanonicalSheafOverlap318.actual V f ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second f)).map e.hom = τ := by
  cases h
  have hde : d = e := by
    apply Iso.ext
    have hh := congrArg (fun i => i.hom) he
    simpa only [Iso.trans_hom, Functor.mapIso_hom, eqToIso_refl, Iso.refl_hom,
      CategoryTheory.Functor.map_id, Category.id_comp] using hh
  simpa only [← hde] using hd

run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "PICARD_SITE_FRONTIER_04_AFTER_original_overlap_of_object_eq"
  out.flush

/-- Check the exact reconstructed line and its original comparison while the
input tensor overlap and both tensor laws are still independent parameters.
The actual-nerve transport is connected by the displayed equality, not by
substituting its derived diagonal and triple proof terms into this proof. -/
private lemma reconstructed_actual_overlap (R S : CommRingCat.{u}) [Algebra R S]
    [Module.FaithfullyFlat R S] (L : Line (Spec S))
    (σ : OriginalLineOverlapCoaction318.first R S L ⟶ OriginalLineOverlapCoaction318.second R S L)
    (hd : OriginalGeometricDiagonal318.Diagonal R S L σ)
    (ht : OriginalGeometricTriple318.Cocycle R S L σ)
    (τ : ActualAffineSheafData318.firstObject R S L ⟶ ActualAffineSheafData318.secondObject R S L)
    (hσ : σ = ActualAffineTensorTransport318.overlap R S L τ) :
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map
        (ReconstructedOverlapCompatibility318.comparison R S L σ hd ht).inv ≫
      CanonicalSheafOverlap318.actual
        (OriginalGeometricAffineLine318.line R S L σ hd ht).object (baseMap R S) ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map
        (ReconstructedOverlapCompatibility318.comparison R S L σ hd ht).hom = τ := by
  exact original_overlap_of_object_eq (baseMap R S)
    (OriginalGeometricAffineLine318.line R S L σ hd ht).object
    (tilde (ReconstructedOverlapCompatibility318.descendedModule R S L σ hd ht))
    (ReconstructedOverlapCompatibility318.line_object R S L σ hd ht) L.object
    (ReconstructedOverlapCompatibility318.comparison R S L σ hd ht)
    (ReconstructedOverlapCompatibility318.namedComparison R S L σ hd ht)
    (ReconstructedOverlapCompatibility318.comparison_transport R S L σ hd ht) τ
    (affine_original_overlap R S
      (ReconstructedOverlapCompatibility318.descendedModule R S L σ hd ht) L
      (ReconstructedOverlapCompatibility318.namedComparison R S L σ hd ht) τ
      ((ReconstructedOverlapCompatibility318.named_original_overlap R S L σ hd ht).trans hσ))

run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "PICARD_SITE_FRONTIER_05_AFTER_reconstructed_actual_overlap"
  out.flush

variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]
  (L : Line (Spec S))
  (τ : ActualAffineSheafData318.firstObject R S L ⟶ ActualAffineSheafData318.secondObject R S L)
  (hdiag : ActualAffineSheafData318.Diagonal R S L τ)
  (htriple : ActualAffineSheafData318.Cocycle R S L τ)
abbrev line := ActualAffineLineReconstruction318.line R S L τ hdiag htriple
abbrev comparison :
    (Scheme.Modules.pullback (baseMap R S)).obj (line R S L τ hdiag htriple).object ≅ L.object :=
  ActualAffineLineReconstruction318.pullbackIso R S L τ hdiag htriple

run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "PICARD_SITE_FRONTIER_06_AFTER_line_comparison_abbreviations"
  out.flush

/-- The exact reconstruction comparison carries the canonical overlap on
the genuine categorical double to the unchanged original input overlap.
The original scheme isomorphism reflects the tensor-spectrum calculation. -/
lemma original_overlap :
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map
        (comparison R S L τ hdiag htriple).inv ≫
      CanonicalSheafOverlap318.actual (line R S L τ hdiag htriple).object (baseMap R S) ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map
        (comparison R S L τ hdiag htriple).hom = τ := by
  exact reconstructed_actual_overlap R S L (ActualAffineTensorTransport318.overlap R S L τ)
    (ActualAffineTensorLaws318.diagonal R S L τ hdiag)
    (ActualAffineTensorLaws318.triple R S L τ htriple) τ rfl

run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "PICARD_SITE_FRONTIER_07_AFTER_original_overlap"
  out.flush

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

run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "PICARD_SITE_FRONTIER_08_AFTER_comparison_commutes"
  out.flush

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
run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "PICARD_SITE_FRONTIER_09_AFTER_effective"
  out.flush

end ActualAffineEffectiveComparison318
