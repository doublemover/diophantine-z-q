module
public import IntrinsicTensorGenerator318
public section
noncomputable section
namespace IntrinsicTensorFrameValue318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (h : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (e : KaehlerDifferential R S ≃ₗ[S] S)

/-- Evaluate the original weighted tensor section in the actual intrinsic
coordinate-derivative frame, before making any choice of field-valued point. -/
theorem weightedSquare_frame (s a : S) (hs : e (KaehlerDifferential.D R S s) = 1) :
    (IntrinsicTensorGenerator318.frame j p h e).hom.app ⊤
      (IntrinsicTensorChartSections318.weightedSquare j p h a (KaehlerDifferential.D R S s)) =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv a := by
  let b := (Scheme.ΓSpecIso (CommRingCat.of S)).inv a
  have hl := (IntrinsicTensorGenerator318.frame j p h e).hom.app_smul b
    (IntrinsicTensorGenerator318.basis j p h s)
  change (IntrinsicTensorGenerator318.frame j p h e).hom.app ⊤
    ((j.appIso ⊤).inv b • IntrinsicTensorGenerator318.basis j p h s) =
      b * (show Γ(Spec (CommRingCat.of S), ⊤) from
        (IntrinsicTensorGenerator318.frame j p h e).hom.app ⊤
          (IntrinsicTensorGenerator318.basis j p h s)) at hl
  rw [IntrinsicTensorGenerator318.basis_normalized j p h e s hs, mul_one] at hl
  exact hl

variable {K : Type u} [CommRing K] (r : S →+* K)

/-- The actual chart-frame coefficient evaluated by a specified ring point. -/
@[expose] def sectionValue (q : Γ(IntrinsicTensorSheaf318.tensor
    (FamilyIntrinsicDifferentials318.omega p) (FamilyIntrinsicDifferentials318.omega p), j ''ᵁ ⊤)) : K :=
  r ((Scheme.ΓSpecIso (CommRingCat.of S)).hom
    ((IntrinsicTensorGenerator318.frame j p h e).hom.app ⊤ q))

theorem sectionValue_weighted (s a : S) (hs : e (KaehlerDifferential.D R S s) = 1) :
    sectionValue j p h e r
      (IntrinsicTensorChartSections318.weightedSquare j p h a (KaehlerDifferential.D R S s)) =
      r a := by
  have hframe := weightedSquare_frame j p h e s a hs
  exact (congrArg (fun b : Γ(Spec (CommRingCat.of S), ⊤) =>
    r ((Scheme.ΓSpecIso (CommRingCat.of S)).hom b)) hframe).trans
    (congrArg r (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of S)) a))

theorem sectionValue_nsmul (n : ℕ) (q : Γ(IntrinsicTensorSheaf318.tensor
    (FamilyIntrinsicDifferentials318.omega p) (FamilyIntrinsicDifferentials318.omega p), j ''ᵁ ⊤)) :
    sectionValue j p h e r (n • q) = n • sectionValue j p h e r q := by
  unfold sectionValue
  simp only [map_nsmul]

end IntrinsicTensorFrameValue318
