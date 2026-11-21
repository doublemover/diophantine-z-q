module
public import SelectedOriginalCompactClassicalDifferentials318
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial KaehlerDifferential
open SelectedRationalRootCompactInstall318 SelectedOriginalRationalOrdinaryRoot318
open SelectedOriginalRationalOrdinaryGeometry318 SelectedOriginalCompactClassicalDifferentials318
open SelectedIntrinsicBaseLinear318 SelectedIntrinsicGlobalToAffine318

namespace SelectedRationalCompactIntrinsicCoefficient318

variable (M : ℕ) [NeZero M] (p : (OpenJModel318.Base M)[X])
local notation "QS" => ordinaryRoot M p

variable (hp : p.Monic) (hu : IsUnit (AdjoinRoot.mk p p.derivative))
variable (hf : IsField (genericRoot M p))

abbrev compactStructure := compactJ M p hf ≫ ProjectiveJLine318.structureMap ℚ
abbrev RationalSections := Sections (compactStructure M p hf)

private theorem restrict_constant {X : Scheme}
    (i : Spec (CommRingCat.of QS)⟶X) [IsOpenImmersion i]
    (f : X⟶Spec (CommRingCat.of ℚ))
    (hi : i≫f=Spec.map (CommRingCat.ofHom (algebraMap ℚ QS))) (r : ℚ) :
    restrictRegular i (constants f r)=algebraMap ℚ QS r := by
  have h :
      ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ f.appTop) ≫ i.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of QS)).hom =
      CommRingCat.ofHom (algebraMap ℚ QS) := by
    rw [Category.assoc,←Category.assoc f.appTop,←Scheme.Hom.comp_appTop,hi,
      Scheme.ΓSpecIso_naturality,←Category.assoc,Iso.inv_hom_id,Category.id_comp]
  exact congrArg (fun k => k r) h

private def affineCoefficient {S : Type} [CommRing S] [Algebra ℚ S] {Y : Scheme}
    (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (f : Y ⟶ Spec (CommRingCat.of ℚ))
    (hq : j ≫ f = Spec.algebraMap ℚ S)
    (F : KaehlerDifferential ℚ S ≃ₗ[S] S)
    (hconst : ∀ r : ℚ, restrictRegular j (constants f r) = algebraMap ℚ S r) :
    Sections f →ₗ[ℚ] S where
  toFun w := F (restrict j f hq w)
  map_add' x y := by
    let x' : Γ(FamilyIntrinsicDifferentials318.omega f,⊤) := x
    let y' : Γ(FamilyIntrinsicDifferentials318.omega f,⊤) := y
    change F (restrict j f hq (x'+y')) = F (restrict j f hq x') + F (restrict j f hq y')
    exact (congrArg (fun w : KaehlerDifferential ℚ S => F w)
      ((restrict j f hq).map_add x' y')).trans (F.map_add _ _)
  map_smul' r w := by
    let w' : Γ(FamilyIntrinsicDifferentials318.omega f,⊤) := w
    let ξ : KaehlerDifferential ℚ S := restrict j f hq w'
    change F (restrict j f hq (constants f r • w')) = r • F ξ
    have ha : F (restrict j f hq (constants f r • w')) =
        F (restrictRegular j (constants f r) • ξ) :=
      congrArg (fun v : KaehlerDifferential ℚ S => F v) (restrict_smul j f hq (constants f r) w')
    have hb : F (restrictRegular j (constants f r) • ξ) =
        restrictRegular j (constants f r) • F ξ := F.map_smul _ _
    have hc : restrictRegular j (constants f r) • F ξ = r • F ξ := by
      rw [smul_eq_mul, hconst, Algebra.smul_def]
    exact ha.trans (hb.trans hc)

include hp hu in
private theorem ordinary_compact_scalar :
    ordinaryEmbedding M p hf hp hu ≫ compactStructure M p hf = Spec.algebraMap ℚ QS := by
  letI : Fact p.Monic := ⟨hp⟩
  exact actual_ordinary_Q M p hu hf

include hp hu in
/-- The true rational compact differential restricted to the actual
ordinary open and expressed in that open's normalized dJ. -/
def rationalCoefficient : RationalSections M p hf→ₗ[ℚ]QS :=
  affineCoefficient (ordinaryEmbedding M p hf hp hu) (compactStructure M p hf)
    (ordinary_compact_scalar M p hp hu hf) (ordinaryFrame M p hp hu)
    (restrict_constant M p (ordinaryEmbedding M p hf hp hu) (compactStructure M p hf)
      (ordinary_compact_scalar M p hp hu hf))

theorem rationalCoefficient_apply
    (hq : ordinaryEmbedding M p hf hp hu ≫ compactStructure M p hf =
      Spec.algebraMap ℚ (ordinaryRoot M p))
    (w : RationalSections M p hf) :
    rationalCoefficient M p hp hu hf w =
      ordinaryFrame M p hp hu
        (restrict (ordinaryEmbedding M p hf hp hu) (compactStructure M p hf) hq w) := rfl

end SelectedRationalCompactIntrinsicCoefficient318

#print axioms SelectedRationalCompactIntrinsicCoefficient318.rationalCoefficient
