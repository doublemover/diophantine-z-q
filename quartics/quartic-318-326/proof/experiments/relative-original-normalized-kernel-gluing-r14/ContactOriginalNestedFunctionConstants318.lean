module
public import ContactOriginalUniversalFunctionConstants318
public section
noncomputable section
namespace ContactOriginalNestedFunctionConstants318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "q" => ContactCanonicalCoefficientFrame318.projection R c
variable {T : Scheme.{0}} (b : T ⟶ Spec R)
/-- Constants on the EXACT nested family consumed by the fixed-pair
full-Isom classifier. No flatness of b is asserted or required. -/
lemma appTop_isIso : IsIso (pullback.snd q b).appTop := by
  let e := RelativeAmbientReassociation318.comparison p (baseMap R) b
  letI : IsIso (pullback.snd p (b ≫ baseMap R)).appTop :=
    ContactOriginalUniversalFunctionConstants318.app_isIso c (b ≫ baseMap R) ⊤
  have h : e.hom ≫ pullback.snd p (b ≫ baseMap R)=pullback.snd q b :=
    RelativeAmbientReassociation318.second p (baseMap R) b
  rw [←h,Scheme.Hom.comp_appTop]
  infer_instance
@[expose] def constants : Γ(T,⊤) ≃+* Γ(pullback q b,⊤) :=
  RingEquiv.ofBijective (pullback.snd q b).appTop.hom (by
    letI := appTop_isIso R c b
    exact ConcreteCategory.bijective_of_isIso _)
lemma constants_apply (a : Γ(T,⊤)) : constants R c b a=(pullback.snd q b).appTop a := rfl
/-- Both directions are canonical structural maps/inverses on the SAME
rings. In particular, full family units really are base units here. -/
@[expose] def units : Γ(T,⊤)ˣ ≃* Γ(pullback q b,⊤)ˣ where
  toFun := Units.map (constants R c b).toMonoidHom
  invFun := Units.map (constants R c b).symm.toMonoidHom
  left_inv a := by apply Units.ext; exact (constants R c b).symm_apply_apply a.val
  right_inv a := by apply Units.ext; exact (constants R c b).apply_symm_apply a.val
  map_mul' a d := (Units.map (constants R c b).toMonoidHom).map_mul a d
lemma units_value (a : Γ(T,⊤)ˣ) :
    (units R c b a).val=(pullback.snd q b).appTop a.val := rfl
variable {T' : Scheme.{0}} (b' : T' ⟶ Spec R) (h : T' ⟶ T) (hh : h ≫ b=b')
lemma units_natural (a : Γ(T,⊤)ˣ) :
    Units.map (RelativeSchemeCoefficient318.map q b b' h hh).appTop.hom.toMonoidHom
      (units R c b a)=units R c b' (Units.map h.appTop.hom.toMonoidHom a) := by
  apply Units.ext
  change (RelativeSchemeCoefficient318.map q b b' h hh).appTop
    ((pullback.snd q b).appTop a.val)=(pullback.snd q b').appTop (h.appTop a.val)
  have he := congrArg (fun k => k.appTop) (RelativeSchemeCoefficient318.map_snd q b b' h hh)
  simp only [Scheme.Hom.comp_appTop] at he
  exact ConcreteCategory.congr_hom he a.val
end ContactOriginalNestedFunctionConstants318
