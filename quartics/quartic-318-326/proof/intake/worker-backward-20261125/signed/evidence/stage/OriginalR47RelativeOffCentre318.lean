module
public import OriginalR47RelativeNodeDatum318
public import OriginalR47GlobalCentreRees318
public section
noncomputable section

namespace OriginalR47RelativeOffCentre318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalR47TraitRoundKernel318
open OriginalR47RelativeNodeDatum318
open OriginalR47IsolatedCentreCover318
open OriginalR47GlobalCentreRees318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime]
variable {X U : Scheme} (s : X ⟶ base (R:=R)) (k : U ⟶ X)

/-- Apply the already checked localization-of-the-original-round
comparison to the actual old open. This never asks that Spec Rₚ→Spec R
have finite type. -/
@[expose] def localizeMap : restricted p (k ≫ s) ⟶ restricted p s :=
  (restrictedRoundIso p s k).inv ≫ a p s k

theorem localizeMap_open [IsOpenImmersion k] : IsOpenImmersion (localizeMap p s k) := by
  let : IsOpenImmersion (a p s k) := MorphismProperty.pullback_snd k (forgetMap p s)
    (inferInstance : IsOpenImmersion k)
  unfold localizeMap
  infer_instance

@[reassoc]
theorem localizeMap_old :
    localizeMap p s k ≫ forgetMap p s = forgetMap p (k ≫ s) ≫ k := by
  rw [localizeMap,Category.assoc,← (pullback_round p s k).w,
    ← restrictedRoundIso_old_assoc, Iso.inv_hom_id_assoc]

@[reassoc]
theorem localizeMap_trait :
    localizeMap p s k ≫ toTrait p s = toTrait p (k ≫ s) := by
  rw [localizeMap,Category.assoc,← restrictedRoundIso_trait, Iso.inv_hom_id_assoc]

@[expose] def localizeMapOver (f : U ⟶ base (R:=R)) (h : k ≫ s = f) :
    restricted p f ⟶ restricted p s :=
  eqToHom (congrArg (restricted p) h.symm) ≫ localizeMap p s k

theorem localizeMapOver_open (f : U ⟶ base (R:=R)) (h : k ≫ s = f)
    [IsOpenImmersion k] :
    IsOpenImmersion (localizeMapOver p s k f h) := by
  subst f
  change IsOpenImmersion (𝟙 _ ≫ localizeMap p s k)
  rw [Category.id_comp]
  exact localizeMap_open p s k

@[reassoc] theorem localizeMapOver_old (f : U ⟶ base (R:=R)) (h : k ≫ s = f) :
    localizeMapOver p s k f h ≫ forgetMap p s = forgetMap p f ≫ k := by
  subst f
  simpa only [localizeMapOver,eqToHom_refl,Category.id_comp] using localizeMap_old p s k

@[reassoc] theorem localizeMapOver_trait (f : U ⟶ base (R:=R)) (h : k ≫ s = f) :
    localizeMapOver p s k f h ≫ toTrait p s = toTrait p f := by
  subst f
  simpa only [localizeMapOver,eqToHom_refl,Category.id_comp] using localizeMap_trait p s k

variable (Z : Set X) (hZ : Z.Finite) (hC : ∀ x ∈ Z, IsClosed ({x} : Set X))
variable (pick : ∀ z : Z, Centre Z z)
local notation "U₀" => off Z hZ hC
local notation "Y" => source Z hZ hC pick
local notation "r" => proj Z hZ hC pick

/-- The actual old line/axis witness transports on the unchanged open
of the genuine global Rees round. Its same closed trait is p; the
point on the literal comparison chart is not changed. -/
theorem terminal_off (y : Y) (hy : r y ∉ Z)
    (xₚ : restricted p s) (hxₚ : forgetMap p s xₚ = r y)
    (oldTerminal : TerminalAt (toTrait p s) xₚ) :
    ∃ yₚ : restricted p (r ≫ s), forgetMap p (r ≫ s) yₚ = y ∧
      TerminalAt (toTrait p (r ≫ s)) yₚ := by
  let U := U₀.toScheme
  let d := U₀.ι
  obtain ⟨k,H⟩ := unchanged Z hZ hC pick
  let : IsOpenImmersion k := MorphismProperty.of_isPullback
    (P:=@IsOpenImmersion) H (inferInstance : IsOpenImmersion d)
  let u : U := ⟨r y,hy⟩
  have huk : k u = y := by
    obtain ⟨w,hw,hw'⟩ := Scheme.exists_preimage_of_isPullback H y u
      (show r y = d u by rfl)
    change w = u at hw'
    exact hw' ▸ hw
  let f := d ≫ s
  let c := toTrait p s xₚ
  have hc : f u = brace p c := by
    have eq := congrArg (fun j : restricted p s ⟶ base (R:=R) => j xₚ)
      (pullback.condition (f:=s) (g:=brace p))
    simpa only [Scheme.Hom.comp_apply,hxₚ] using eq
  obtain ⟨uₚ,hu₁,hu₂⟩ :=
    Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback f (brace p)) u c hc
  have hk : k ≫ (r ≫ s) = f := by
    have eq : k ≫ r = d := by simpa only [Category.id_comp] using H.w
    rw [←Category.assoc,eq]
  let j₁ := localizeMap p s d
  let j₂ := localizeMapOver p (r ≫ s) k f hk
  let : IsOpenImmersion j₁ := localizeMap_open p s d
  let : IsOpenImmersion j₂ := localizeMapOver_open p (r ≫ s) k f hk
  have h₁ : j₁ uₚ = xₚ := by
    let : IsPreimmersion (forgetMap p s) := forgetMap_preimmersion p s
    apply (forgetMap p s).isEmbedding.injective
    have eq := congrArg (fun g : restricted p f ⟶ X => g uₚ) (localizeMap_old p s d)
    simpa only [j₁,Scheme.Hom.comp_apply,hu₁,hxₚ] using eq
  have h₂ : forgetMap p (r ≫ s) (j₂ uₚ) = y := by
    have eq := congrArg (fun g : restricted p f ⟶ Y => g uₚ)
      (localizeMapOver_old p (r ≫ s) k f hk)
    simpa only [j₂,Scheme.Hom.comp_apply,hu₁,huk] using eq
  have hT := terminal_pull_open oldTerminal j₁ uₚ h₁
  have HT : TerminalAt (toTrait p f) uₚ := localizeMap_trait p s d ▸ hT
  exact ⟨j₂ uₚ,h₂,terminal_push_open HT j₂ (localizeMapOver_trait p (r ≫ s) k f hk)⟩

end OriginalR47RelativeOffCentre318

#print axioms OriginalR47RelativeOffCentre318.localizeMapOver_old
#print axioms OriginalR47RelativeOffCentre318.terminal_off
