module
public import PELOriginalOrderDivisionTorsorMap318
public import PELOriginalOrderIsogenyDegree318
public section
noncomputable section
namespace PELOriginalOrderDivisionTorsorIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalSchemePointGroup318 PELOriginalOrderKernelScheme318
open PELOriginalOrderSchemeMorphism318
open PELOriginalOrderLocalDivision318 PELOriginalOrderDivisionRootPoints318
open PELOriginalOrderDivisionTorsorMap318
variable (τ : ℂ) (hτ : 0<τ.im) (a : PELPrincipalOrderCoordinates318.order)
variable {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ)) (p : Points τ hτ T ρ)

/-- Every pair of roots over the SAME test map differs by one genuine
whole-kernel point. This constructs a lift on arbitrary scheme tests. -/
lemma lift_point {U : Scheme} (m : U⟶Relation τ hτ a ρ p) :
    ∃ q : U⟶Product τ hτ a ρ p,q≫forward τ hτ a ρ p=m := by
  let k := m≫pullback.snd _ _≫projection τ hτ a ρ p
  let l₂ : FiberPoints τ hτ a ρ p k := ⟨m≫pullback.snd _ _,Category.assoc _ _ _⟩
  let l₁ : FiberPoints τ hτ a ρ p k := ⟨m≫pullback.fst _ _,by
    rw [Category.assoc,pullback.condition];rfl⟩
  let x := toRoot τ hτ a ρ p k l₁
  let y := toRoot τ hτ a ρ p k l₂
  let t := (kernelPointsEquiv τ hτ a (k≫ρ)).symm (difference τ hτ a ρ p k x y)
  refine ⟨pair τ hτ a ρ p k t l₂,?_⟩
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc,Category.assoc,pair_first_root]
      change (((kernelPointsEquiv τ hτ a (k≫ρ))
        ((kernelPointsEquiv τ hτ a (k≫ρ)).symm (difference τ hτ a ρ p k x y))).val+y.val).val=x.val.val
      rw [Equiv.apply_symm_apply]
      change (x.val-y.val+y.val).val=x.val.val
      rw [sub_add_cancel]
    · rw [Category.assoc,Category.assoc,pullback.condition]
      rw [←Category.assoc,pair_second]
      exact l₂.property.trans l₁.property.symm
  · rw [Category.assoc,pair_second]

/-- Whole-scheme freeness, proved on arbitrary test maps by original
point-group cancellation and both projections of the actual kernel pullback. -/
lemma hom_injective {U : Scheme} (q r : U⟶Product τ hτ a ρ p)
    (hqr : q≫forward τ hτ a ρ p=r≫forward τ hτ a ρ p) : q=r := by
  have hl : q≫pullback.snd _ _=r≫pullback.snd _ _ := by
    have h := congrArg (fun f => f≫pullback.snd _ _) hqr
    simpa only [Category.assoc,forward_second] using h
  let σ := q≫productBase τ hτ a ρ p
  have hr : r≫productBase τ hτ a ρ p=σ := by
    change r≫((pullback.snd _ _≫projection τ hτ a ρ p)≫ρ)=
      q≫((pullback.snd _ _≫projection τ hτ a ρ p)≫ρ)
    simpa only [Category.assoc] using
      congrArg (fun f => f≫projection τ hτ a ρ p≫ρ) hl.symm
  let Fq := pull τ hτ (productBase τ hτ a ρ p) q (rfl : q≫productBase τ hτ a ρ p=σ)
  let Fr := pull τ hτ (productBase τ hτ a ρ p) r hr
  have hs : Fq (secondRoot τ hτ a ρ p).val=Fr (secondRoot τ hτ a ρ p).val := by
    apply Subtype.ext
    change q≫(pullback.snd _ _≫(root τ hτ a ρ p).val)=
      r≫(pullback.snd _ _≫(root τ hτ a ρ p).val)
    rw [←Category.assoc,←Category.assoc,hl]
  have ha : Fq (kernelPointsEquiv τ hτ a _ (kernelPoint τ hτ a ρ p)).val+
      Fq (secondRoot τ hτ a ρ p).val=
      Fr (kernelPointsEquiv τ hτ a _ (kernelPoint τ hτ a ρ p)).val+
      Fr (secondRoot τ hτ a ρ p).val := by
    rw [←map_add,←map_add]
    apply Subtype.ext
    have h := congrArg (fun f => f≫pullback.fst _ _≫(root τ hτ a ρ p).val) hqr
    simpa only [Category.assoc,forward_first_root] using h
  rw [hs] at ha
  have ht := add_right_cancel ha
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · have h := congrArg Subtype.val ht
      change q≫(pullback.fst _ _≫inclusion τ hτ a)=r≫(pullback.fst _ _≫inclusion τ hτ a) at h
      simpa only [Category.assoc] using h
    · have hq : (q≫pullback.fst _ _)≫structureMap τ hτ a=
          (q≫pullback.snd _ _)≫coverBase τ hτ a ρ p := by
        simp only [Category.assoc,pullback.condition]
      have hr' : (r≫pullback.fst _ _)≫structureMap τ hτ a=
          (r≫pullback.snd _ _)≫coverBase τ hτ a ρ p := by
        simp only [Category.assoc,pullback.condition]
      exact hq.trans ((congrArg (fun f => f≫coverBase τ hτ a ρ p) hl).trans hr'.symm)
  · exact hl

/-- Genuine full scheme torsor relation for the literal division cover,
K_a ×_C D ≅ D ×_T D, with (k,r) ↦ (k+r,r). -/
@[expose] def iso : Product τ hτ a ρ p ≅ Relation τ hτ a ρ p := by
  let q := (lift_point τ hτ a ρ p (𝟙 _)).choose
  have hq := (lift_point τ hτ a ρ p (𝟙 _)).choose_spec
  refine ⟨forward τ hτ a ρ p,q,?_,?_⟩
  · apply hom_injective τ hτ a ρ p
    rw [Category.assoc,hq,Category.comp_id,Category.id_comp]
  · exact hq
@[reassoc] lemma iso_second : (iso τ hτ a ρ p).hom≫pullback.snd _ _=pullback.snd _ _ :=
  forward_second τ hτ a ρ p

/-- The original division map is a genuine finite étale surjective
cover equipped with the preceding whole-scheme kernel relation iso. -/
lemma finite_etale_cover (ha : PELOriginalOrderIntegralNorm318.norm a≠0) :
    IsFinite (projection τ hτ a ρ p) ∧ Etale (projection τ hτ a ρ p) ∧
    Function.Surjective (projection τ hτ a ρ p) := by
  letI := PELOriginalOrderLocalDivision318.finite_projection τ hτ a ρ p ha
  letI := PELOriginalEtaleOrderIsogeny318.etale τ hτ a ha
  letI := PELOriginalOrderLocalDivision318.surjective_projection τ hτ a ρ p ha
  refine ⟨inferInstance,?_,?_⟩
  · exact inferInstanceAs (Etale (pullback.snd (morphism τ hτ a) p.val))
  · exact (projection τ hτ a ρ p).surjective

/-- Native rank of the SAME whole order division torsor at every prime
of its arbitrary test base, retaining the literal reduced-norm premise. -/
lemma degree (ha : PELOriginalOrderIntegralNorm318.norm a≠0) (t : T) :
    (projection τ hτ a ρ p).finrank t=(PELOriginalOrderIntegralNorm318.norm a).natAbs^2 :=
  PELOriginalOrderIsogenyDegree318.baseChange_degree τ hτ a ha p.val t
end PELOriginalOrderDivisionTorsorIso318
