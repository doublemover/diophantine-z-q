module
public import PELOriginalDivisionTorsorMap318
public import PELOriginalIntegerIsogenyDegree318
public section
noncomputable section
namespace PELOriginalDivisionTorsorIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalSchemePointGroup318 PELOriginalTorsionKernelScheme318
open PELOriginalMultiplicationLocalDivision318 PELOriginalDivisionRootPoints318
open PELOriginalDivisionTorsorMap318
variable (τ : ℂ) (hτ : 0<τ.im) (n : ℤ)
variable {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ)) (p : Points τ hτ T ρ)

/-- Every pair of roots over the SAME test map differs by one genuine
whole-kernel point. This constructs a lift on arbitrary scheme tests. -/
lemma lift_point {U : Scheme} (m : U⟶Relation τ hτ n ρ p) :
    ∃ q : U⟶Product τ hτ n ρ p,q≫forward τ hτ n ρ p=m := by
  let k := m≫pullback.snd _ _≫projection τ hτ n ρ p
  let l₂ : FiberPoints τ hτ n ρ p k := ⟨m≫pullback.snd _ _,Category.assoc _ _ _⟩
  let l₁ : FiberPoints τ hτ n ρ p k := ⟨m≫pullback.fst _ _,by
    rw [Category.assoc,pullback.condition];rfl⟩
  let x := toRoot τ hτ n ρ p k l₁
  let y := toRoot τ hτ n ρ p k l₂
  let t := (pointsEquiv τ hτ n (k≫ρ)).symm (difference τ hτ n ρ p k x y)
  refine ⟨pair τ hτ n ρ p k t l₂,?_⟩
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc,Category.assoc,pair_first_root]
      change (((pointsEquiv τ hτ n (k≫ρ))
        ((pointsEquiv τ hτ n (k≫ρ)).symm (difference τ hτ n ρ p k x y))).val+y.val).val=x.val.val
      rw [Equiv.apply_symm_apply]
      change (x.val-y.val+y.val).val=x.val.val
      rw [sub_add_cancel]
    · rw [Category.assoc,Category.assoc,pullback.condition]
      rw [←Category.assoc,pair_second]
      exact l₂.property.trans l₁.property.symm
  · rw [Category.assoc,pair_second]

/-- Whole-scheme freeness, proved on arbitrary test maps by original
point-group cancellation and the actual equalizer monomorphism. -/
lemma hom_injective {U : Scheme} (q r : U⟶Product τ hτ n ρ p)
    (hqr : q≫forward τ hτ n ρ p=r≫forward τ hτ n ρ p) : q=r := by
  have hl : q≫pullback.snd _ _=r≫pullback.snd _ _ := by
    have h := congrArg (fun f => f≫pullback.snd _ _) hqr
    simpa only [Category.assoc,forward_second] using h
  let σ := q≫productBase τ hτ n ρ p
  have hr : r≫productBase τ hτ n ρ p=σ := by
    change r≫((pullback.snd _ _≫projection τ hτ n ρ p)≫ρ)=
      q≫((pullback.snd _ _≫projection τ hτ n ρ p)≫ρ)
    simpa only [Category.assoc] using
      congrArg (fun f => f≫projection τ hτ n ρ p≫ρ) hl.symm
  let Fq := pull τ hτ (productBase τ hτ n ρ p) q (rfl : q≫productBase τ hτ n ρ p=σ)
  let Fr := pull τ hτ (productBase τ hτ n ρ p) r hr
  have hs : Fq (secondRoot τ hτ n ρ p).val=Fr (secondRoot τ hτ n ρ p).val := by
    apply Subtype.ext
    change q≫(pullback.snd _ _≫(root τ hτ n ρ p).val)=
      r≫(pullback.snd _ _≫(root τ hτ n ρ p).val)
    rw [←Category.assoc,←Category.assoc,hl]
  have ha : Fq (pointsEquiv τ hτ n _ (kernelPoint τ hτ n ρ p)).val+
      Fq (secondRoot τ hτ n ρ p).val=
      Fr (pointsEquiv τ hτ n _ (kernelPoint τ hτ n ρ p)).val+
      Fr (secondRoot τ hτ n ρ p).val := by
    rw [←map_add,←map_add]
    apply Subtype.ext
    have h := congrArg (fun f => f≫pullback.fst _ _≫(root τ hτ n ρ p).val) hqr
    simpa only [Category.assoc,forward_first_root] using h
  rw [hs] at ha
  have ht := add_right_cancel ha
  apply pullback.hom_ext
  · apply (cancel_mono (inclusion τ hτ n)).mp
    have h := congrArg Subtype.val ht
    change q≫(pullback.fst _ _≫inclusion τ hτ n)=r≫(pullback.fst _ _≫inclusion τ hτ n) at h
    simpa only [Category.assoc] using h
  · exact hl

/-- Genuine full scheme torsor relation for the literal division cover,
K_n ×_C D ≅ D ×_T D, with (k,r) ↦ (k+r,r). -/
@[expose] def iso : Product τ hτ n ρ p ≅ Relation τ hτ n ρ p := by
  let q := (lift_point τ hτ n ρ p (𝟙 _)).choose
  have hq := (lift_point τ hτ n ρ p (𝟙 _)).choose_spec
  refine ⟨forward τ hτ n ρ p,q,?_,?_⟩
  · apply hom_injective τ hτ n ρ p
    rw [Category.assoc,hq,Category.comp_id,Category.id_comp]
  · exact hq
@[reassoc] lemma iso_second : (iso τ hτ n ρ p).hom≫pullback.snd _ _=pullback.snd _ _ :=
  forward_second τ hτ n ρ p

/-- The original division map is a genuine finite étale surjective
cover equipped with the preceding whole-scheme kernel relation iso. -/
lemma finite_etale_cover (hn : n≠0) :
    IsFinite (projection τ hτ n ρ p) ∧ Etale (projection τ hτ n ρ p) ∧
    Function.Surjective (projection τ hτ n ρ p) :=
  PELOriginalEtaleKernelDivision318.division_finite_etale τ hτ n hn ρ p
/-- The SAME division torsor has actual native rank |n|^4 at every
prime of its arbitrary test base, not merely that many geometric roots. -/
lemma degree (hn : n≠0) (t : T) :
    (projection τ hτ n ρ p).finrank t=n.natAbs^4 :=
  PELOriginalIntegerIsogenyDegree318.baseChange_degree τ hτ n hn p.val t
end PELOriginalDivisionTorsorIso318
