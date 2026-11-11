module
public import PELOriginalFiniteTorsionKernel318
public section
noncomputable section
namespace PELOriginalKernelRelationMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalSchemePointGroup318 PELOriginalIntegerMultiplication318
open PELOriginalTorsionKernelScheme318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ)
abbrev Product := pullback (structureMap τ hτ n) (π τ hτ)
abbrev Relation := pullback (multiplication τ hτ n) (multiplication τ hτ n)
abbrev productBase : Product τ hτ n ⟶ Spec (CommRingCat.of ℂ) := pullback.snd _ _≫π τ hτ
abbrev relationBase : Relation τ hτ n ⟶ Spec (CommRingCat.of ℂ) := pullback.snd _ _≫π τ hτ
lemma relation_first_over : pullback.fst (multiplication τ hτ n) (multiplication τ hτ n)≫π τ hτ=
    relationBase τ hτ n := by
  have h := congrArg (fun f => f≫π τ hτ) (pullback.condition (multiplication τ hτ n) (multiplication τ hτ n))
  simpa only [Category.assoc,over_complex] using h
@[expose] def kernelPoint : KernelPoints τ hτ n (Product τ hτ n) (productBase τ hτ n) :=
  ⟨pullback.fst _ _,pullback.condition _ _⟩
@[expose] def firstPoint : Points τ hτ (Product τ hτ n) (productBase τ hτ n) :=
  (pointsEquiv τ hτ n _ (kernelPoint τ hτ n)).val
@[expose] def secondPoint : Points τ hτ (Product τ hτ n) (productBase τ hτ n) :=
  ⟨pullback.snd _ _,rfl⟩
lemma first_torsion : n • firstPoint τ hτ n=0 :=
  (pointsEquiv τ hτ n _ (kernelPoint τ hτ n)).property

/-- The genuine relation map (k,x) ↦ (k+x,x), on the FULL kernel
product scheme, retaining nilpotent and infinitesimal tests. -/
@[expose] def forward : Product τ hτ n ⟶ Relation τ hτ n :=
  pullback.lift (firstPoint τ hτ n+secondPoint τ hτ n).val (secondPoint τ hτ n).val (by
    rw [test_action τ hτ n _ (firstPoint τ hτ n+secondPoint τ hτ n).property,
      test_action τ hτ n _ (secondPoint τ hτ n).property,zsmul_add,first_torsion,zero_add])
@[reassoc] lemma forward_second : forward τ hτ n≫pullback.snd _ _=pullback.snd _ _ :=
  pullback.lift_snd _ _ _
@[reassoc] lemma forward_first : forward τ hτ n≫pullback.fst _ _=
    (firstPoint τ hτ n+secondPoint τ hτ n).val := pullback.lift_fst _ _ _

@[expose] def pair {T : Scheme} {ρ : T ⟶ Spec (CommRingCat.of ℂ)}
    (k : KernelPoints τ hτ n T ρ) (x : Points τ hτ T ρ) : T ⟶ Product τ hτ n :=
  pullback.lift k.val x.val (k.property.trans x.property.symm)
lemma pair_over {T : Scheme} {ρ : T ⟶ Spec (CommRingCat.of ℂ)}
    (k : KernelPoints τ hτ n T ρ) (x : Points τ hτ T ρ) :
    pair τ hτ n k x≫productBase τ hτ n=ρ := by
  rw [productBase,←Category.assoc,pair,pullback.lift_snd]
  exact x.property
lemma pair_first_action {T : Scheme} {ρ : T ⟶ Spec (CommRingCat.of ℂ)}
    (k : KernelPoints τ hτ n T ρ) (x : Points τ hτ T ρ) :
    pair τ hτ n k x≫forward τ hτ n≫pullback.fst _ _=
      ((pointsEquiv τ hτ n ρ k).val+x).val := by
  rw [forward_first]
  let F := pull τ hτ (productBase τ hτ n) (pair τ hτ n k x) (pair_over τ hτ n k x)
  have hk : F (firstPoint τ hτ n)=(pointsEquiv τ hτ n ρ k).val := by
    apply Subtype.ext
    change pair τ hτ n k x≫(pullback.fst _ _≫inclusion τ hτ n)=k.val≫inclusion τ hτ n
    rw [←Category.assoc,pair,pullback.lift_fst]
  have hx : F (secondPoint τ hτ n)=x := by
    apply Subtype.ext
    exact pullback.lift_snd _ _ _
  change (F (firstPoint τ hτ n+secondPoint τ hτ n)).val=_
  rw [map_add,hk,hx]
lemma pair_second_action {T : Scheme} {ρ : T ⟶ Spec (CommRingCat.of ℂ)}
    (k : KernelPoints τ hτ n T ρ) (x : Points τ hτ T ρ) :
    pair τ hτ n k x≫forward τ hτ n≫pullback.snd _ _=x.val := by
  rw [forward_second,pair,pullback.lift_snd]

/-- EVERY over-C scheme point of the self-relation lifts to the actual
kernel product. This uses the represented group on that SAME test scheme,
not merely complex points or a reduced-point equality principle. -/
lemma lift_point {T : Scheme} {ρ : T ⟶ Spec (CommRingCat.of ℂ)}
    (p : T ⟶ Relation τ hτ n) (hp : p≫relationBase τ hτ n=ρ) :
    ∃ q : T ⟶ Product τ hτ n,q≫forward τ hτ n=p := by
  let x : Points τ hτ T ρ := ⟨p≫pullback.fst _ _,by
    rw [Category.assoc,relation_first_over]; exact hp⟩
  let y : Points τ hτ T ρ := ⟨p≫pullback.snd _ _,by
    rw [Category.assoc]; exact hp⟩
  have hxy : n • x=n • y := by
    apply Subtype.ext
    rw [←test_action τ hτ n x.val x.property,←test_action τ hτ n y.val y.property]
    change (p≫pullback.fst _ _)≫multiplication τ hτ n=(p≫pullback.snd _ _)≫multiplication τ hτ n
    rw [Category.assoc,pullback.condition,←Category.assoc]
  let k : torsion τ hτ n ρ := ⟨x-y,by
    change n • (x-y)=0
    rw [zsmul_sub,hxy,sub_self]⟩
  let k' := (pointsEquiv τ hτ n ρ).symm k
  refine ⟨pair τ hτ n k' y,?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc,pair_first_action]
    change (((pointsEquiv τ hτ n ρ) ((pointsEquiv τ hτ n ρ).symm k)).val+y).val=x.val
    rw [Equiv.apply_symm_apply]
    change (x-y+y).val=x.val
    rw [sub_add_cancel]
  · rw [Category.assoc,pair_second_action]
/-- The preceding ALL-test lift applied to the relation's identity
makes the actual relation map split-surjective on all scheme points. -/
lemma surjective : Function.Surjective (forward τ hτ n) := by
  obtain ⟨q,hq⟩ := lift_point τ hτ n (𝟙 (Relation τ hτ n)) (Category.id_comp _)
  intro x
  refine ⟨q x,?_⟩
  rw [←Scheme.Hom.comp_apply,hq]
  rfl
end PELOriginalKernelRelationMap318
