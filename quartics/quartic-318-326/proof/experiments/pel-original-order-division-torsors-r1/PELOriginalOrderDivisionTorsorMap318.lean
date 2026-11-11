module
public import PELOriginalOrderDivisionRootPoints318
public section
noncomputable section
namespace PELOriginalOrderDivisionTorsorMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalSchemePointGroup318 PELOriginalOrderKernelScheme318
open PELOriginalOrderSchemeMorphism318
open PELOriginalOrderLocalDivision318 PELOriginalOrderDivisionRootPoints318
variable (τ : ℂ) (hτ : 0<τ.im) (a : PELPrincipalOrderCoordinates318.order)
variable {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ)) (p : Points τ hτ T ρ)
abbrev Product := pullback (structureMap τ hτ a) (coverBase τ hτ a ρ p)
abbrev Relation := pullback (projection τ hτ a ρ p) (projection τ hτ a ρ p)
abbrev toBase : Product τ hτ a ρ p⟶T := pullback.snd _ _≫projection τ hτ a ρ p
abbrev productBase : Product τ hτ a ρ p⟶Spec (CommRingCat.of ℂ) := toBase τ hτ a ρ p≫ρ
@[expose] def kernelPoint : KernelPoint τ hτ a (productBase τ hτ a ρ p) :=
  ⟨pullback.fst _ _,by
    change pullback.fst _ _≫structureMap τ hτ a=(pullback.snd _ _≫projection τ hτ a ρ p)≫ρ
    rw [Category.assoc]
    exact pullback.condition _ _⟩
@[expose] def secondRoot : Roots τ hτ a ρ p (toBase τ hτ a ρ p) :=
  toRoot τ hτ a ρ p _ ⟨pullback.snd _ _,rfl⟩
@[expose] def firstRoot : Roots τ hτ a ρ p (toBase τ hτ a ρ p) :=
  translate τ hτ a ρ p _
    (kernelPointsEquiv τ hτ a _ (kernelPoint τ hτ a ρ p)) (secondRoot τ hτ a ρ p)

/-- The actual whole scheme relation map (k,r) maps to (k+r,r) on
this specific division cover, over the original arbitrary test scheme. -/
@[expose] def forward : Product τ hτ a ρ p⟶Relation τ hτ a ρ p :=
  pullback.lift (fromRoot τ hτ a ρ p _ (firstRoot τ hτ a ρ p)).val
    (pullback.snd _ _) (fromRoot τ hτ a ρ p _ (firstRoot τ hτ a ρ p)).property
@[reassoc] lemma forward_second : forward τ hτ a ρ p≫pullback.snd _ _=pullback.snd _ _ :=
  pullback.lift_snd _ _ _
@[reassoc] lemma forward_first_root : forward τ hτ a ρ p≫pullback.fst _ _≫
    (root τ hτ a ρ p).val=(firstRoot τ hτ a ρ p).val.val := by
  rw [←Category.assoc]
  change (pullback.lift _ _ _≫pullback.fst _ _)≫(root τ hτ a ρ p).val=_
  rw [pullback.lift_fst]
  exact pullback.lift_fst _ _ _

variable {U : Scheme} (k : U⟶T)
@[expose] def pair (t : KernelPoint τ hτ a (k≫ρ))
    (l : FiberPoints τ hτ a ρ p k) : U⟶Product τ hτ a ρ p :=
  pullback.lift t.val l.val (by
    rw [t.property]
    change k≫ρ=l.val≫(projection τ hτ a ρ p≫ρ)
    rw [←Category.assoc,l.property])
lemma pair_over (t : KernelPoint τ hτ a (k≫ρ)) (l : FiberPoints τ hτ a ρ p k) :
    pair τ hτ a ρ p k t l≫productBase τ hτ a ρ p=k≫ρ := by
  change pair τ hτ a ρ p k t l≫((pullback.snd _ _≫projection τ hτ a ρ p)≫ρ)=_
  rw [←Category.assoc,←Category.assoc,pair,pullback.lift_snd,l.property]
lemma pair_second (t : KernelPoint τ hτ a (k≫ρ)) (l : FiberPoints τ hτ a ρ p k) :
    pair τ hτ a ρ p k t l≫forward τ hτ a ρ p≫pullback.snd _ _=l.val := by
  rw [forward_second,pair,pullback.lift_snd]
lemma pair_first_root (t : KernelPoint τ hτ a (k≫ρ)) (l : FiberPoints τ hτ a ρ p k) :
    pair τ hτ a ρ p k t l≫forward τ hτ a ρ p≫pullback.fst _ _≫(root τ hτ a ρ p).val=
      ((kernelPointsEquiv τ hτ a (k≫ρ) t).val+(toRoot τ hτ a ρ p k l).val).val := by
  rw [forward_first_root]
  let F := pull τ hτ (productBase τ hτ a ρ p) (pair τ hτ a ρ p k t l)
    (pair_over τ hτ a ρ p k t l)
  have ht : F (kernelPointsEquiv τ hτ a _ (kernelPoint τ hτ a ρ p)).val=
      (kernelPointsEquiv τ hτ a (k≫ρ) t).val := by
    apply Subtype.ext
    change pair τ hτ a ρ p k t l≫(pullback.fst _ _≫inclusion τ hτ a)=t.val≫inclusion τ hτ a
    rw [←Category.assoc,pair,pullback.lift_fst]
  have hl : F (secondRoot τ hτ a ρ p).val=(toRoot τ hτ a ρ p k l).val := by
    apply Subtype.ext
    change pair τ hτ a ρ p k t l≫(pullback.snd _ _≫(root τ hτ a ρ p).val)=
      l.val≫(root τ hτ a ρ p).val
    rw [←Category.assoc,pair,pullback.lift_snd]
  change (F ((kernelPointsEquiv τ hτ a _ (kernelPoint τ hτ a ρ p)).val+
    (secondRoot τ hτ a ρ p).val)).val=_
  rw [map_add,ht,hl]
end PELOriginalOrderDivisionTorsorMap318
