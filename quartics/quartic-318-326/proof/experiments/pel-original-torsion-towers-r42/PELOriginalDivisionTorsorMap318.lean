module
public import PELOriginalDivisionRootPoints318
public section
noncomputable section
namespace PELOriginalDivisionTorsorMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalSchemePointGroup318 PELOriginalTorsionKernelScheme318
open PELOriginalMultiplicationLocalDivision318 PELOriginalDivisionRootPoints318
variable (τ : ℂ) (hτ : 0<τ.im) (n : ℤ)
variable {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ)) (p : Points τ hτ T ρ)
abbrev Product := pullback (structureMap τ hτ n) (coverBase τ hτ n ρ p)
abbrev Relation := pullback (projection τ hτ n ρ p) (projection τ hτ n ρ p)
abbrev toBase : Product τ hτ n ρ p⟶T := pullback.snd _ _≫projection τ hτ n ρ p
abbrev productBase : Product τ hτ n ρ p⟶Spec (CommRingCat.of ℂ) := toBase τ hτ n ρ p≫ρ
@[expose] def kernelPoint : KernelPoints τ hτ n (Product τ hτ n ρ p) (productBase τ hτ n ρ p) :=
  ⟨pullback.fst _ _,by
    change pullback.fst _ _≫structureMap τ hτ n=(pullback.snd _ _≫projection τ hτ n ρ p)≫ρ
    rw [Category.assoc]
    exact pullback.condition _ _⟩
@[expose] def secondRoot : Roots τ hτ n ρ p (toBase τ hτ n ρ p) :=
  toRoot τ hτ n ρ p _ ⟨pullback.snd _ _,rfl⟩
@[expose] def firstRoot : Roots τ hτ n ρ p (toBase τ hτ n ρ p) :=
  translate τ hτ n ρ p _
    (pointsEquiv τ hτ n _ (kernelPoint τ hτ n ρ p)) (secondRoot τ hτ n ρ p)

/-- The actual whole scheme relation map (k,r) maps to (k+r,r) on
this specific division cover, over the original arbitrary test scheme. -/
@[expose] def forward : Product τ hτ n ρ p⟶Relation τ hτ n ρ p :=
  pullback.lift (fromRoot τ hτ n ρ p _ (firstRoot τ hτ n ρ p)).val
    (pullback.snd _ _) (fromRoot τ hτ n ρ p _ (firstRoot τ hτ n ρ p)).property
@[reassoc] lemma forward_second : forward τ hτ n ρ p≫pullback.snd _ _=pullback.snd _ _ :=
  pullback.lift_snd _ _ _
@[reassoc] lemma forward_first_root : forward τ hτ n ρ p≫pullback.fst _ _≫
    (root τ hτ n ρ p).val=(firstRoot τ hτ n ρ p).val.val := by
  rw [←Category.assoc]
  change (pullback.lift _ _ _≫pullback.fst _ _)≫(root τ hτ n ρ p).val=_
  rw [pullback.lift_fst]
  exact pullback.lift_fst _ _ _

variable {U : Scheme} (k : U⟶T)
@[expose] def pair (t : KernelPoints τ hτ n U (k≫ρ))
    (l : FiberPoints τ hτ n ρ p k) : U⟶Product τ hτ n ρ p :=
  pullback.lift t.val l.val (by
    rw [t.property]
    change k≫ρ=l.val≫(projection τ hτ n ρ p≫ρ)
    rw [←Category.assoc,l.property])
lemma pair_over (t : KernelPoints τ hτ n U (k≫ρ)) (l : FiberPoints τ hτ n ρ p k) :
    pair τ hτ n ρ p k t l≫productBase τ hτ n ρ p=k≫ρ := by
  change pair τ hτ n ρ p k t l≫((pullback.snd _ _≫projection τ hτ n ρ p)≫ρ)=_
  rw [←Category.assoc,←Category.assoc,pair,pullback.lift_snd,l.property]
lemma pair_second (t : KernelPoints τ hτ n U (k≫ρ)) (l : FiberPoints τ hτ n ρ p k) :
    pair τ hτ n ρ p k t l≫forward τ hτ n ρ p≫pullback.snd _ _=l.val := by
  rw [forward_second,pair,pullback.lift_snd]
lemma pair_first_root (t : KernelPoints τ hτ n U (k≫ρ)) (l : FiberPoints τ hτ n ρ p k) :
    pair τ hτ n ρ p k t l≫forward τ hτ n ρ p≫pullback.fst _ _≫(root τ hτ n ρ p).val=
      ((pointsEquiv τ hτ n (k≫ρ) t).val+(toRoot τ hτ n ρ p k l).val).val := by
  rw [forward_first_root]
  let F := pull τ hτ (productBase τ hτ n ρ p) (pair τ hτ n ρ p k t l)
    (pair_over τ hτ n ρ p k t l)
  have ht : F (pointsEquiv τ hτ n _ (kernelPoint τ hτ n ρ p)).val=
      (pointsEquiv τ hτ n (k≫ρ) t).val := by
    apply Subtype.ext
    change pair τ hτ n ρ p k t l≫(pullback.fst _ _≫inclusion τ hτ n)=t.val≫inclusion τ hτ n
    rw [←Category.assoc,pair,pullback.lift_fst]
  have hl : F (secondRoot τ hτ n ρ p).val=(toRoot τ hτ n ρ p k l).val := by
    apply Subtype.ext
    change pair τ hτ n ρ p k t l≫(pullback.snd _ _≫(root τ hτ n ρ p).val)=
      l.val≫(root τ hτ n ρ p).val
    rw [←Category.assoc,pair,pullback.lift_snd]
  change (F ((pointsEquiv τ hτ n _ (kernelPoint τ hτ n ρ p)).val+
    (secondRoot τ hτ n ρ p).val)).val=_
  rw [map_add,ht,hl]
end PELOriginalDivisionTorsorMap318
