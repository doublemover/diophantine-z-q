module
public import PELOriginalEtaleKernelDivision318
public section
noncomputable section
namespace PELOriginalDivisionRootPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalSchemePointGroup318 PELOriginalIntegerMultiplication318
open PELOriginalMultiplicationLocalDivision318 PELOriginalTorsionKernelScheme318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ)
variable {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ)) (p : Points τ hτ T ρ)
variable {U : Scheme} (k : U⟶T)
/-- ALL original n-roots over the specified arbitrary test map. -/
abbrev Roots := {x : Points τ hτ U (k≫ρ) // n • x=pull τ hτ ρ k rfl p}
abbrev FiberPoints := {l : U⟶Cover τ hτ n ρ p // l≫projection τ hτ n ρ p=k}
@[expose] def toRoot (l : FiberPoints τ hτ n ρ p k) : Roots τ hτ n ρ p k := by
  let x : Points τ hτ U (k≫ρ) :=
    ⟨l.val≫(root τ hτ n ρ p).val,by
      rw [Category.assoc,(root τ hτ n ρ p).property]
      change l.val≫(projection τ hτ n ρ p≫ρ)=k≫ρ
      rw [←Category.assoc,l.property]⟩
  refine ⟨x,?_⟩
  apply Subtype.ext
  rw [←test_action τ hτ n x.val x.property]
  change (l.val≫pullback.fst _ _)≫multiplication τ hτ n=k≫p.val
  rw [Category.assoc,pullback.condition,←Category.assoc]
  exact congrArg (fun f => f≫p.val) l.property
@[expose] def fromRoot (r : Roots τ hτ n ρ p k) : FiberPoints τ hτ n ρ p k :=
  ⟨pullback.lift r.val.val k (by
    rw [test_action τ hτ n _ r.val.property]
    exact congrArg Subtype.val r.property),pullback.lift_snd _ _ _⟩

/-- Exact both-inverse representation of every original root by the
literal division pullback, on arbitrary, possibly nonreduced test schemes. -/
@[expose] def equivalence : FiberPoints τ hτ n ρ p k ≃ Roots τ hτ n ρ p k where
  toFun := toRoot τ hτ n ρ p k
  invFun := fromRoot τ hτ n ρ p k
  left_inv l := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans l.property.symm
  right_inv r := by
    apply Subtype.ext
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

/-- The actual kernel acts by the original represented addition law. -/
@[expose] def translate (t : torsion τ hτ n (k≫ρ)) (r : Roots τ hτ n ρ p k) :
    Roots τ hτ n ρ p k :=
  ⟨t.val+r.val,by rw [zsmul_add,t.property,r.property,zero_add]⟩
@[expose] def difference (r s : Roots τ hτ n ρ p k) : torsion τ hτ n (k≫ρ) :=
  ⟨r.val-s.val,by rw [zsmul_sub,r.property,s.property,sub_self]⟩
lemma difference_translate (t : torsion τ hτ n (k≫ρ)) (r : Roots τ hτ n ρ p k) :
    difference τ hτ n ρ p k (translate τ hτ n ρ p k t r) r=t := by
  apply Subtype.ext
  exact add_sub_cancel_right t.val r.val
lemma translate_difference (r s : Roots τ hτ n ρ p k) :
    translate τ hτ n ρ p k (difference τ hτ n ρ p k r s) s=r := by
  apply Subtype.ext
  exact sub_add_cancel r.val s.val

/-- Once a root is specified, ALL roots are uniquely its translates
by genuine whole-kernel scheme points. This states freeness/transitivity
on every test, not an assertion that a root always exists before covering. -/
@[expose] def kernelEquiv (r : Roots τ hτ n ρ p k) :
    KernelPoints τ hτ n U (k≫ρ) ≃ Roots τ hτ n ρ p k :=
  (pointsEquiv τ hτ n (k≫ρ)).trans
    { toFun := fun t => translate τ hτ n ρ p k t r
      invFun := fun s => difference τ hτ n ρ p k s r
      left_inv := fun t => difference_translate τ hτ n ρ p k t r
      right_inv := fun s => translate_difference τ hτ n ρ p k s r }
end PELOriginalDivisionRootPoints318
