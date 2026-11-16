module
public import PELOriginalEtaleOrderIsogeny318
public section
noncomputable section
namespace PELOriginalOrderDivisionRootPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalSchemePointGroup318 PELOriginalOrderSchemeMorphism318
open PELOriginalOrderLocalDivision318 PELOriginalOrderKernelScheme318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : PELPrincipalOrderCoordinates318.order)
variable {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ)) (p : Points τ hτ T ρ)
abbrev kernelPointsEquiv {U : Scheme} (σ : U⟶Spec (CommRingCat.of ℂ)) :=
  PELOriginalOrderKernelScheme318.equivalence τ hτ a σ
variable {U : Scheme} (k : U⟶T)
/-- ALL original order-roots over the specified arbitrary test map. -/
abbrev Roots := {x : Points τ hτ U (k≫ρ) // PELOriginalUniversalOrderAction318.endomorphism τ hτ (k≫ρ) a x=pull τ hτ ρ k rfl p}
abbrev FiberPoints := {l : U⟶Cover τ hτ a ρ p // l≫projection τ hτ a ρ p=k}
@[expose] def toRoot (l : FiberPoints τ hτ a ρ p k) : Roots τ hτ a ρ p k := by
  let x : Points τ hτ U (k≫ρ) :=
    ⟨l.val≫(root τ hτ a ρ p).val,by
      rw [Category.assoc,(root τ hτ a ρ p).property]
      change l.val≫(projection τ hτ a ρ p≫ρ)=k≫ρ
      rw [←Category.assoc,l.property]⟩
  refine ⟨x,?_⟩
  apply Subtype.ext
  change (l.val≫pullback.fst _ _)≫morphism τ hτ a=k≫p.val
  rw [Category.assoc,pullback.condition,←Category.assoc]
  exact congrArg (fun f => f≫p.val) l.property
@[expose] def fromRoot (r : Roots τ hτ a ρ p k) : FiberPoints τ hτ a ρ p k :=
  ⟨pullback.lift r.val.val k (by
    exact congrArg Subtype.val r.property),pullback.lift_snd _ _ _⟩

/-- Exact both-inverse representation of every original root by the
literal division pullback, on arbitrary, possibly nonreduced test schemes. -/
@[expose] def equivalence : FiberPoints τ hτ a ρ p k ≃ Roots τ hτ a ρ p k where
  toFun := toRoot τ hτ a ρ p k
  invFun := fromRoot τ hτ a ρ p k
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
@[expose] def translate (t : PointKernel τ hτ a (k≫ρ)) (r : Roots τ hτ a ρ p k) :
    Roots τ hτ a ρ p k :=
  ⟨t.val+r.val,by rw [map_add,t.property,r.property,zero_add]⟩
/-- The genuine kernel addition acts with its original identity and
associativity on every test root set. -/
lemma translate_zero (r : Roots τ hτ a ρ p k) :
    translate τ hτ a ρ p k 0 r=r := by
  apply Subtype.ext
  exact zero_add r.val
lemma translate_add (t u : PointKernel τ hτ a (k≫ρ)) (r : Roots τ hτ a ρ p k) :
    translate τ hτ a ρ p k (t+u) r=
      translate τ hτ a ρ p k t (translate τ hτ a ρ p k u r) := by
  apply Subtype.ext
  exact add_assoc t.val u.val r.val
@[expose] def difference (r s : Roots τ hτ a ρ p k) : PointKernel τ hτ a (k≫ρ) :=
  ⟨r.val-s.val,by rw [map_sub,r.property,s.property,sub_self]⟩
lemma difference_translate (t : PointKernel τ hτ a (k≫ρ)) (r : Roots τ hτ a ρ p k) :
    difference τ hτ a ρ p k (translate τ hτ a ρ p k t r) r=t := by
  apply Subtype.ext
  exact add_sub_cancel_right t.val r.val
lemma translate_difference (r s : Roots τ hτ a ρ p k) :
    translate τ hτ a ρ p k (difference τ hτ a ρ p k r s) s=r := by
  apply Subtype.ext
  exact sub_add_cancel r.val s.val

/-- Once a root is specified, ALL roots are uniquely its translates
by genuine whole-kernel scheme points. This states freeness/transitivity
on every test, not an assertion that a root always exists before covering. -/
@[expose] def kernelEquiv (r : Roots τ hτ a ρ p k) :
    KernelPoint τ hτ a (k≫ρ) ≃ Roots τ hτ a ρ p k :=
  (kernelPointsEquiv τ hτ a (k≫ρ)).trans
    { toFun := fun t => translate τ hτ a ρ p k t r
      invFun := fun s => difference τ hτ a ρ p k s r
      left_inv := fun t => difference_translate τ hτ a ρ p k t r
      right_inv := fun s => translate_difference τ hτ a ρ p k s r }
end PELOriginalOrderDivisionRootPoints318
