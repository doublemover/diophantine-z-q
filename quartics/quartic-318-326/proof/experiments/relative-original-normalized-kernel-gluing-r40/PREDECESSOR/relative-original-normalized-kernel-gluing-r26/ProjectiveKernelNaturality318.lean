module
public import ProjectiveKernelParameter318
public section
noncomputable section
namespace ProjectiveKernelNaturality318
open scoped TensorProduct
universe u v w
variable (R P Q : Type u) [CommRing R] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] (d : P →ₗ[R] Q)
  (S : Type v) [CommRing S] [Algebra R S]
  {T : Type w} [CommRing T] [Algebra R T]

lemma transport_square (g : S →ₐ[R] T) (x : S ⊗[R] P) :
    d.baseChange T (ProjectiveSectionParameter318.transport R P S g x)=
      ProjectiveSectionParameter318.transport R Q S g (d.baseChange S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Actual tensor coefficient transport restricts to the genuine differential kernel. -/
@[expose] def transport (g : S →ₐ[R] T) (x : LinearMap.ker (d.baseChange S)) :
    LinearMap.ker (d.baseChange T) :=
  ⟨ProjectiveSectionParameter318.transport R P S g x.val,by
    rw [transport_square,x.property,map_zero]⟩

variable [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]

lemma natural (g : S →ₐ[R] T) (a : ProjectiveKernelParameter318.algebra R P Q d →ₐ[R] S) :
    ProjectiveKernelParameter318.points R P Q d T (g.comp a)=
      transport R P Q d S g (ProjectiveKernelParameter318.points R P Q d S a) := by
  apply Subtype.ext
  exact ProjectiveSectionParameter318.natural R P S g
    (a.comp (ProjectiveKernelParameter318.quotient R P Q d))

/-- A single actual universal kernel section, not a point-dependent existence choice. -/
@[expose] def universal :
    LinearMap.ker (d.baseChange (ProjectiveKernelParameter318.algebra R P Q d)) :=
  ProjectiveKernelParameter318.points R P Q d _ (AlgHom.id R _)

lemma specialize (a : ProjectiveKernelParameter318.algebra R P Q d →ₐ[R] S) :
    transport R P Q d (ProjectiveKernelParameter318.algebra R P Q d) a
      (universal R P Q d)=ProjectiveKernelParameter318.points R P Q d S a := by
  simpa only [universal,AlgHom.comp_id] using
    (natural R P Q d (ProjectiveKernelParameter318.algebra R P Q d) a (AlgHom.id R _)).symm
end ProjectiveKernelNaturality318
