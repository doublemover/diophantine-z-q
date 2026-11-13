module
public import FiniteDualModuleAction318
public section
noncomputable section
namespace ScalarChangedFiniteDual318
open FiniteDualModuleAction318
variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] (σ : R ≃+* S) (e : A ≃+* B)
  (h : ∀ r, e (algebraMap R A r)=algebraMap S B (σ r))

include h in
lemma inverse_scalar (s : S) :
    e.symm (algebraMap S B s)=algebraMap R A (σ.symm s) := by
  apply e.injective
  rw [e.apply_symm_apply,h,σ.apply_symm_apply]

/-- Both the input order and the output coefficient ring are transported.
Keeping only precomposition would give the wrong reciprocal scalar. -/
@[expose] def map (f : Dual R A) : Dual S B where
  toFun b := σ (f (e.symm b))
  map_add' b c := by rw [map_add,map_add,map_add]
  map_smul' s b := by
    change σ (f (e.symm (algebraMap S B s*b)))=s*σ (f (e.symm b))
    rw [map_mul,inverse_scalar σ e h]
    change σ (f ((σ.symm s) • e.symm b))=_
    rw [map_smul]
    change σ (σ.symm s*f (e.symm b))=_
    rw [map_mul,σ.apply_symm_apply]

lemma value (f : Dual R A) (b : B) :
    map σ e h f b=σ (f (e.symm b)) := rfl

/-- Entire duals, with the OLD multiplication-precomposition actions. -/
@[expose] def equivalence : Dual R A ≃ₛₗ[e.toRingHom] Dual S B where
  toFun := map σ e h
  invFun := map σ.symm e.symm (inverse_scalar σ e h)
  left_inv f := by
    apply LinearMap.ext
    intro a
    change σ.symm (σ (f (e.symm (e a))))=f a
    rw [e.symm_apply_apply,σ.symm_apply_apply]
  right_inv f := by
    apply LinearMap.ext
    intro b
    change σ (σ.symm (f (e (e.symm b))))=f b
    rw [e.apply_symm_apply,σ.apply_symm_apply]
  map_add' f g := by
    apply LinearMap.ext
    intro b
    exact σ.map_add _ _
  map_smul' a f := by
    apply LinearMap.ext
    intro b
    change σ (f (a*e.symm b))=σ (f (e.symm (e a*b)))
    rw [map_mul,e.symm_apply_apply]

lemma at_image (f : Dual R A) (a : A) :
    equivalence σ e h f (e a)=σ (f a) := by
  change σ (f (e.symm (e a)))=_
  rw [e.symm_apply_apply]
end ScalarChangedFiniteDual318
