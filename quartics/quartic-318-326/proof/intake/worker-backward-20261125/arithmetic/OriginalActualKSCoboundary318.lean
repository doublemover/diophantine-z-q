module
public import OriginalActualKSCotangentOverlap318
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
An actual dε Čech coboundary acts by invertible changes of affine
first-order coordinates. The closed open-cover agreement here is
equality of the actual transition homomorphisms, not only of their
reductions or their Hodge coefficients.
-/
@[expose] public section
noncomputable section

open TrivSqZeroExt

namespace OriginalActualKSCoboundary318
open OriginalActualKSCotangentOverlap318

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The actual gauge correction of a flat affine deformation.
It is over the same base, fixes ε and is the identity on the fibre. -/
def shear (d : Derivation R A A) : Sq A →ₐ[R] Sq A where
  toFun x := inl x.fst + inr (x.snd+d x.fst)
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · simp
    · simp only [fst_add,snd_add,fst_inl,fst_inr,snd_inl,snd_inr,add_zero,zero_add,map_add]
      abel
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · simp
    · simp only [fst_mul,snd_mul,fst_add,snd_add,fst_inl,fst_inr,snd_inl,snd_inr,
        add_zero,zero_add,op_smul_eq_smul,smul_eq_mul,Derivation.leibniz]
      ring
  commutes' r := by
    rw [TrivSqZeroExt.algebraMap_eq_inl']
    simp

@[simp] theorem shear_fst (d : Derivation R A A) (x : Sq A) : (shear d x).fst=x.fst := by
  change (inl x.fst+inr (x.snd+d x.fst) : Sq A).fst=x.fst
  simp

@[simp] theorem shear_snd (d : Derivation R A A) (x : Sq A) :
    (shear d x).snd=x.snd+d x.fst := by
  change (inl x.fst+inr (x.snd+d x.fst) : Sq A).snd=_
  simp

@[simp] theorem shear_epsilon (d : Derivation R A A) : shear d (epsilon A)=epsilon A := by
  apply TrivSqZeroExt.ext
  · exact shear_fst _ _
  · simp [epsilon]

theorem shear_base_read (d : Derivation R A A)
    (x : TrivSqZeroExt R R) :
    shear d (inl (algebraMap R A x.fst) + inr (algebraMap R A x.snd)) =
      inl (algebraMap R A x.fst) + inr (algebraMap R A x.snd) := by
  apply TrivSqZeroExt.ext
  · exact shear_fst _ _
  · simp

theorem shear_add (d e : Derivation R A A) :
    (shear d).comp (shear e) = shear (d+e) := by
  apply AlgHom.ext
  intro x
  apply TrivSqZeroExt.ext
  · simp only [AlgHom.comp_apply,shear_fst]
  · simp only [AlgHom.comp_apply,shear_snd,shear_fst,Derivation.add_apply]
    abel

theorem shear_zero : shear (0 : Derivation R A A) = AlgHom.id R (Sq A) := by
  apply AlgHom.ext
  intro x
  apply TrivSqZeroExt.ext
  · simp [AlgHom.id_apply]
  · simp [AlgHom.id_apply]

def gauge (d : Derivation R A A) : Sq A ≃ₐ[R] Sq A :=
  AlgEquiv.ofAlgHom (shear d) (shear (-d))
    (by rw [shear_add,add_neg_cancel,shear_zero])
    (by rw [shear_add,neg_add_cancel,shear_zero])

theorem shear_faithful : Function.Injective (shear (R:=R) (A:=A)) := by
  intro d e h
  apply Derivation.ext
  intro a
  have q := congrArg (fun F : Sq A →ₐ[R] Sq A => (F (inl a)).snd) h
  simpa only [shear_snd,snd_inl,fst_inl,zero_add] using q

/-- On the actual overlap the Čech difference does not just compare
symbol matrices: its automorphism carries the first lift to the second. -/
theorem carries_actual_lift (s t : Lift R A) :
    (shear (difference s t)).comp s.arrow = t.arrow := by
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · simpa only [AlgHom.comp_apply,shear_fst] using (s.reduced a).trans (t.reduced a).symm
  · rw [AlgHom.comp_apply,shear_snd,s.reduced]
    change (s.arrow a).snd + ((t.arrow a).snd - (s.arrow a).snd) = (t.arrow a).snd
    abel

/-- A self-map of the genuine split affine chart that fixes the base
ε and the reduced algebra is recovered from its actual lifting of
constant functions. -/
def backLift (F : Sq A →ₐ[R] Sq A)
    (red : ∀ x : Sq A, (F x).fst=x.fst) : Lift R A where
  arrow := F.comp (TrivSqZeroExt.inlAlgHom R A A)
  reduced a := by
    change (F (inl a)).fst=a
    rw [red,fst_inl]

def constantLift (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] : Lift R A where
  arrow := TrivSqZeroExt.inlAlgHom R A A
  reduced _ := rfl

theorem recover_actual_chart_map (F : Sq A →ₐ[R] Sq A)
    (red : ∀ x : Sq A, (F x).fst=x.fst)
    (base : F (epsilon A)=epsilon A) :
    F = shear (difference (constantLift R A) (backLift F red)) := by
  let d := difference (constantLift R A) (backLift F red)
  change F=shear d
  apply AlgHom.ext
  intro x
  have hr : F (inr x.snd) = inr x.snd := by
    have hx : (inr x.snd : Sq A) = epsilon A * inl x.snd := by
      rw [epsilon,inr_mul_inl]
      congr 1
      rw [op_smul_eq_smul,smul_eq_mul,mul_one]
    rw [hx,map_mul,base]
    apply TrivSqZeroExt.ext
    · simp [epsilon]
    · simp only [epsilon,snd_mul,fst_inr,snd_inr,
        op_smul_eq_smul,smul_eq_mul,zero_mul,zero_add,mul_one,red,fst_inl]
  apply TrivSqZeroExt.ext
  · rw [red,shear_fst]
  · have q : F x = F (inl x.fst) + inr x.snd := by
      calc
        F x = F (inl x.fst + inr x.snd) :=
          congrArg F (inl_fst_add_inr_snd_eq x).symm
        _ = _ := by rw [map_add,hr]
    rw [q,snd_add,snd_inr,shear_snd]
    change (F (inl x.fst)).snd + x.snd = x.snd+((F (inl x.fst)).snd-0)
    abel

/-- Local cohomological triviality gives equality of the actual
transition map after correcting source and target trivializations. -/
theorem actual_coboundary_kills_transition
    (F : Sq A →ₐ[R] Sq A) (red : ∀ x : Sq A, (F x).fst=x.fst)
    (base : F (epsilon A)=epsilon A) (d_i d_j : Derivation R A A)
    (boundary : difference (constantLift R A) (backLift F red) = d_j-d_i) :
    (shear (-d_j)).comp (F.comp (shear d_i)) = AlgHom.id R (Sq A) := by
  rw [recover_actual_chart_map F red base,boundary,shear_add,shear_add]
  have h : -d_j + (d_j-d_i+d_i) = 0 := by abel
  rw [h,shear_zero]

end OriginalActualKSCoboundary318

#print axioms OriginalActualKSCoboundary318.shear_base_read
#print axioms OriginalActualKSCoboundary318.shear_faithful
#print axioms OriginalActualKSCoboundary318.carries_actual_lift
#print axioms OriginalActualKSCoboundary318.recover_actual_chart_map
#print axioms OriginalActualKSCoboundary318.actual_coboundary_kills_transition
