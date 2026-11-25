module
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section
noncomputable section

open Algebra Polynomial

namespace OriginalSameJRetainedAffineJet318

abbrev Jet (k : Type*) [Field k] := TrivSqZeroExt k k

variable {k : Type*} [Field k]

def proj : Jet k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

theorem proj_square_zero : (RingHom.ker (proj (k:=k))) ^ 2 = ⊥ := by
  rw [pow_two]
  apply le_antisymm _ bot_le
  refine Ideal.mul_le.mpr ?_
  intro a ha b hb
  have ha' : a.fst = 0 := RingHom.mem_ker.mp ha
  have hb' : b.fst = 0 := RingHom.mem_ker.mp hb
  refine (Ideal.mem_bot (x := a*b)).mpr ?_
  apply TrivSqZeroExt.ext
  · simp [ha', hb']
  · simp [ha', hb']

section Lift

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra R k] [Algebra R (Jet k)]
variable (h : (proj (k:=k)).comp (algebraMap R (Jet k)) = algebraMap R k)

def projection : Jet k →ₐ[R] k :=
  { proj with commutes' := fun r => RingHom.congr_fun h r }

theorem projection_surj : Function.Surjective (projection h) :=
  fun y => ⟨TrivSqZeroExt.inl y, rfl⟩

theorem projection_nil : IsNilpotent (RingHom.ker (projection h).toRingHom) := by
  exact ⟨2, proj_square_zero (k:=k)⟩

variable [Algebra.FormallyEtale R A] (e : A →ₐ[R] k)

/-- The actual square-zero lift of the entire retained affine point.
The base acts on Jet through the given whole polynomial jet. -/
def lift : A →ₐ[R] Jet k :=
  Algebra.FormallySmooth.liftOfSurjective e (projection h)
    (projection_surj h) (projection_nil h)

theorem specializes : (projection h).comp (lift h e) = e :=
  Algebra.FormallySmooth.comp_liftOfSurjective e (projection h)
    (projection_surj h) (projection_nil h)

theorem unique_lift (other : A →ₐ[R] Jet k) (same : (projection h).comp other = e) :
    other = lift h e :=
  Algebra.FormallyUnramified.lift_unique' (projection h) (projection_nil h) other (lift h e)
    (same.trans (specializes h e).symm)

end Lift

section Polynomial

def namedBase (a v : k) : k[X] →ₐ[k] Jet k :=
  Polynomial.aeval ((a,v) : Jet k)

def namedResidue (a : k) : k[X] →ₐ[k] k := Polynomial.aeval a

theorem base_specializes (a v : k) :
    (proj (k:=k)).comp (namedBase a v).toRingHom = (namedResidue a).toRingHom := by
  let g : Jet k →ₐ[k] k := TrivSqZeroExt.fstHom k k k
  have h : g.comp (namedBase a v) = namedResidue a := by
    apply Polynomial.algHom_ext
    change g (namedBase a v (X:k[X])) = namedResidue a (X:k[X])
    have hx : namedBase a v (X:k[X]) = ((a,v) : Jet k) := Polynomial.aeval_X _
    have ha : namedResidue a (X:k[X]) = a := Polynomial.aeval_X _
    exact (congrArg g hx).trans ((show g ((a,v) : Jet k) = a from rfl).trans ha.symm)
  apply RingHom.ext
  intro p
  exact DFunLike.congr_fun h p

theorem namedBase_X (a v : k) : namedBase a v (Polynomial.X : k[X]) = ((a,v) : Jet k) :=
  Polynomial.aeval_X _

end Polynomial

section MarkedReads

variable {A B : Type*} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
variable (F : B →ₐ[k] A) (j : A →ₐ[k] Jet k)

def abelJet : B →ₐ[k] Jet k := j.comp F

theorem abel_whole_and_derivative (b : B) :
    abelJet F j b = j (F b) ∧ (abelJet F j b).snd = (j (F b)).snd :=
  ⟨rfl,rfl⟩

/-- Literal reciprocal read: no choice of phase or analytic measure.
Its second component is the normalized marked derivative of π. -/
theorem reciprocal_read (χ π : A) (hχπ : χ * π = 1) (a v : k)
    (ha : a ≠ 0) (hχ : j χ = ((a,v) : Jet k)) :
    (j π).fst = a⁻¹ ∧ (j π).snd = -(a⁻¹ * v * a⁻¹) := by
  let z : Jet k := ((a⁻¹, -(a⁻¹ * v * a⁻¹)) : Jet k)
  have hj : j χ * j π = 1 := by rw [← map_mul, hχπ, map_one]
  have hfst : (j χ).fst = a :=
    (congrArg (fun b : Jet k => b.fst) hχ).trans (TrivSqZeroExt.fst_mk a v)
  have hsnd : (j χ).snd = v :=
    (congrArg (fun b : Jet k => b.snd) hχ).trans (TrivSqZeroExt.snd_mk a v)
  have hzfst : z.fst = a⁻¹ := rfl
  have hzsnd : z.snd = -(a⁻¹ * v * a⁻¹) := rfl
  have hz : j χ * z = 1 := by
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_mul,hfst,hzfst,TrivSqZeroExt.fst_one]
      exact mul_inv_cancel₀ ha
    · rw [TrivSqZeroExt.snd_mul,hfst,hsnd,hzfst,hzsnd,TrivSqZeroExt.snd_one]
      simp only [op_smul_eq_smul,smul_eq_mul,mul_neg]
      have ha' : a * (a⁻¹ * v * a⁻¹) = a⁻¹ * v := by
        calc
          _ = (a * a⁻¹) * (v * a⁻¹) := by simp only [mul_assoc]
          _ = _ := by rw [mul_inv_cancel₀ ha,one_mul,mul_comm v a⁻¹]
      rw [ha',neg_add_cancel]
  have he : j π = z := by
    calc
      j π = j π * 1 := (mul_one _).symm
      _ = j π * (j χ * z) := congrArg (j π * ·) hz.symm
      _ = (j χ * j π) * z := by rw [← mul_assoc, mul_comm (j π) (j χ)]
      _ = z := by rw [hj, one_mul]
  rw [he]
  exact ⟨rfl,rfl⟩

end MarkedReads
end OriginalSameJRetainedAffineJet318

#print axioms OriginalSameJRetainedAffineJet318.specializes
#print axioms OriginalSameJRetainedAffineJet318.unique_lift
#print axioms OriginalSameJRetainedAffineJet318.base_specializes
#print axioms OriginalSameJRetainedAffineJet318.abel_whole_and_derivative
#print axioms OriginalSameJRetainedAffineJet318.reciprocal_read
