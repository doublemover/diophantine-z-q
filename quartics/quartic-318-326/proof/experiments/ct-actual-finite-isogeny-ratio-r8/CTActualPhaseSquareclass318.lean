module
public import CTActualQuadraticRootSigns318
public import ActualTwoDescentSquareClassQuotient318
import all CTActualQuadraticRootSigns318
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public section

noncomputable section

namespace CTActualPhaseSquareclass318

open CTActualQuadraticRootSigns318 CTFieldPrimitiveRestriction318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentClosureFieldEmbedding318

variable (K : Type) [Field K] [CharZero K]
local notation "A" => AlgebraicClosure K
local notation "ι" => (algebraMap K A)
local instance : DecidableEq A := Classical.decEq _

/-- Literal squareclass equality is exactly equality of these two
continuous absolute root phases, even if the two roots were chosen
independently. No additional H¹ comparison is assumed here. -/
theorem phase_eq_iff_squareclass_eq (a b : Kˣ) (r s : Aˣ)
    (hr : (r:A)^2=ι (a:K)) (hs : (s:A)^2=ι (b:K)) :
    (∀ g : Gal K, phase K r g=phase K s g) ↔
      classOf (a:K) a.ne_zero=classOf (b:K) b.ne_zero := by
  constructor
  · intro h
    have hFix (σ : A ≃ₐ[K] A) : σ ((r:A)/(s:A))=(r:A)/(s:A) := by
      let g : Gal K := σ
      have hR := act_on_square_root K r a hr g
      have hS := act_on_square_root K s b hs g
      change σ (r:A)=fieldSign K (phase K r g) (r:A) at hR
      change σ (s:A)=fieldSign K (phase K s g) (s:A) at hS
      rw [map_div₀,hR,hS,h g]
      cases phase K s g <;> simp [fieldSign]
    obtain ⟨z,hz⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k:=K)
      ((r:A)/(s:A))).mpr hFix
    have hz0 : z≠0 := by
      intro h0
      rw [h0,map_zero] at hz
      exact div_ne_zero r.ne_zero s.ne_zero hz.symm
    apply (class_of_eq_iff _ _ _ _).mpr
    refine ⟨z,hz0,?_⟩
    apply ι.injective
    rw [map_mul,map_pow,hz,div_pow,hr,hs]
    field_simp [map_ne_zero ι b.ne_zero] <;> ring
  · intro h g
    obtain ⟨z,hz,hA⟩ := (class_of_eq_iff _ _ _ _).mp h
    have hzA : ι z≠0 := map_ne_zero ι hz
    have hSq : (r:A)^2=((s:A)*ι z)^2 := by rw [mul_pow,hs,hr,hA,map_mul,map_pow]
    have hFixed : (act K g (r:A)=(r:A)) ↔ (act K g (s:A)=(s:A)) := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hSq with hh | hh
      · simp only [hh,map_mul,(act K g).commutes]
        constructor
        · exact mul_right_cancel₀ hzA
        · intro he
          rw [he]
      · simp only [hh,map_neg,map_mul,(act K g).commutes,neg_inj]
        constructor
        · exact mul_right_cancel₀ hzA
        · intro he
          rw [he]
    simp only [phase,hFixed]

variable {L : Type} [Field L] [CharZero L]

/-- Restriction uses the same closure embedding as the literal original
point restriction. The locally constant scalar phases commute before
passing to any quotient or invoking the global product theorem. -/
theorem actual_phase_restriction (f : K →+* L) (r : Aˣ) (g : Gal L) :
    phase L (Units.map (closureMap f).toMonoidHom r) g =
      phase K r (Field.absoluteGaloisGroup.map f g) := by
  change (if act L g (closureMap f (r:A)) = closureMap f (r:A) then false else true) =
    (if act K (Field.absoluteGaloisGroup.map f g) (r:A) = (r:A) then false else true)
  have h : closureMap f (act K (Field.absoluteGaloisGroup.map f g) (r:A)) =
    act L g (closureMap f (r:A)) := actual_closure_map_galois f g (r:A)
  rw [←h]
  have he : (closureMap f (act K (Field.absoluteGaloisGroup.map f g) (r:A)) =
      closureMap f (r:A)) ↔ act K (Field.absoluteGaloisGroup.map f g) (r:A)=(r:A) :=
    ⟨(closureMap f).injective,congrArg (closureMap f)⟩
  simp only [he]

end CTActualPhaseSquareclass318

#print axioms CTActualPhaseSquareclass318.phase_eq_iff_squareclass_eq
#print axioms CTActualPhaseSquareclass318.actual_phase_restriction
