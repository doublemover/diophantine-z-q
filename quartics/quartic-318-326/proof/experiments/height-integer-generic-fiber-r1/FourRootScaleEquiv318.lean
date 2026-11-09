module
public import FourRootPointUniversal318
public section
noncomputable section
namespace FourRootScaleEquiv318
open FourRootOrder318 FourRootOrderSigns318
set_option maxHeartbeats 600000
variable {R : Type*} [CommRing R] (a b : Fin 4 → R) (d : Rˣ)
    (h : ∀ i, b i = (d : R)^2 * a i)

/-- The exact generator-rescaling map on all four actual tensor factors. -/
@[expose] def forward : Order b →ₐ[R] Order a :=
  FourRootPointUniversal318.point b
    (fun i => algebraMap R (Order a) (d : R) * generator a i) (by
      intro i
      rw [mul_pow, generator_square, ← map_pow, ← map_mul, ← h])

@[simp] theorem forward_generator (i : Fin 4) :
    forward a b d h (generator b i) =
      algebraMap R (Order a) (d : R) * generator a i :=
  FourRootPointUniversal318.point_generator _ _ _ _

include h in
lemma inverse_parameters (i : Fin 4) : a i = (↑d⁻¹ : R)^2 * b i := by
  rw [h, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]

/-- This equivalence identifies the entire specialized four-root algebras,
including every tensor factor, not just a chosen field quotient. -/
@[expose] def equiv : Order b ≃ₐ[R] Order a :=
  AlgEquiv.ofAlgHom (forward a b d h)
    (forward b a d⁻¹ (inverse_parameters a b d h))
    (by
      apply FourRootSignBaseChange318.hom_ext
      intro i
      simp only [AlgHom.comp_apply, forward_generator, map_mul, AlgHom.commutes,
        AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul])
    (by
      apply FourRootSignBaseChange318.hom_ext
      intro i
      simp only [AlgHom.comp_apply, forward_generator, map_mul, AlgHom.commutes,
        AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul])

@[simp] theorem equiv_generator (i : Fin 4) :
    equiv a b d h (generator b i) =
      algebraMap R (Order a) (d : R) * generator a i :=
  forward_generator a b d h i

end FourRootScaleEquiv318
