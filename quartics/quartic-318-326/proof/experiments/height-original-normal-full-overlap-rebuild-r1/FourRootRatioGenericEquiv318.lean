module
public import FourRootRatioOrder318
public section
noncomputable section
namespace FourRootRatioGenericEquiv318
open FourRootRatioOrder318 FourRootOrderSigns318
variable {R : Type*} [CommRing R] (q : R) (r : Fin 3 → R) (hq : IsUnit q)

include hq in
lemma root_unit : IsUnit (generator (original q r) 0) := by
  apply (isUnit_pow_iff (by decide : (2:ℕ)≠0)).mp
  rw [generator_square]
  exact hq.map (algebraMap R (OriginalOrder q r))
@[expose] def rootUnit : (OriginalOrder q r)ˣ := (root_unit q r hq).unit
lemma rootUnit_value : (rootUnit q r hq : OriginalOrder q r) = generator (original q r) 0 :=
  (root_unit q r hq).unit_spec
lemma rootUnit_square : (rootUnit q r hq : OriginalOrder q r)^2 =
    algebraMap R (OriginalOrder q r) q := by
  rw [rootUnit_value,generator_square]
  rfl

@[expose] def inverseRoot : Fin 4 → OriginalOrder q r :=
  Fin.cases (generator (original q r) 0)
    (fun i => (↑(rootUnit q r hq)⁻¹ : OriginalOrder q r)*generator (original q r) i.succ)
lemma inverseRoot_square (i : Fin 4) : inverseRoot q r hq i ^2 =
    algebraMap R (OriginalOrder q r) (normalized q r i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact generator_square (original q r) 0
  · simp only [inverseRoot,Fin.cases_succ,mul_pow,generator_square,
      original,normalized,Fin.cases_succ,map_mul]
    rw [←rootUnit_square q r hq,←mul_assoc,←mul_pow,Units.inv_mul,one_pow,one_mul]

/-- Actual inverse on the WHOLE order where the common ramified factor is
a unit. No fraction-field or pointwise surjectivity hypothesis is used. -/
@[expose] def inverse : RatioOrder q r →ₐ[R] OriginalOrder q r :=
  IntegralRootPointMaps318.fourMap (normalized q r) (inverseRoot q r hq)
    (inverseRoot_square q r hq)
lemma inverse_root (i : Fin 4) : inverse q r hq (generator (normalized q r) i)=
    inverseRoot q r hq i := IntegralRootPointMaps318.fourMap_generator _ _ _ i

lemma inverse_map : (inverse q r hq).comp (map q r) = AlgHom.id R (OriginalOrder q r) := by
  apply FourRootSignBaseChange318.hom_ext
  intro i
  change inverse q r hq (map q r (generator (original q r) i)) = _
  rw [map_root]
  refine Fin.cases ?_ (fun i => ?_) i
  · exact inverse_root q r hq 0
  · change inverse q r hq
      (generator (normalized q r) 0 * generator (normalized q r) i.succ) =
      generator (original q r) i.succ
    rw [map_mul,inverse_root,inverse_root]
    change generator (original q r) 0 *
      ((↑(rootUnit q r hq)⁻¹ : OriginalOrder q r)*generator (original q r) i.succ) = _
    rw [←rootUnit_value q r hq,←mul_assoc,Units.mul_inv,one_mul]

lemma map_inverse : (map q r).comp (inverse q r hq) = AlgHom.id R (RatioOrder q r) := by
  apply FourRootSignBaseChange318.hom_ext
  intro i
  change map q r (inverse q r hq (generator (normalized q r) i)) = _
  rw [inverse_root]
  refine Fin.cases ?_ (fun i => ?_) i
  · exact map_root q r 0
  · change map q r ((↑(rootUnit q r hq)⁻¹ : OriginalOrder q r)*generator (original q r) i.succ)=_
    rw [map_mul,map_root]
    have hu : map q r (↑(rootUnit q r hq)⁻¹ : OriginalOrder q r) *
        generator (normalized q r) 0 = 1 := by
      have hh := congrArg (map q r) (Units.inv_mul (rootUnit q r hq))
      rw [map_mul,map_one,rootUnit_value,map_root] at hh
      exact hh
    change map q r (↑(rootUnit q r hq)⁻¹ : OriginalOrder q r) *
      (generator (normalized q r) 0 * generator (normalized q r) i.succ)=_
    rw [←mul_assoc,hu,one_mul]

@[expose] def equiv : OriginalOrder q r ≃ₐ[R] RatioOrder q r :=
  AlgEquiv.ofAlgHom (map q r) (inverse q r hq) (map_inverse q r hq) (inverse_map q r hq)
lemma equiv_root (i : Fin 4) : equiv q r hq (generator (original q r) i)=marked q r i :=
  map_root q r i
end FourRootRatioGenericEquiv318
