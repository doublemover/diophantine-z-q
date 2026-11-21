module
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section

namespace SelectedActualIntegralAlgebraGenericSection318

variable {R B L : Type*} [CommRing R] [CommRing B] [Field L]
variable [Algebra R B] [Algebra R L] [IsFractionRing R L] [IsIntegrallyClosed R]
variable [Algebra.IsIntegral R B] (g : B →ₐ[R] L)

private theorem lies_in_actual_base (b : B) :
    ∃ r : R, algebraMap R L r = g b :=
  IsIntegrallyClosed.algebraMap_eq_of_integral
    ((Algebra.IsIntegral.isIntegral b : IsIntegral R b).map g)

private def coeff (b : B) : R := (lies_in_actual_base g b).choose

private theorem coeff_eq (b : B) : algebraMap R L (coeff g b) = g b :=
  (lies_in_actual_base g b).choose_spec

/-- The designated generic section of a given integral algebra
lands in the same normal base. A point of the opposite level or a
new solution branch is never chosen. -/
def integralSection : B →ₐ[R] R where
  toFun := coeff g
  map_zero' := IsFractionRing.injective R L (by rw [coeff_eq,map_zero,map_zero])
  map_one' := IsFractionRing.injective R L (by rw [coeff_eq,map_one,map_one])
  map_add' x y := IsFractionRing.injective R L (by rw [coeff_eq,map_add,map_add,coeff_eq,coeff_eq])
  map_mul' x y := IsFractionRing.injective R L (by rw [coeff_eq,map_mul,map_mul,coeff_eq,coeff_eq])
  commutes' a := IsFractionRing.injective R L (by
    rw [coeff_eq,g.commutes,Algebra.algebraMap_self,RingHom.id_apply])

@[simp]
theorem integralSection_field (b : B) : algebraMap R L (integralSection g b) = g b :=
  coeff_eq g b

theorem integralSection_generic : (Algebra.ofId R L).comp (integralSection g) = g := by
  ext b
  exact integralSection_field g b

theorem unique_same_section (s : B →ₐ[R] R)
    (hs : (Algebra.ofId R L).comp s = g) : s = integralSection g := by
  apply AlgHom.ext
  intro b
  apply IsFractionRing.injective R L
  exact (congrArg (fun f : B →ₐ[R] L => f b) hs).trans (integralSection_field g b).symm

theorem existsUnique_integralSection :
    ∃! s : B →ₐ[R] R, (Algebra.ofId R L).comp s = g :=
  ⟨integralSection g,integralSection_generic g,unique_same_section g⟩

end SelectedActualIntegralAlgebraGenericSection318

#print axioms SelectedActualIntegralAlgebraGenericSection318.existsUnique_integralSection
