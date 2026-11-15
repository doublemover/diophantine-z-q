module
public import PELPrimeIsogenyFibers318
public import PELNormalizerProjectiveLevel318
public import Mathlib.Algebra.Group.Units.Hom
public section
noncomputable section
namespace PELNormalizerPrincipalConjugation318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELPositiveOrderNormalizer318
open PELQuaternionNormParity318 PELPrincipalThreeFreeAction318 PELJointNormOneAction318
set_option maxHeartbeats 1800000

/-- Actual inner conjugation by ANY positive original-order normalizer,
restricted to the entire same integral order in both directions. -/
@[expose] def conjugation (g : positiveNormalizer) : order ≃+* order where
  toFun x := ⟨(g.val:B)*(x:B)*((g.val⁻¹:Bˣ):B),(g.property.1 x x.property).1⟩
  invFun x := ⟨((g.val⁻¹:Bˣ):B)*(x:B)*(g.val:B),(g.property.1 x x.property).2⟩
  left_inv x := by
    apply Subtype.ext
    change ((g.val⁻¹:Bˣ):B)*((g.val:B)*(x:B)*((g.val⁻¹:Bˣ):B))*(g.val:B)=(x:B)
    calc
      _ = (((g.val⁻¹:Bˣ):B)*(g.val:B))*(x:B)*(((g.val⁻¹:Bˣ):B)*(g.val:B)) := by noncomm_ring
      _ = _ := by rw [Units.inv_val,one_mul,mul_one]
  right_inv x := by
    apply Subtype.ext
    change (g.val:B)*(((g.val⁻¹:Bˣ):B)*(x:B)*(g.val:B))*((g.val⁻¹:Bˣ):B)=(x:B)
    calc
      _ = ((g.val:B)*((g.val⁻¹:Bˣ):B))*(x:B)*((g.val:B)*((g.val⁻¹:Bˣ):B)) := by noncomm_ring
      _ = _ := by rw [Units.val_inv,one_mul,mul_one]
  map_add' x y := by
    apply Subtype.ext
    change (g.val:B)*((x:B)+(y:B))*((g.val⁻¹:Bˣ):B)=
      (g.val:B)*(x:B)*((g.val⁻¹:Bˣ):B)+(g.val:B)*(y:B)*((g.val⁻¹:Bˣ):B)
    noncomm_ring
  map_mul' x y := by
    apply Subtype.ext
    change (g.val:B)*((x:B)*(y:B))*((g.val⁻¹:Bˣ):B)=
      ((g.val:B)*(x:B)*((g.val⁻¹:Bˣ):B))*((g.val:B)*(y:B)*((g.val⁻¹:Bˣ):B))
    calc
      _ = (g.val:B)*(x:B)*((((g.val⁻¹:Bˣ):B)*(g.val:B))*(y:B))*((g.val⁻¹:Bˣ):B) := by
        rw [Units.inv_val,one_mul]
        all_goals noncomm_ring
      _ = _ := by noncomm_ring

theorem conjugation_value (g : positiveNormalizer) (x : order) :
    (conjugation g x:B)=(g.val:B)*(x:B)*((g.val⁻¹:Bˣ):B) := rfl

theorem conjugation_norm (g : positiveNormalizer) (x : order) :
    reducedNorm (conjugation g x:B)=reducedNorm (x:B) := by
  have hu : reducedNorm (g.val:B)*reducedNorm ((g.val⁻¹:Bˣ):B)=1 := by
    rw [←norm_mul,Units.val_inv]
    norm_num [reducedNorm]
  rw [conjugation_value,norm_mul,norm_mul]
  calc
    _ = (reducedNorm (g.val:B)*reducedNorm ((g.val⁻¹:Bˣ):B))*reducedNorm (x:B) := by ring
    _ = _ := by rw [hu,one_mul]

@[expose] def conjugateUnit (g : positiveNormalizer) : orderˣ →* orderˣ :=
  Units.map (conjugation g).toMonoidHom

/-- The exact principal-three subgroup is stable: both original reduced
norm1 and u=1+3v are transported in the SAME order. -/
theorem conjugateUnit_principal (g : positiveNormalizer) (u : principalThree) :
    conjugateUnit g u.val∈principalThree := by
  constructor
  · apply (mem_normOneUnits _).mpr
    change reducedNorm (conjugation g (u.val:order):B)=1
    rw [conjugation_norm]
    exact (mem_normOneUnits u.val).mp u.property.1
  · obtain ⟨v,hv⟩ := u.property.2
    refine ⟨conjugation g v,?_⟩
    change conjugation g (u.val:order)=1+(3:ℕ) • conjugation g v
    rw [hv,map_add,map_one,map_nsmul]

@[expose] def principalConjugation (g : positiveNormalizer) : principalThree →* principalThree where
  toFun u := ⟨conjugateUnit g u.val,conjugateUnit_principal g u⟩
  map_one' := Subtype.ext (map_one (conjugateUnit g))
  map_mul' u v := Subtype.ext (map_mul (conjugateUnit g) u.val v.val)

theorem principalConjugation_value (g : positiveNormalizer) (u : principalThree) :
    (((principalConjugation g u).val:order):B)=
      (g.val:B)*((u.val:order):B)*((g.val⁻¹:Bˣ):B) := rfl

/-- The intertwining identity is in the original rational quaternion
algebra, before applying any real splitting or Möbius action. -/
theorem original_intertwining (g : positiveNormalizer) (u : principalThree) :
    (((principalConjugation g u).val:order):B)*(g.val:B)=
      (g.val:B)*((u.val:order):B) := by
  rw [principalConjugation_value]
  simp only [mul_assoc,Units.inv_val,mul_one]
end PELNormalizerPrincipalConjugation318
