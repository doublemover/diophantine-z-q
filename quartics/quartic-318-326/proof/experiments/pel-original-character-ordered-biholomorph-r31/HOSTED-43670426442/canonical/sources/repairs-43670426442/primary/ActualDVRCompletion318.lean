module
public import SeparatedPrincipalLocal318
public import CompleteContactEvaluation318
public section
noncomputable section
namespace ActualDVRCompletion318
set_option maxHeartbeats 600000
open Ideal IsLocalRing PowerSeries
variable (R:Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

abbrev Completion:=AdicCompletion (maximalIdeal R) R

theorem completion_injective : Function.Injective (algebraMap R (Completion R)) := by
  intro x y h
  apply AdicCompletion.of_injective (maximalIdeal R) R
  simpa only [AdicCompletion.algebraMap_apply,Algebra.algebraMap_self,RingHom.id_apply] using h

theorem completion_maximal (pi:R) (hp:Irreducible pi) :
    maximalIdeal (Completion R)=Ideal.span {algebraMap R (Completion R) pi} := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  calc
    _=(Ideal.span {pi}).map (algebraMap R (Completion R)) :=
      congrArg (fun I:Ideal R=>I.map (algebraMap R (Completion R))) hp.maximalIdeal_eq
    _=_ := by rw [Ideal.map_span];simp

theorem completion_domain : IsDomain (Completion R) := by
  obtain ⟨pi,hp⟩:=IsDiscreteValuationRing.exists_irreducible R
  apply SeparatedPrincipalLocal318.domain (algebraMap R (Completion R) pi)
    (completion_maximal R pi hp)
  intro n h
  apply pow_ne_zero n hp.ne_zero
  apply completion_injective R
  simpa only [map_pow,map_zero] using h

instance : IsDomain (Completion R) := completion_domain R

theorem completion_principal : IsPrincipalIdealRing (Completion R) := by
  obtain ⟨pi,hp⟩:=IsDiscreteValuationRing.exists_irreducible R
  exact SeparatedPrincipalLocal318.principal (algebraMap R (Completion R) pi)
    (completion_maximal R pi hp)

instance : IsDiscreteValuationRing (Completion R) where
  toIsPrincipalIdealRing:=completion_principal R
  toIsLocalRing:=inferInstance
  not_a_field':=by
    obtain ⟨pi,hp⟩:=IsDiscreteValuationRing.exists_irreducible R
    rw [completion_maximal R pi hp]
    intro h
    have hz:algebraMap R (Completion R) pi=0 := by
      have hi:algebraMap R (Completion R) pi∈Ideal.span {algebraMap R (Completion R) pi}:=
        Ideal.subset_span (by simp)
      rw [h] at hi
      exact hi
    apply hp.ne_zero
    apply completion_injective R
    simpa only [map_zero] using hz

/-- The actual completed DVR is complete and separated at its actual maximal ideal. -/
theorem completion_complete : IsAdicComplete (maximalIdeal (Completion R)) (Completion R) :=
  inferInstance

theorem completed_uniformizer (pi:R) (hp:Irreducible pi) :
    Irreducible (algebraMap R (Completion R) pi) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ (by
      intro h
      apply hp.ne_zero
      exact completion_injective R (by simpa only [map_zero] using h))
    (completion_maximal R pi hp)


theorem completion_value (x:R) :
    IsDiscreteValuationRing.addVal (Completion R) (algebraMap R (Completion R) x)=
      IsDiscreteValuationRing.addVal R x := by
  by_cases hx:x=0
  · simp [hx]
  obtain ⟨pi,hp⟩:=IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n,u,rfl⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hp
  rw [map_mul,map_pow,IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_mul,hp.addVal_pow,(completed_uniformizer R pi hp).addVal_pow,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit]
  have hu:IsDiscreteValuationRing.addVal (Completion R) (algebraMap R (Completion R) (u:R))=0 := by
    exact IsDiscreteValuationRing.addVal_eq_zero_of_unit
      (Units.map (algebraMap R (Completion R)).toMonoidHom u)
  rw [hu]

/-- The actual completion supplies the target, topology/completeness, and
coefficient map for positive-contact formal evaluation. -/
theorem completed_contact_map {A:Type*} [CommRing A] (f:A→+*R)
    (u:Rˣ) (pi:R) (m:ℕ) (hp:Irreducible pi) (hm:0<m) :
    ∃e:A⟦X⟧→+*Completion R,
      e PowerSeries.X=algebraMap R (Completion R) ((u:R)*pi^(2*m)) ∧
      ∀a:A,e (PowerSeries.C a)=algebraMap R (Completion R) (f a) := by
  obtain ⟨e,he,hc⟩:=CompleteContactEvaluation318.complete_dvr_map (completion_complete R)
    ((algebraMap R (Completion R)).comp f)
    (Units.map (algebraMap R (Completion R)).toMonoidHom u)
    (algebraMap R (Completion R) pi) m (completed_uniformizer R pi hp) hm
  refine ⟨e,?_,hc⟩
  change e X=(algebraMap R (Completion R) (u:R))*algebraMap R (Completion R) pi^(2*m) at he
  simpa only [map_mul,map_pow] using he

end ActualDVRCompletion318
