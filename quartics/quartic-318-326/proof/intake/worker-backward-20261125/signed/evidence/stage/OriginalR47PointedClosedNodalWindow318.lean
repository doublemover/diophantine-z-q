module
public import OriginalR47PointedCommonCentre318
public import OriginalR47CentralSurvivorClosed318
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public section
noncomputable section

namespace OriginalR47PointedClosedNodalWindow318

open AlgebraicGeometry CategoryTheory Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {C : CommRingCat.{u}} {U X S : Scheme.{u}}
variable (g : U ⟶ Spec C) [LocallyOfFiniteType g] [FormallyUnramified g]
variable (e : U ⟶ X) [LocallyOfFiniteType e]
variable (s : X ⟶ S) [LocallyOfFiniteType s] (k : Spec C ⟶ S)

/-- Close the same old point using one genuine affine open of its
pointed site. The split residue may be different from the old residue;
only the exact two arrows and closedness of the two actual bases are
used. No global quasi-finite/étale package or field equality is needed. -/
theorem transport (H : e ≫ s = g ≫ k) (w : U) (z : PrimeSpectrum C)
    [z.asIdeal.IsMaximal] (Hw : g w = z) (hk : IsClosed ({k z} : Set S)) :
    IsClosed ({e w} : Set X) := by
  let W := U.affineOpenCover
  obtain ⟨i,a,ha⟩ := W.openCover.exists_eq w
  let B := W.X i
  let j : Spec B ⟶ U := W.f i
  let β : C ⟶ B := Spec.preimage (j ≫ g)
  let b : Spec B ⟶ Spec C := Spec.map β
  have hb : b = j ≫ g := Spec.map_preimage _
  have ha' : j a = w := ha
  letI : IsOpenImmersion j := W.map_prop i
  letI : LocallyOfFiniteType b :=
    hb.symm ▸ (inferInstance : LocallyOfFiniteType (j ≫ g))
  letI : FormallyUnramified b :=
    hb.symm ▸ (MorphismProperty.comp_mem (@FormallyUnramified) j g
      inferInstance inferInstance)
  letI : Algebra C B := β.hom.toAlgebra
  letI : Algebra.FiniteType C B := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P:=@LocallyOfFiniteType)).mp
      (inferInstance : LocallyOfFiniteType b))
  letI : Algebra.FormallyUnramified C B := RingHom.formallyUnramified_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P:=@FormallyUnramified)).mp
      (inferInstance : FormallyUnramified b))
  have hSupport : ((b : Spec B → Spec C) ⁻¹' ({z} : Set (Spec C))) =
      PrimeSpectrum.zeroLocus (((z.asIdeal.map (algebraMap C B)) : Ideal B) : Set B) := by
    ext x
    change b x ∈ ({z} : Set (Spec C)) ↔ _
    rw [Set.mem_singleton_iff,PrimeSpectrum.mem_zeroLocus]
    change b x = z ↔ Ideal.map β.hom z.asIdeal ≤ x.asIdeal
    rw [Ideal.map_le_iff_le_comap]
    change b x = z ↔ z.asIdeal ≤ (b x).asIdeal
    exact ⟨fun h => h.symm ▸ le_rfl,
      fun h => PrimeSpectrum.ext ((‹z.asIdeal.IsMaximal›.eq_of_le (b x).isPrime.ne_top h).symm)⟩
  have hD : IsDiscrete ((b : Spec B → Spec C) ⁻¹' ({z} : Set (Spec C))) := by
    rw [hSupport]
    exact OriginalR47PointedCommonCentre318.discrete_closed_fibre z.asIdeal
  letI : DiscreteTopology ((b : Spec B → Spec C) ⁻¹' ({z} : Set (Spec C))) :=
    isDiscrete_iff_discreteTopology.mp hD
  letI : DiscreteTopology (b.fiber z) := (b.fiberHomeo z).isEmbedding.discreteTopology
  have hba : b a = z := by rw [hb,Scheme.Hom.comp_apply,ha',Hw]
  let v := (b.fiberHomeo z).symm ⟨a,hba⟩
  have hv : b.fiberι z v = a := b.fiberι_fiberHomeo_symm z ⟨a,hba⟩
  have hcomp : (j ≫ e) ≫ s = b ≫ k := by rw [hb,Category.assoc,H,Category.assoc]
  have he := OriginalR47CentralSurvivorClosed318.closed_in_old_chart b s
    (j ≫ e) k hcomp z (PrimeSpectrum.isClosed_singleton_iff_isMaximal z |>.mpr inferInstance)
    hk v isClosed_discrete
  simpa only [Scheme.Hom.comp_apply,hv,ha'] using he

end OriginalR47PointedClosedNodalWindow318

#print axioms OriginalR47PointedClosedNodalWindow318.transport
