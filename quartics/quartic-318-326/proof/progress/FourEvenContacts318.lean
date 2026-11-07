module
public import FourUnitCover318
public import EtalePrimeDVR318
public import EvenContactCover318
public section
noncomputable section
namespace FourEvenContacts318
set_option maxHeartbeats 900000
open scoped TensorProduct
open FourUnitCover318
variable {R:Type*} [CommRing R] (u:Fin 4→Rˣ) (pi:R) (m:Fin 4→ℕ)

@[expose] def contactRoot (i:Fin 4):Cover u:=
  generator u i*algebraMap R (Cover u) pi^(m i)

theorem contactRoot_square (i:Fin 4) :
    contactRoot u pi m i^2=algebraMap R (Cover u) ((u i:R)*pi^(2*m i)) := by
  rw [contactRoot,mul_pow,generator_square,map_mul,map_pow,←pow_mul]
  congr 2
  omega

/-- Every simultaneous field-valued four-root tuple factors through the actual
rank-sixteen etale cover. No root choices or splitting premise is supplied. -/
theorem all_field_points (L:Type*) [Field L] [Algebra R L]
    (hpi:algebraMap R L pi≠0) (y:Fin 4→L)
    (hy:∀i,y i^2=algebraMap R L ((u i:R)*pi^(2*m i))) :
    ∃f:Cover u→ₐ[R]L,∀i,f (contactRoot u pi m i)=y i := by
  choose f hf using fun i:Fin 4=>
    EvenContactEtale318.factor_even_contact_point (u i) pi (m i) L hpi (y i) (hy i)
  refine ⟨liftFour u f,?_⟩
  intro i
  rw [contactRoot,map_mul,map_pow,AlgHom.commutes,liftFour_generator]
  simpa only [map_mul,map_pow,AlgHom.commutes] using hf i

open CategoryTheory AlgebraicGeometry
@[expose] def coverScheme:Scheme:=Spec (CommRingCat.of (Cover u))
@[expose] def coverMap:coverScheme u⟶Spec (CommRingCat.of R):=
  Spec.map (CommRingCat.ofHom (algebraMap R (Cover u)))

/-- The simultaneous root cover is an actual finite etale surjective scheme
map over the original base, and may have split components. -/
theorem finite_etale_surjective [Nontrivial R] (h2:IsUnit (2:R)) :
    IsFinite (coverMap u) ∧ Etale (coverMap u) ∧ Surjective (coverMap u) := by
  have hd:=finite_free_etale u h2
  have hf:=faithfullyFlat u
  refine ⟨(IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hd.1),
    (HasRingHomProperty.Spec_iff (P:=@Etale)).mpr (RingHom.etale_algebraMap.mpr hd.2.2),?_⟩
  exact ((flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hf)).2

end FourEvenContacts318
