module
public import InfinityOverlapLocalization318
public section
noncomputable section
namespace SourceInfinityOverlap318
open Polynomial InfinityOverlapLocalization318
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

theorem away_of_square {A B:Type*} [CommRing A] [CommRing B] [Algebra A B]
    (x:A) [IsLocalization.Away (x^2) B] : IsLocalization.Away x B:=by
  apply IsLocalization.Away.mk
  · have h:=IsLocalization.Away.algebraMap_isUnit (S:=B) (x^2)
    simpa only [map_pow,isUnit_pow_iff (by decide : (2:ℕ)≠0)] using h
  · intro z
    obtain ⟨n,a,ha⟩:=IsLocalization.Away.surj (x^2) z
    exact ⟨2*n,a,by simpa only [map_pow,pow_mul] using ha⟩
  · intro a b h
    obtain ⟨n,hn⟩:=IsLocalization.Away.exists_of_eq (x^2) h
    exact ⟨2*n,by simpa only [pow_mul] using hn⟩

variable (c:Fin 4→ℚˣ)
local instance sourceAlgebra : Algebra (Infinity c) (Source c):=(toOpen c).toAlgebra

theorem whole_localization : IsLocalization.Away (coordinate c) (Source c):=by
  letI:=reciprocal_isLocalization c
  letI:IsLocalization.Away
      (algebraMap ℚ (Infinity c) (↑((c 0)⁻¹):ℚ)*(coordinate c)^2) (Source c):=by
    rw [←reciprocal_coordinate]
    infer_instance
  letI:IsLocalization.Away ((coordinate c)^2) (Source c):=
    IsLocalization.Away.of_associated (associated_unit_mul_left _ _
      (((c 0)⁻¹).isUnit.map (algebraMap ℚ (Infinity c))))
  exact away_of_square (coordinate c)

/-- The full original unbranched order is the actual localization of the
whole infinity neighborhood, not merely a subring of an isomorphic field. -/
@[expose] def overlapEquiv : Localization.Away (coordinate c)≃ₐ[Infinity c]Source c:=by
  letI:=whole_localization c
  exact IsLocalization.algEquiv (Submonoid.powers (coordinate c)) _ _

theorem overlapEquiv_on_infinity (x:Infinity c):
    overlapEquiv c (algebraMap (Infinity c) (Localization.Away (coordinate c)) x)=toOpen c x:=
  (overlapEquiv c).commutes x

theorem overlapEquiv_embedding (x:Localization.Away (coordinate c)):
    SourceOpenFractionField318.openEmbedding c (overlapEquiv c x)=
      IsLocalization.Away.lift (g:=InfinityOpenFractionField318.openEmbedding c) (coordinate c)
        (by
          rw [show InfinityOpenFractionField318.openEmbedding c (coordinate c)=
            InfinityFieldCoordinates318.u c by
              simpa only [coordinate,Polynomial.aeval_X] using
                ReciprocalInfinityNormalization318.openEmbedding_on_polynomial c X]
          letI:Field (InfinityFieldCoordinates318.L c):=(KummerTensorField318.source_raw_field c).toField
          exact IsUnit.mk0 _ (InfinityFieldCoordinates318.u_ne_zero c)) x:=by
  letI:Field (InfinityFieldCoordinates318.L c):=(KummerTensorField318.source_raw_field c).toField
  have h:(SourceOpenFractionField318.openEmbedding c).comp (overlapEquiv c).toRingHom=
      IsLocalization.Away.lift (g:=InfinityOpenFractionField318.openEmbedding c) (coordinate c)
        (by
          rw [show InfinityOpenFractionField318.openEmbedding c (coordinate c)=
            InfinityFieldCoordinates318.u c by
              simpa only [coordinate,Polynomial.aeval_X] using
                ReciprocalInfinityNormalization318.openEmbedding_on_polynomial c X]
          exact IsUnit.mk0 _ (InfinityFieldCoordinates318.u_ne_zero c)):=by
    apply IsLocalization.ringHom_ext (Submonoid.powers (coordinate c))
    apply RingHom.ext
    intro y
    simp only [RingHom.comp_apply,IsLocalization.Away.lift_eq]
    change SourceOpenFractionField318.openEmbedding c
      (overlapEquiv c (algebraMap (Infinity c) (Localization.Away (coordinate c)) y))=_
    rw [overlapEquiv_on_infinity]
    exact toOpen_embedding c y
  exact RingHom.congr_fun h x

@[expose] def t : Source c:=
  algebraMap ContactKummerOrder318.OpenBase (Source c) ContactReciprocalBase318.t
@[expose] def u : Source c:=toOpen c (coordinate c)
local instance rawField : Field (InfinityFieldCoordinates318.L c):=(KummerTensorField318.source_raw_field c).toField

theorem t_embedding : SourceOpenFractionField318.openEmbedding c (t c)=InfinityFieldCoordinates318.t c:=by
  rw [t,ContactReciprocalBase318.t,SourceOpenFractionField318.openEmbedding_on_polynomial,RatFunc.algebraMap_X]
  rfl

theorem u_embedding : SourceOpenFractionField318.openEmbedding c (u c)=InfinityFieldCoordinates318.u c:=by
  rw [u,toOpen_embedding]
  simpa only [coordinate,Polynomial.aeval_X] using
    ReciprocalInfinityNormalization318.openEmbedding_on_polynomial c X

/-- Literal equality in the entire overlap ring, under u=c₀/y₀ and t=c₀/u². -/
theorem coordinate_relation : (u c)^2*t c=algebraMap ℚ (Source c) (c 0:ℚ):=by
  apply SourceOpenFractionField318.openEmbedding_injective c
  simp only [map_mul,map_pow,u_embedding,t_embedding,RingHom.map_rat_algebraMap]
  rw [InfinityFieldCoordinates318.u_square,div_mul_cancel₀ _ (InfinityFieldCoordinates318.t_ne_zero c)]
  rfl

theorem u_unit : IsUnit (u c):=by
  letI:=whole_localization c
  exact IsLocalization.Away.algebraMap_isUnit (S:=Source c) (coordinate c)

theorem t_unit : IsUnit (t c):=by
  simpa only [ContactReciprocalBase318.tUnit_coe,t] using
    ContactReciprocalBase318.tUnit.isUnit.map (algebraMap ContactKummerOrder318.OpenBase (Source c))
end SourceInfinityOverlap318
