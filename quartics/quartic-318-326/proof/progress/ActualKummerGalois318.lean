module
public import FourRootGalois318
public section
noncomputable section
namespace ActualKummerGalois318
set_option maxHeartbeats 300000
open QuadraticTower318 KummerTensorField318 FourRootAutomorphisms318 FourRootGalois318
variable {F:Type*} [Field F] [CharZero F] (a:Fin 4→F) [Fact (Independent a)]

/-- The field structure is the proved one on the original tensor of four
quadratic polynomial quotients. -/
instance rawField : Field (Raw a) := (actual_field a).toField

/-- Actual Galoisness of the original four-polynomial coordinate algebra. -/
theorem raw_galois : IsGalois F (Raw a) := by
  letI:=actual_galois a
  exact IsGalois.of_algEquiv (rawEquiv a).symm

theorem raw_automorphism_card : Nat.card (Raw a≃ₐ[F]Raw a)=16 := by
  rw [Nat.card_congr (AlgEquiv.autCongr (rawEquiv a)).toEquiv]
  exact automorphism_card a

/-- Every actual field automorphism is an involution. -/
theorem automorphism_square (e:L4 a≃ₐ[F]L4 a) : e*e=1 := by
  obtain ⟨s,rfl⟩:=signAutomorphism_surjective a e
  change (AlgEquiv.autCongr (rawEquiv a)) (signEquiv a s) *
    (AlgEquiv.autCongr (rawEquiv a)) (signEquiv a s)=1
  rw [←map_mul]
  have hh:signEquiv a s * signEquiv a s=1 := signEquiv_trans_self a s
  rw [hh,map_one]

theorem raw_automorphism_square (e:Raw a≃ₐ[F]Raw a) : e*e=1 := by
  apply (AlgEquiv.autCongr (rawEquiv a)).injective
  rw [map_mul,map_one]
  exact automorphism_square a _

theorem source_raw_galois (c:Fin 4→ℚˣ) :
    IsGalois (RatFunc ℚ) (Raw (SourceKummerField318.parameter c)) := raw_galois _
theorem source_raw_automorphism_card (c:Fin 4→ℚˣ) :
    Nat.card (Raw (SourceKummerField318.parameter c)≃ₐ[RatFunc ℚ]
      Raw (SourceKummerField318.parameter c))=16 := raw_automorphism_card _
theorem source_raw_automorphism_square (c:Fin 4→ℚˣ)
    (e:Raw (SourceKummerField318.parameter c)≃ₐ[RatFunc ℚ]
      Raw (SourceKummerField318.parameter c)) : e*e=1 := raw_automorphism_square _ e
end ActualKummerGalois318
