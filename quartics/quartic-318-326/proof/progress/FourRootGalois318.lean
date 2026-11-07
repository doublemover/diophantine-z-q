module
public import FourRootAutomorphisms318
public import Mathlib.FieldTheory.Galois.Basic
public section
noncomputable section
namespace FourRootGalois318
set_option maxHeartbeats 200000
open QuadraticTower318 KummerTensorField318 FourRootAutomorphisms318
variable {F:Type*} [Field F] [CharZero F] (a:Fin 4→F) [Fact (Independent a)]

/-- The sixteen concrete sign maps, transported to the actual iterated field. -/
@[expose] def signAutomorphism (s:Fin 4→Bool) : L4 a≃ₐ[F]L4 a :=
  (AlgEquiv.autCongr (rawEquiv a)) (signEquiv a s)

theorem signAutomorphism_injective : Function.Injective (signAutomorphism a) :=
  (AlgEquiv.autCongr (rawEquiv a)).injective.comp (signEquiv_injective a)

instance finiteDimensional : FiniteDimensional F (L4 a) :=
  Module.finite_of_finrank_pos (by rw [degree_sixteen]; decide)

/-- The automorphism cardinal is derived from sixteen distinct actual maps
and the actual field degree, rather than assumed as Kummer data. -/
theorem automorphism_card : Nat.card (L4 a≃ₐ[F]L4 a)=16 := by
  have lo:16≤Nat.card (L4 a≃ₐ[F]L4 a) := by
    have hh:=Nat.card_le_card_of_injective (signAutomorphism a) (signAutomorphism_injective a)
    simpa using hh
  have hi:Nat.card (L4 a≃ₐ[F]L4 a)≤16 := by
    simpa only [Nat.card_eq_fintype_card,degree_sixteen] using (AlgEquiv.card_le (F:=F) (K:=L4 a))
  exact Nat.le_antisymm hi lo

/-- Actual Galoisness follows from the proved automorphism/degree equality. -/
theorem actual_galois : IsGalois F (L4 a) := by
  apply IsGalois.of_card_aut_eq_finrank
  rw [automorphism_card,degree_sixteen]

/-- Every field automorphism is one of the sixteen actual root-sign maps. -/
theorem signAutomorphism_surjective : Function.Surjective (signAutomorphism a) := by
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ?_).2
  exact ⟨signAutomorphism_injective a,by simpa using (automorphism_card a).symm⟩

theorem source_galois (c:Fin 4→ℚˣ) :
    IsGalois (RatFunc ℚ) (L4 (SourceKummerField318.parameter c)) := actual_galois _
theorem source_automorphism_card (c:Fin 4→ℚˣ) :
    Nat.card (L4 (SourceKummerField318.parameter c)≃ₐ[RatFunc ℚ]
      L4 (SourceKummerField318.parameter c))=16 := automorphism_card _
end FourRootGalois318
