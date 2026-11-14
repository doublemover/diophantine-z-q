module
public import OriginalFiniteDeckGalois318
public section
noncomputable section
namespace OriginalFiniteDeckDegree318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {G F L : Type*} [Group G] [Finite G] [Field F] [Field L] [Algebra F L]
  (ρ : G →* (L ≃ₐ[F] L)) (hfaithful : Function.Injective ρ)

include hfaithful in
/-- When the original extension degree equals the size of its SAME faithful
finite deck action, the actual fixed field is the original base. Neither
Galois structure nor a fixed-function descent identity is assumed. -/
theorem fixed (hdegree : Module.finrank F L = Nat.card G) (x : L)
    (hx : ∀ w : G, ρ w x = x) : ∃ r : F, algebraMap F L r = x := by
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional F L := FiniteDimensional.of_finrank_pos (by
    rw [hdegree]
    exact Nat.card_pos)
  letI := OriginalFiniteDeckGalois318.action ρ
  letI : FaithfulSMul G L := ⟨fun v w h => hfaithful (AlgEquiv.ext h)⟩
  letI : SMulCommClass G F L := ⟨fun w r z => (ρ w).map_smul r z⟩
  let E : IntermediateField F L := FixedPoints.intermediateField G
  have hE : Module.finrank E L = Nat.card G := by
    simpa only [Nat.card_eq_fintype_card] using FixedPoints.finrank_eq_card G L
  have ht := Module.finrank_mul_finrank F E L
  rw [hE, hdegree] at ht
  have hbase : Module.finrank F E = 1 :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card G)
      (ht.trans (one_mul (Nat.card G)).symm)
  have hbot : E = ⊥ := IntermediateField.finrank_eq_one_iff.mp hbase
  have hm : x ∈ E := hx
  rw [hbot] at hm
  exact hm
end OriginalFiniteDeckDegree318
