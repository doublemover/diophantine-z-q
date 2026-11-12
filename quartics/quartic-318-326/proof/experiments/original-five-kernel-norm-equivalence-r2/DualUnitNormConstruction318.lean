module
public import DualUnitFactorization318
public section
noncomputable section
namespace DualUnitNormConstruction318
open SquareZeroUnit318 DualUnitFactorization318
universe u v w t
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (N : Sˣ →* Rˣ) (T : S →+ R)
/-- The unique multiplicative extension fixed by coefficient norm and
infinitesimal trace. Agreement with determinant norm is proved separately. -/
@[expose] def norm : (Dual S)ˣ →* (Dual R)ˣ where
  toFun z := lift R (N (coefficient S z)) * unit R (T (log S z))
  map_one' := by simp
  map_mul' z w := by
    simp only [map_mul, log_mul, map_add, unit_add]
    ac_rfl
lemma coefficient_value (a : Sˣ) : norm N T (lift S a) = lift R (N a) := by
  simp [norm]
lemma infinitesimal_value (a : S) : norm N T (unit S a) = unit R (T a) := by
  simp [norm]
lemma reduction (z : (Dual S)ˣ) : coefficient R (norm N T z) = N (coefficient S z) := by
  change coefficient R (lift R _ * unit R _) = _
  rw [map_mul, coefficient_lift, coefficient_unit, mul_one]
lemma unique (F : (Dual S)ˣ →* (Dual R)ˣ)
    (hN : ∀ a, F (lift S a) = lift R (N a))
    (hT : ∀ a, F (unit S a) = unit R (T a)) : F = norm N T := by
  ext z
  calc
    F z = F (lift S (coefficient S z) * unit S (log S z)) :=
      congrArg F (factorization S z).symm
    _ = norm N T z := by
      rw [map_mul, hN, hT]
      all_goals rfl
variable {R' : Type w} {S' : Type t} [CommRing R'] [CommRing S']
    (N' : S'ˣ →* R'ˣ) (T' : S' →+ R') (r : R →+* R') (s : S →+* S')
    (hN : ∀ a, Units.map r.toMonoidHom (N a) = N' (Units.map s.toMonoidHom a))
    (hT : ∀ a, r (T a) = T' (s a))
include hN hT in
lemma naturality (z : (Dual S)ˣ) :
    Units.map (map R r).toMonoidHom (norm N T z) =
      norm N' T' (Units.map (map S s).toMonoidHom z) := by
  change Units.map (map R r).toMonoidHom (lift R (N (coefficient S z)) * unit R (T (log S z))) =
    lift R' (N' (coefficient S' (Units.map (map S s).toMonoidHom z))) *
      unit R' (T' (log S' (Units.map (map S s).toMonoidHom z)))
  rw [map_mul, lift_natural, map_unit, coefficient_natural, log_natural, hN, hT]
end DualUnitNormConstruction318
