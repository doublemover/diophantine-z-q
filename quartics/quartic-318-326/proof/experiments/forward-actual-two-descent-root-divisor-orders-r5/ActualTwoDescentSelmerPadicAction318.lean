module
public import ActualTwoDescentActualPrimaryCharacters318
public section
noncomputable section
namespace ActualTwoDescentSelmerPadicAction318
set_option maxHeartbeats 16000000
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentFullPrimarySelmerTorsion318
open ActualTwoDescentPrimaryPadicScalar318 ActualTwoDescentPrimaryPadicAction318
open ActualTwoDescentPrimaryPadicNaturality318 ActualTwoDescentActualPrimaryCharacters318
open ActualTwoDescentPrueferLevelCoordinates318 ActualTwoDescentPrueferPadicEndomorphisms318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

lemma actual_selmer_primary (n : ℚ) (hn : n ≠ 0) : PrimaryTwo (actualPrimarySelmer n hn) :=
  actual_primary_selmer_two_primary n hn

def actualSelmerPadicEnd (n : ℚ) (hn : n ≠ 0) : ℤ_[2] →+* AddMonoid.End (actualPrimarySelmer n hn) :=
  primaryPadicEndHom (actual_selmer_primary n hn)

lemma actual_selmer_padic_equiv_natural (n : ℚ) (hn : n ≠ 0)
    (e : actualPrimarySelmer n hn ≃+ PrueferAdd) (a : ℤ_[2]) (x : actualPrimarySelmer n hn) :
    e (actualSelmerPadicEnd n hn a x)=padicToPrueferEnd a (e x) :=
  actual_primary_padic_natural (actual_selmer_primary n hn) actual_pruefer_add_primary e.toAddMonoidHom a x

/-- The natural dual action is PRECOMPOSITION by the actual native2-adic
scalar on Selmer, not a module structure transported from a desired answer. -/
def actualCharacterPadicModule (n : ℚ) (hn : n ≠ 0) : Module ℤ_[2] (ActualPrimaryCharacters n hn) where
  smul a f := f.comp (actualSelmerPadicEnd n hn a)
  one_smul f := by ext x; simp
  mul_smul a b f := by
    ext x
    change f (actualSelmerPadicEnd n hn (a*b) x)=f (actualSelmerPadicEnd n hn b (actualSelmerPadicEnd n hn a x))
    rw [mul_comm a b,map_mul]
    rfl
  smul_zero a := by ext x; rfl
  smul_add a f g := by ext x; rfl
  add_smul a b f := by ext x; simp [map_add]
  zero_smul f := by ext x; simp

end ActualTwoDescentSelmerPadicAction318
