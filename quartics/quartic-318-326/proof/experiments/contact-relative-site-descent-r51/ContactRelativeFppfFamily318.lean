module
public import ContactRelativeOpenCoverSieve318
public import Mathlib.AlgebraicGeometry.Cover.Sigma
public section
noncomputable section
namespace ContactRelativeFppfFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OriginalRelativeSite318 ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {Y : Scheme} (b : Y ⟶ FieldBase t) (R : Sieve (object b))
  (U : Scheme.Cover.{0} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) Y)
  (hR : ∀ i, R (arrow b (U.f i ≫ b) (U.f i) rfl))

include U hR in
/-- Arbitrary original fppf covering families belong to the genuine
sheaf topology: use their actual full coproduct covering arrow, then its
original open component cover. No finite subfamily is substituted. -/
lemma mem_topology : R ∈ ContactRelativeOpenSieve318.topology t (object b) := by
  let p := Sigma.desc U.f
  let c := p ≫ b
  let a := arrow b c p rfl
  let J := ContactRelativeOpenSieve318.topology t
  have hp := U.sigma.map_prop (default : U.sigma.I₀)
  letI : Flat p := hp.1
  letI : LocallyOfFinitePresentation p := hp.2
  letI : Surjective p := inferInstanceAs (Surjective (Sigma.desc U.f))
  have hsingle : Sieve.generate (Presieve.singleton a) ∈ J (object b) :=
    ContactRelativeFppfSieve318.mem_topology t b c p rfl _
      (Sieve.le_generate _ _ _ (Presieve.singleton_self a))
  have hlocal : R.pullback a ∈ J (object c) := by
    apply ContactRelativeOpenCoverSieve318.mem_topology t c (R.pullback a) (Scheme.sigmaOpenCover U.X)
    intro i
    change R (arrow c (Sigma.ι U.X i ≫ c) (Sigma.ι U.X i) rfl ≫ a)
    apply (sieve_mem_left R _).mpr
    change Sieve.overEquiv (object b) R (Sigma.ι U.X i ≫ p)
    rw [show Sigma.ι U.X i ≫ p = U.f i from Sigma.ι_desc U.f i]
    exact (sieve_mem_left R _).mp (hR i)
  apply J.transitive hsingle R
  rintro Z g ⟨W,k,_,⟨⟩,rfl⟩
  rw [Sieve.pullback_comp]
  exact J.pullback_stable k hlocal
end ContactRelativeFppfFamily318
