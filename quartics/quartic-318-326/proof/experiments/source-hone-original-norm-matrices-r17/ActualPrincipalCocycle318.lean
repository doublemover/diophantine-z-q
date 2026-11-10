module
public import ActualPrincipalSections318

public section
noncomputable section
namespace ActualPrincipalCocycle318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PrincipalFractionClearing318 ActualPrincipalSections318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : CommRingCat.{0}} [IsDomain R]
variable {ι : Type*} [Fintype ι] (f : ι → R) (hf : ∀ i, f i ≠ 0)

abbrev tripleLeft (i j k : ι) : PrimeSpectrum.basicOpen ((f i*f j)*f k) ≤
    PrimeSpectrum.basicOpen (f i*f j) := PrimeSpectrum.basicOpen_mul_le_left _ _
abbrev tripleRight (i j k : ι) : PrimeSpectrum.basicOpen ((f i*f j)*f k) ≤
    PrimeSpectrum.basicOpen (f j*f k) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf inf_le_right le_rfl
abbrev tripleOuter (i j k : ι) : PrimeSpectrum.basicOpen ((f i*f j)*f k) ≤
    PrimeSpectrum.basicOpen (f i*f k) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf inf_le_left le_rfl

/-- The ordinary additive cocycle equation on the actual triple-overlap section ring. -/
@[expose] def Cocycle (c : ∀ i j, Sections (f i*f j)) : Prop :=
  ∀ i j k, restrict (tripleLeft f i j k) (c i j) +
    restrict (tripleRight f i j k) (c j k) = restrict (tripleOuter f i j k) (c i k)

include hf

/-- Every actual additive structure-sheaf cocycle on a finite nonempty-principal-open
cover of Spec of a domain splits by original structure-sheaf sections. -/
theorem split (hcover : (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤)
    (c : ∀ i j, Sections (f i*f j)) (hc : Cocycle f c) :
    ∃ b : ∀ i, Sections (f i), ∀ i j,
      c i j = restrict (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (b i) -
        restrict (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (b j) := by
  let K := FractionRing R
  let z (i j : ι) : K := embed (f i*f j) (mul_ne_zero (hf i) (hf j)) (c i j)
  have hz : ∀ i j, z i j ∈ away (f i*f j) (mul_ne_zero (hf i) (hf j)) := by
    intro i j
    rw [← range_embed]
    exact ⟨c i j,rfl⟩
  have hzc : ∀ i j k, z i j+z j k=z i k := by
    intro i j k
    have h := congrArg (embed (K:=K) ((f i*f j)*f k)
      (mul_ne_zero (mul_ne_zero (hf i) (hf j)) (hf k))) (hc i j k)
    simpa only [map_add, embed_restrict (mul_ne_zero (hf i) (hf j)),
      embed_restrict (mul_ne_zero (hf j) (hf k)),
      embed_restrict (mul_ne_zero (hf i) (hf k))] using h
  obtain ⟨b,hb,he⟩ := PrincipalCocycleSplit318.split_of_principal_cover f hf hcover z hz hzc
  choose s hs using fun i => exists_section (f i) (hf i) (b i) (hb i)
  refine ⟨s,fun i j => ?_⟩
  apply embed_injective (K:=K) (f i*f j) (mul_ne_zero (hf i) (hf j))
  rw [map_sub,embed_restrict (hf i),embed_restrict (hf j),hs,hs]
  exact he i j

end ActualPrincipalCocycle318
