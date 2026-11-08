module
public import WeierstrassBaseChange318
public section
noncomputable section
namespace InfinityOriginNeighborhood318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R] (A B:R)

/-- Every prime on the closed infinity boundary also contains its x
coordinate. This is a topological cover statement, not a reducedness
assertion about the boundary scheme. -/
lemma prime_cover (d:InfinityChart318.Ring A B) (hd:IsUnit (InfinityChart318.origin A B d))
    (p:PrimeSpectrum (InfinityChart318.Ring A B)) :
    p ∈ PrimeSpectrum.basicOpen (InfinityChart318.z A B) ∨ p ∈ PrimeSpectrum.basicOpen d := by
  by_cases hz:InfinityChart318.z A B ∈ p.asIdeal
  · right
    letI:=p.isPrime
    let f:InfinityChart318.Ring A B →ₐ[R] (InfinityChart318.Ring A B ⧸ p.asIdeal):=
      Ideal.Quotient.mkₐ R p.asIdeal
    have hfz:f (InfinityChart318.z A B)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hz
    have he:=congrArg f (InfinityChart318.relation A B)
    simp only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes,hfz,
      zero_pow (by decide : (2:ℕ)≠0),zero_pow (by decide : (3:ℕ)≠0),mul_zero,sub_zero,zero_sub] at he
    have hfx:f (InfinityChart318.x A B)=0:=eq_zero_of_pow_eq_zero (neg_eq_zero.mp he)
    have hf:f=(Algebra.ofId R (InfinityChart318.Ring A B ⧸ p.asIdeal)).comp (InfinityChart318.origin A B) := by
      exact InfinityChart318.hom_ext (R:=R) (S:=InfinityChart318.Ring A B ⧸ p.asIdeal) A B
        (f:=f) (g:=(Algebra.ofId R (InfinityChart318.Ring A B ⧸ p.asIdeal)).comp (InfinityChart318.origin A B))
        (by simpa only [AlgHom.comp_apply,InfinityChart318.origin_x,map_zero] using hfx)
        (by simpa only [AlgHom.comp_apply,InfinityChart318.origin_z,map_zero] using hfz)
    have hu:IsUnit (f d) := by
      rw [hf]
      exact hd.map (Algebra.ofId R (InfinityChart318.Ring A B ⧸ p.asIdeal))
    change d ∉ p.asIdeal
    intro hmem
    exact hu.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  · exact Or.inl hz

@[expose] def neighborhood (d:InfinityChart318.Ring A B) : Scheme :=
  Spec (CommRingCat.of (Localization.Away d))
@[expose] def intoChart (d:InfinityChart318.Ring A B) : neighborhood A B d ⟶ InfinitySmooth318.scheme A B :=
  Spec.map (CommRingCat.ofHom (algebraMap (InfinityChart318.Ring A B) (Localization.Away d)))
instance intoChart_open (d:InfinityChart318.Ring A B) : IsOpenImmersion (intoChart A B d) :=
  IsOpenImmersion.of_isLocalization (S:=Localization.Away d) d
@[expose] def intoCurve (d:InfinityChart318.Ring A B) : neighborhood A B d ⟶ WeierstrassGluing318.scheme A B :=
  intoChart A B d ≫ WeierstrassGluing318.infinityChart A B
instance intoCurve_open (d:InfinityChart318.Ring A B) : IsOpenImmersion (intoCurve A B d) := by
  dsimp only [intoCurve]
  infer_instance
lemma chart_range (d:InfinityChart318.Ring A B) :
    Set.range (intoChart A B d)=(PrimeSpectrum.basicOpen d : Set (PrimeSpectrum (InfinityChart318.Ring A B))) :=
  PrimeSpectrum.localization_away_comap_range (Localization.Away d) d

/-- Any actual principal infinity neighborhood containing the whole zero
section, together with the whole finite chart, covers the completed curve. -/
theorem covers (d:InfinityChart318.Ring A B) (hd:IsUnit (InfinityChart318.origin A B d))
    (x:WeierstrassGluing318.scheme A B) :
    x ∈ Set.range (WeierstrassGluing318.finiteChart A B) ∨ x ∈ Set.range (intoCurve A B d) := by
  rcases WeierstrassGluing318.charts_cover A B x with ⟨a,ha⟩|⟨b,hb⟩
  · exact Or.inl ⟨a,ha⟩
  · rcases prime_cover A B d hd b with hz|hd'
    · left
      rw [←WeierstrassBaseChange318.infinity_preimage_finite A B] at hz
      change WeierstrassGluing318.infinityChart A B b ∈ Set.range (WeierstrassGluing318.finiteChart A B) at hz
      exact hb ▸ hz
    · right
      have hm:b ∈ Set.range (intoChart A B d) := by
        rw [chart_range A B d]
        exact hd'
      obtain ⟨c,hc⟩:=hm
      refine ⟨c,?_⟩
      change WeierstrassGluing318.infinityChart A B (intoChart A B d c)=x
      rw [hc,hb]
end InfinityOriginNeighborhood318
