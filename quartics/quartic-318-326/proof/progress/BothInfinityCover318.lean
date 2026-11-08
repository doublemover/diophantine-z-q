module
public import BothInfinityScheme318
public import FinitePairCover318
public section
noncomputable section
namespace BothInfinityCover318
open BothInfinityAlgebra318 InfinityVietaAlgebra318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R:Type u} [CommRing R]

lemma vanish_at_infinity {T:Type u} [CommRing T] [IsDomain T] (A B:R) (φ:PairRing A B →+* T)
    (hv1:φ (V1 A B)=0) (hv2:φ (V2 A B)=0) : φ (domainElement A B)=1 := by
  have h1 := congrArg φ (raw_first A B)
  have h2 := congrArg φ (raw_second A B)
  simp only [equation,map_sub,map_mul,map_pow,map_zero,hv1,hv2,zero_pow (by decide : 2≠0),
    zero_pow (by decide : 3≠0),mul_zero,sub_zero,zero_sub,neg_eq_zero] at h1 h2
  have hu1 := eq_zero_of_pow_eq_zero h1
  have hu2 := eq_zero_of_pow_eq_zero h2
  simp only [domainElement,C,Q,S,q,s,map_mul,map_add,map_sub,map_pow,map_one,hv1,hv2,hu1,hu2,
    zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),zero_add,add_zero,mul_zero,zero_mul,sub_zero,one_pow,mul_one]

theorem basic_open_cover (A B:R) (p:PrimeSpectrum (PairRing A B)) :
    p ∈ PrimeSpectrum.basicOpen (V1 A B) ∨ p ∈ PrimeSpectrum.basicOpen (V2 A B) ∨
      p ∈ PrimeSpectrum.basicOpen (domainElement A B) := by
  have h := FinitePairCover318.cover_of_domain_tests (T:=PairRing A B)
    (V1 A B) (V2 A B) (domainElement A B) (domainElement A B)
    (fun T _ _ φ hv1 hv2 hd _ => one_ne_zero ((vanish_at_infinity A B φ hv1 hv2).symm.trans hd)) p
  tauto

@[expose] def chartElement (A B:R) : Fin 3 → PairRing A B := ![V1 A B,V2 A B,domainElement A B]
theorem chart_span_top (A B:R) : Ideal.span (Set.range (chartElement A B))=⊤ := by
  apply (PrimeSpectrum.iSup_basicOpen_eq_top_iff (R:=PairRing A B) (f:=chartElement A B)).mp
  apply top_unique
  intro p _
  simp only [TopologicalSpace.Opens.mem_iSup]
  rcases basic_open_cover A B p with h|h|h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩

/-- The two finite-transition opens and the actual both-infinity chart cover the whole input product. -/
@[expose] def productCover (A B:R) : (BothInfinityScheme318.productScheme A B).OpenCover :=
  ((Scheme.affineOpenCoverOfSpanRangeEqTop (R:=CommRingCat.of (PairRing A B))
    (chartElement A B) (chart_span_top A B)).openCover).pushforwardIso
      (pullbackSpecIso R (InfinityChart318.Ring A B) (InfinityChart318.Ring A B)).inv

theorem productCover_regular (A B:R) : (productCover A B).f (2:Fin 3)=BothInfinityScheme318.intoProduct A B := rfl

end BothInfinityCover318
