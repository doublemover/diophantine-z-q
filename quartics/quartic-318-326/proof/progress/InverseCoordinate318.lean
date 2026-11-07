module
public import LocalDeck318
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open Filter Topology
open scoped MatrixGroups
namespace InverseCoordinate318
set_option maxHeartbeats 0

/-- A genuine local inverse of the actual quotient projection has holomorphic
coordinate transitions with the upper-half-plane coordinate. -/
theorem analytic_local_inverse (N:ℕ) (hN:5≤N)
    (e:OpenPartialHomeomorph (Base (image N)) UpperHalfPlane)
    (he:(e.symm:UpperHalfPlane→Base (image N))=quotientMap N)
    (z:UpperHalfPlane) (hz:quotientMap N z∈e.source) :
    AnalyticAt ℂ (fun w:ℂ => (e (quotientMap N (ofComplex w)):ℂ)) (z:ℂ) := by
  have hf:ContinuousAt ofComplex (z:ℂ):=(contMDiffAt_ofComplex (n:=0) z.im_pos).continuousAt
  have hp:ContinuousAt (fun w:ℂ=>quotientMap N (ofComplex w)) (z:ℂ) :=
    (quotient_covering N hN).isCoveringMap.continuous.continuousAt.comp hf
  have hz':quotientMap N (ofComplex (z:ℂ))∈e.source := by simpa using hz
  have hg:ContinuousAt (fun w:ℂ=>e (quotientMap N (ofComplex w))) (z:ℂ) :=
    (e.continuousAt hz').comp (f:=fun w:ℂ=>quotientMap N (ofComplex w)) hp
  have hev:∀ᶠw in 𝓝 (z:ℂ),quotientMap N (ofComplex w)∈e.source :=
    hp.eventually (e.open_source.mem_nhds hz')
  have hsame:∀ᶠw in 𝓝 (z:ℂ),quotientMap N (ofComplex w)=
      quotientMap N (e (quotientMap N (ofComplex w))) := by
    filter_upwards [hev] with w hw
    have hh:=e.left_inv hw
    rw [he] at hh
    exact hh.symm
  obtain ⟨gamma,hgamma⟩:=LocalDeck318.locally_deck_eq N hN ofComplex
    (fun w:ℂ=>e (quotientMap N (ofComplex w))) (z:ℂ) hf hg hsame
  have ha:=analyticAt_smul (g:=((gamma:DerivativeCocycle318.G):GL (Fin 2) ℝ))
    (gamma:DerivativeCocycle318.G).property z
  apply ha.congr
  filter_upwards [hgamma] with w hw
  exact congrArg UpperHalfPlane.coe hw

/-- The particular local inverses used in the actual quotient atlas satisfy
this holomorphic transition conclusion without any inverse-regularity input. -/
theorem analytic_localInverseAt (N:ℕ) (hN:5≤N) (a z:UpperHalfPlane)
    (hz:quotientMap N z∈((quotient_localHomeomorph N hN).localInverseAt a).source) :
    AnalyticAt ℂ (fun w:ℂ =>
      ((quotient_localHomeomorph N hN).localInverseAt a (quotientMap N (ofComplex w)):ℂ)) (z:ℂ) :=
  analytic_local_inverse N hN _ ((quotient_localHomeomorph N hN).localInverseAt_symm a) z hz
end InverseCoordinate318
