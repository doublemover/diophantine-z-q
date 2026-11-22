module
public import ActualGaussianWeberOriginJet318
public import ActualGaussianWeberGaussianScalarCore318
public section
noncomputable section

namespace ActualGaussianWeberStationaryScalar318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberValuedKernelChart318
open ActualGaussianWeberQuarterTurn318 ActualGaussianWeberGaussianScalarSpecialization318
open ActualGaussianWeberOriginJet318

variable {F : Type*} [Field F] [DecidableEq F] (V : ValuationSubring F)
variable (hF : (2:F)≠0) (h2 : (2:ResidueField V)≠0) (t : V)

@[expose] def turnOnOrigin (ht : t∈maximalIdeal V)
    (i : V) (hi : i^2= -1) (P : scaledOrigin V hF h2 t ht) :
    scaledOrigin V hF h2 t ht :=
  ⟨turn hF (V.subtype i) (chosen_square_generic V i hi) (P:WP F),
    ⟨turnWitness V hF h2 t i hi (chosen V hF h2 t ht P)⟩⟩

theorem jet_turn (ht : t∈maximalIdeal V) (ht0 : t≠0)
    (i : V) (hi : i^2= -1) (P : scaledOrigin V hF h2 t ht) :
    jet V hF h2 t ht ht0 (turnOnOrigin V hF h2 t ht i hi P)=
      residue V i*jet V hF h2 t ht ht0 P := by
  let A := turnWitness V hF h2 t i hi (chosen V hF h2 t ht P)
  rw [jet_eq_of_witness V hF h2 t ht ht0 _ A]
  change residue V (i*(chosen V hF h2 t ht P).c)=_
  rw [map_mul] <;> rfl

/-- For the selected Gaussian prime the same-place scalar has zero
linear coefficient on the actual origin kernel at t-scale. This
conclusion uses the literal square root i and the vanishing of a+b i
at this residue place; substituting its conjugate is not licensed. -/
theorem scalar_first_jet_zero (ht : t∈maximalIdeal V) (ht0 : t≠0)
    (i : V) (hi : i^2= -1) (a b : ℤ)
    (hSelected : (a:ResidueField V)+(b:ResidueField V)*residue V i=0)
    (P : scaledOrigin V hF h2 t ht) :
    jet V hF h2 t ht ht0 (a • P+b • turnOnOrigin V hF h2 t ht i hi P)=0 := by
  rw [map_add,map_zsmul,map_zsmul,jet_turn V hF h2 t ht ht0 i hi]
  let c := jet V hF h2 t ht ht0 P
  change a • c+b • (residue V i*c)=0
  calc
    _ = ((a:ResidueField V)+(b:ResidueField V)*residue V i)*c := by
      simp only [zsmul_eq_mul]
      ring
    _ = _ := by rw [hSelected,zero_mul]

/-- In the genuine formal parameter case, where t generates the
maximal ideal, the actual scalar's t-coordinate is divisible by t².
This is a native stationary-arc assertion, not a degree assertion. -/
theorem selected_scalar_stationary (ht : t∈maximalIdeal V) (ht0 : t≠0)
    (hPrincipal : maximalIdeal V=Ideal.span {t}) (i : V) (hi : i^2= -1)
    (a b : ℤ) (hSelected : (a:ResidueField V)+(b:ResidueField V)*residue V i=0)
    (P : scaledOrigin V hF h2 t ht) :
    let R := gaussian hF (V.subtype i) (chosen_square_generic V i hi) a b (P:WP F)
    specialize V h2 R=Point.zero ∧ ∃ c : V, tCoord R=V.subtype (t^2*c) := by
  let Q : scaledOrigin V hF h2 t ht := a • P+b • turnOnOrigin V hF h2 t ht i hi P
  let D := chosen V hF h2 t ht Q
  have hQ : residue V D.c=0 := scalar_first_jet_zero V hF h2 t ht ht0 i hi a b hSelected P
  have hc : D.c ∈ maximalIdeal V := (residue_eq_zero_iff D.c).mp hQ
  rw [hPrincipal] at hc
  obtain ⟨u,hu⟩ := Ideal.mem_span_singleton.mp hc
  have hQEq : (Q:WP F)=gaussian hF (V.subtype i) (chosen_square_generic V i hi) a b (P:WP F) := by
    change (scaledOrigin V hF h2 t ht).subtype
      (a • P+b • turnOnOrigin V hF h2 t ht i hi P)=_
    rw [map_add,map_zsmul,map_zsmul] <;> rfl
  dsimp only
  rw [←hQEq]
  refine ⟨D.origin,u,?_⟩
  rw [D.exact_t,hu]
  congr 1 <;> ring

end ActualGaussianWeberStationaryScalar318
