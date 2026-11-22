module
public import ActualGaussianWeberOriginalFieldFoundation318
public import ActualGaussianWeberStockCoordinateHom318
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Closure
public section
noncomputable section

namespace ActualGaussianWeberNamedFullFieldGalois318

open IntermediateField
open WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberSelectedGaussianPrime318
open ActualGaussianWeberFullTorsionInertia318 ActualGaussianWeberFullCoordinateField318
open ActualGaussianWeberAlgebraicClosureTorsion318

attribute [local instance] Classical.decEq

private theorem named_closure_two_ne : (2:Ω)≠0 := by
  intro h
  have e := congrArg chosenClosureEmbedding h
  exact (by norm_num : (2:ℂ)≠0) (by simpa only [map_ofNat,map_zero] using e)

/-- The literal ambient generator family of the original full
coordinate field is stable under every Base-embedding of the
same closure into itself. This needs no arithmetic class action. -/
theorem named_coordinates_map_stable (M : ℕ) (g : Ω→ₐ[Base]Ω) :
    Set.MapsTo g (torsionCoordinates Ω M) (torsionCoordinates Ω M) := by
  rintro z ⟨x,y,hn,hT,hz⟩
  let f := g.toRingHom
  have h := congrArg (coordinateHom f named_closure_two_ne) hT
  rw [map_nsmul,map_zero] at h
  change M • onCurvePoint f named_closure_two_ne (Point.some x y hn)=0 at h
  rw [point_some f named_closure_two_ne hn] at h
  refine ⟨g x,g y,mapped_nonsingular f named_closure_two_ne hn,h,?_⟩
  rcases hz with rfl|rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The genuine original full coordinate adjoin is Galois over the
same Gaussian fraction field. Normality follows from all conjugate
torsion coordinates staying in the defining generator set, and
separability from characteristic zero. No degree or finite-lattice
premise is needed for this result itself. -/
theorem old_fullField_isGalois (M : ℕ) : IsGalois Base (fullField Ω M) := by
  letI : CharZero Base := ⟨fun a b h =>
    Nat.cast_injective (R:=ℂ) (by
      simpa only [map_natCast] using congrArg complexEmbedding h)⟩
  letI : IsGalois Base Ω := ⟨⟩
  refine ⟨Algebra.isSeparable_tower_bot_of_isSeparable Base (fullField Ω M) Ω,?_⟩
  apply IntermediateField.normal_iff_forall_map_le.mpr
  intro g
  apply IntermediateField.map_le_iff_le_comap.mpr
  apply IntermediateField.adjoin_le_iff.mpr
  intro z hz
  change g z∈fullField Ω M
  exact IntermediateField.subset_adjoin Base _ (named_coordinates_map_stable M g hz)

private theorem coordinate_reflects_zero {K : Type*} [Field K] (f : K→+*Ω) (P : WP K)
    (h : coordinateHom f named_closure_two_ne P=0) : P=0 := by
  cases P with
  | zero => rfl
  | some x y hn =>
    change onCurvePoint f named_closure_two_ne (Point.some x y hn)=(0:WP Ω) at h
    rw [point_some f named_closure_two_ne hn] at h
    exact False.elim (Point.some_ne_zero _ h)

/-- Every original affine torsion point over Ω descends to the
same fullField, with both coordinates given by membership in the
original generator set, not by a second choice of embedding. -/
theorem original_affine_torsion_lifts_to_fullField
    (M : ℕ) (x y : Ω) (hn : (curve Ω).toAffine.Nonsingular x y)
    (hT : M • Point.some x y hn=0) :
    ∃ (a b : fullField Ω M), ∃ hn' : (curve (fullField Ω M)).toAffine.Nonsingular a b,
      M • Point.some a b hn'=0 ∧ (a:Ω)=x ∧ (b:Ω)=y := by
  let D := fullField Ω M
  obtain ⟨hx,hy⟩ := ActualGaussianWeberOriginalFieldFoundation318.affine_torsion_coordinates_mem_fullField
    M x y hn hT
  let a : D := ⟨x,hx⟩
  let b : D := ⟨y,hy⟩
  let f := algebraMap D Ω
  have h₂ : (2:D)≠0 := by
    intro e
    exact named_closure_two_ne (by simpa only [map_ofNat,map_zero] using congrArg f e)
  have hE : b^2=a^3-a := by
    apply f.injective
    rw [map_pow,map_sub,map_pow]
    exact (literal_equation x y).mp hn.1
  let hd := nonsing_of_equation h₂ hE
  let H := coordinateHom f named_closure_two_ne
  have hPt : H (Point.some a b hd)=Point.some x y hn := by
    change onCurvePoint f named_closure_two_ne (Point.some a b hd)=_
    rw [point_some f named_closure_two_ne hd] <;> exact some_congr rfl rfl
  refine ⟨a,b,hd,?_,rfl,rfl⟩
  apply coordinate_reflects_zero f
  change H (M • Point.some a b hd)=0
  rw [map_nsmul,hPt,hT]

/-- The internal M-torsion coordinates generate this actual full
field; this is the faithfulness input for an automorphism acting on
its stock torsion points. It is not an adjoin equality on an
isomorphic comparison field. -/
theorem old_fullField_internally_generated (M : ℕ) :
    IntermediateField.adjoin Base (torsionCoordinates (fullField Ω M) M)=⊤ := by
  let D := fullField Ω M
  let f : D→ₐ[Base]Ω := D.val
  have hImage : f '' torsionCoordinates D M=torsionCoordinates Ω M := by
    ext z
    constructor
    · rintro ⟨u,⟨x,y,hn,hT,hu⟩,rfl⟩
      have h := congrArg (coordinateHom f.toRingHom named_closure_two_ne) hT
      rw [map_nsmul,map_zero] at h
      change M • onCurvePoint f.toRingHom named_closure_two_ne (Point.some x y hn)=0 at h
      rw [point_some f.toRingHom named_closure_two_ne hn] at h
      exact ⟨f x,f y,mapped_nonsingular f.toRingHom named_closure_two_ne hn,h,
        hu.imp (congrArg f) (congrArg f)⟩
    · rintro ⟨x,y,hn,hT,hz⟩
      obtain ⟨a,b,h,hT',ha,hb⟩ := original_affine_torsion_lifts_to_fullField M x y hn hT
      rcases hz with rfl|rfl
      · exact ⟨a,⟨a,b,h,hT',Or.inl rfl⟩,ha⟩
      · exact ⟨b,⟨a,b,h,hT',Or.inr rfl⟩,hb⟩
  let J := IntermediateField.adjoin Base (torsionCoordinates D M)
  have hMap : J.map f=D := by
    change (IntermediateField.adjoin Base (torsionCoordinates D M)).map f=_
    rw [IntermediateField.adjoin_map,hImage] <;> rfl
  change J=⊤
  apply le_antisymm le_top
  intro z _
  have hz : (z:Ω)∈J.map f := hMap.symm ▸ z.property
  obtain ⟨u,hu,e⟩ := (IntermediateField.mem_map (S:=J)).mp hz
  exact (f.injective e) ▸ hu

end ActualGaussianWeberNamedFullFieldGalois318
