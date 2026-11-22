module
public import ActualGaussianWeberStockReductionAdd318
public import ActualGaussianWeberFiniteAnchorTranslate318
public import ActualGaussianWeberOrdinaryStock318
public import ActualGaussianWeberQuarterTurn318
public section
noncomputable section

namespace ActualGaussianWeberOriginJet318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberValuedKernelChart318
open ActualGaussianWeberStockReductionAdd318 ActualGaussianWeberFiniteAnchorTranslate318
open ActualGaussianWeberMixedStockCoordinates318 ActualGaussianWeberMixedValuedData318
open ActualGaussianWeberOrdinaryStock318 ActualGaussianWeberOrdinarySlope318
open ActualGaussianWeberQuarterTurn318

variable {F : Type*} [Field F] [DecidableEq F] (V : ValuationSubring F)
variable (hF : (2:F)≠0) (h2 : (2:ResidueField V)≠0) (t : V)

/-- The original t=−x/y coordinate at the fixed scale t; nothing
is divided in the residue field. -/
structure Witness (P : WP F) where
  origin : specialize V h2 P=Point.zero
  c : V
  exact_t : tCoord P=V.subtype (t*c)

theorem tCoord_neg (P : WP F) : tCoord (-P)= -tCoord P := by
  cases P with
  | zero => change (0:F)= -0; rw [neg_zero]
  | some x y h =>
    rw [Point.neg_some]
    change (-x)/((curve F).toAffine.negY x y)= -((-x)/y)
    rw [literal_negY,div_neg]

theorem tCoord_turn (i : F) (hi : i^2= -1) (P : WP F) :
    tCoord (turn hF i hi P)=i*tCoord P := by
  cases P with
  | zero => change (0:F)=i*0; rw [mul_zero]
  | some x y h =>
    rw [turn_some]
    change (-(-x))/(i*y)=i*((-x)/y)
    rw [neg_neg]
    by_cases hy : y=0
    · rw [hy,mul_zero,div_zero,div_zero,mul_zero]
    · have hi0 : i≠0 := by
        intro hz
        rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at hi
        exact (neg_ne_zero.mpr one_ne_zero) hi.symm
      symm
      apply (eq_div_iff (mul_ne_zero hi0 hy)).2
      calc
        _ = i^2*((-x)/y*y) := by ring
        _ = x := by rw [hi,div_mul_cancel₀ _ hy]; ring

@[expose] def zero_witness : Witness V h2 t (0:WP F) :=
  ⟨rfl,0,by change (0:F)=V.subtype (t*0); rw [mul_zero,map_zero]⟩

def neg_witness {P : WP F} (A : Witness V h2 t P) : Witness V h2 t (-P) where
  origin := by rw [specialize_neg V h2 P,A.origin] <;> rfl
  c := -A.c
  exact_t := by rw [tCoord_neg,A.exact_t,mul_neg,map_neg]

private def ordinate : WP F → F
  | Point.zero => 0
  | Point.some _ y _ => y

/-- Actual first jet from the same finite anchor T₀=(0,0).
The two-origin chord and its order-five estimate are not involved. -/
theorem add_witness (ht : t∈maximalIdeal V) {P Q : WP F}
    (A : Witness V h2 t P) (B : Witness V h2 t Q) :
    ∃ U : Witness V h2 t (P+Q), residue V U.c=residue V A.c+residue V B.c := by
  by_cases hZero : P=Point.zero
  · subst P
    have hP0 : V.subtype (t*A.c)=0 := A.exact_t.symm
    have hP : t*A.c=0 := V.subtype_injective (hP0.trans (map_zero V.subtype).symm)
    have hQsum : (Point.zero : WP F)+Q=Q := zero_add _
    refine ⟨⟨?_,A.c+B.c,?_⟩,map_add _ _ _⟩
    · rw [hQsum]; exact B.origin
    · rw [hQsum,B.exact_t,mul_add,hP,zero_add]
  · obtain ⟨p⟩ := from_kernel V h2 P A.origin
    obtain ⟨q⟩ := from_kernel V h2 Q B.origin
    have hp : p.t=t*A.c := V.subtype_injective (p.t_exact.trans A.exact_t)
    have hq : q.t=t*B.c := V.subtype_injective (q.t_exact.trans B.exact_t)
    obtain ⟨R⟩ := read V hF h2 B.origin q
    obtain ⟨K,hXY,hAdd⟩ := mixed_stock_coordinates V h2 P R.x (-q.t*R.u)
      R.ns A.origin hZero p
    let d : V := -B.c*R.u
    have hYQ : -q.t*R.u=t*d := by rw [hq]; unfold d; ring
    have hd : residue V d= -residue V B.c := by simp [d,R.u_residue]
    obtain ⟨e,hY,he⟩ := mixed_scaled_ordinate V K ht hp hYQ R.x_residue
    have hOrigin : specialize V h2 (P+Q)=Point.zero := by
      classical
      have hP₀ : specialize V h2 P=(0:WP (ResidueField V)) := A.origin
      have hQ₀ : specialize V h2 Q=(0:WP (ResidueField V)) := B.origin
      rw [specialize_add V hF h2 P Q,hP₀,hQ₀,add_zero] <;> rfl
    obtain ⟨S⟩ := from_kernel V h2 (P+Q) hOrigin
    obtain ⟨T⟩ := read V hF h2 hOrigin S
    have hPoint : Point.some (V.subtype T.x) (V.subtype (-S.t*T.u)) T.ns =
        Point.some (V.subtype K.X) (V.subtype K.Y) hXY := by
      rw [←T.point_exact,add_assoc,R.point_exact,hAdd]
    have hOrd : -S.t*T.u=K.Y := V.subtype_injective (congrArg ordinate hPoint)
    obtain ⟨v,hv,hvr⟩ := inverse_over_residue_one V T.u T.u_residue
    have hScale : (-S.t*T.u)*v=(t*e)*v :=
      congrArg (fun x : V => x*v) (hOrd.trans hY)
    have hNeg : -S.t=(t*e)*v := by simpa only [mul_assoc,hv,mul_one] using hScale
    have hS : S.t=t*(-e*v) := by
      calc
        _ = -(-S.t) := (neg_neg _).symm
        _ = _ := by rw [hNeg]; ring
    refine ⟨⟨hOrigin,-e*v,S.t_exact.symm.trans (congrArg V.subtype hS)⟩,?_⟩
    simp only [map_mul,map_neg,he,hd,hvr,mul_one]
    ring

/-- Actual subgroup on which the normalized first jet is defined. -/
@[expose] def scaledOrigin (ht : t∈maximalIdeal V) : AddSubgroup (WP F) where
  carrier := {P | Nonempty (Witness V h2 t P)}
  zero_mem' := ⟨zero_witness V h2 t⟩
  add_mem' hP hQ := by
    obtain ⟨A⟩ := hP
    obtain ⟨B⟩ := hQ
    obtain ⟨U,_⟩ := add_witness V hF h2 t ht A B
    exact ⟨U⟩
  neg_mem' hP := by
    obtain ⟨A⟩ := hP
    exact ⟨neg_witness V h2 t A⟩

@[expose] def chosen (ht : t∈maximalIdeal V) (P : scaledOrigin V hF h2 t ht) :
    Witness V h2 t (P:WP F) := Classical.choice P.property

theorem coeff_unique (ht0 : t≠0) {P : WP F} (A B : Witness V h2 t P) :
    A.c=B.c := by
  apply mul_left_cancel₀ ht0
  exact V.subtype_injective (A.exact_t.symm.trans B.exact_t)

/-- First jet in the residue additive group, from the literal
finite translation at the actual (0,0) anchor. -/
@[expose] def jet (ht : t∈maximalIdeal V) (ht0 : t≠0) :
    scaledOrigin V hF h2 t ht→+ResidueField V where
  toFun P := residue V (chosen V hF h2 t ht P).c
  map_zero' := by
    have hc := coeff_unique V h2 t ht0 (chosen V hF h2 t ht 0) (zero_witness V h2 t)
    simpa only [hc,zero_witness,map_zero]
  map_add' P Q := by
    obtain ⟨U,hU⟩ := add_witness V hF h2 t ht (chosen V hF h2 t ht P) (chosen V hF h2 t ht Q)
    have hc := coeff_unique V h2 t ht0 (chosen V hF h2 t ht (P+Q)) U
    exact (congrArg (residue V) hc).trans hU

theorem jet_eq_of_witness (ht : t∈maximalIdeal V) (ht0 : t≠0)
    (P : scaledOrigin V hF h2 t ht) (A : Witness V h2 t (P:WP F)) :
    jet V hF h2 t ht ht0 P=residue V A.c :=
  congrArg (residue V) (coeff_unique V h2 t ht0 (chosen V hF h2 t ht P) A)

@[expose] def turnWitness (i : V) (hi : i^2= -1) {P : WP F} (A : Witness V h2 t P) :
    Witness V h2 t (turn hF (V.subtype i) (chosen_square_generic V i hi) P) where
  origin := by rw [specialize_turn V hF h2 i hi P,A.origin] <;> rfl
  c := i*A.c
  exact_t := by
    rw [tCoord_turn hF,A.exact_t,map_mul,map_mul,map_mul]
    ring

end ActualGaussianWeberOriginJet318
