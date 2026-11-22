module
public import PointwiseConverseRationalArtin
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Choose

@[expose] public section
noncomputable section
open Filter Polynomial
open PointwiseConverseRawMatrixReceiver PointwiseConverseRationalArtin
open PointwiseConverseMatchedInnerOuter

namespace PointwiseConverseRetainedArtinRows

abbrev C (i : ℕ) := ZMod (modulus i)
abbrev rel (i : ℕ) : Polynomial (C i) := X ^ i
abbrev A (i : ℕ) := AdjoinRoot (rel i)

theorem monic_rel (i : ℕ) : (rel i).Monic := monic_X.pow _

/-- Coefficient readout from the actual truncated polynomial ring. It is
not the pointwise ring structure on vectors of coefficients. -/
def coeff (i : ℕ) (x : A i) (d : Fin i) : C i :=
  (AdjoinRoot.modByMonicHom (monic_rel i) x).coeff d.val

theorem coeff_injective (i : ℕ) : Function.Injective (coeff i) := by
  intro x y e
  rcases subsingleton_or_nontrivial (C i) with h | h
  · let : Subsingleton (C i) := h
    let : Subsingleton (A i) := Module.subsingleton (C i) _
    exact Subsingleton.elim _ _
  · let : Nontrivial (C i) := h
    have hdeg : (rel i).natDegree = i := by simp [rel]
    apply (AdjoinRoot.powerBasisAux' (monic_rel i)).repr.injective
    apply Finsupp.ext
    intro k
    have hk : k.val < i := lt_of_lt_of_eq k.isLt hdeg
    rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun,AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
    exact congrFun e (⟨k.val,hk⟩ : Fin i)

/-- Columns given by the image of each retained *basis vector* on the
original cochains. For unary tests use 'unary'; for degree two keep both
group arguments. No cycle, or choice of inner lift of an approximate
outer cycle, is needed to form these columns. -/
abbrev Columns (G : Type*) [TopologicalSpace G] (S : Shape) (i : ℕ) :=
  (m : Fin S.slots) → Fin (S.cols m) → LocallyConstant (G × G) (Fin (S.rows m) → A i)

def unary {G M : Type*} [TopologicalSpace G] (z : LocallyConstant G M) :
    LocallyConstant (G × G) M :=
  ⟨fun p => z p.1, z.isLocallyConstant.comp_continuous continuous_fst⟩

def packet {G : Type*} [TopologicalSpace G] {S : Shape} {i : ℕ}
    (B : Columns G S i) (p : G × G) : Packet S i :=
  fun m a b => coeff i (B m b p a)

theorem packet_lc {G : Type*} [TopologicalSpace G] {S : Shape} {i : ℕ}
    (B : Columns G S i) :
    ∀ m a b d, IsLocallyConstant (fun p => packet B p m a b d) :=
  fun m a b d => (B m b).isLocallyConstant.comp (fun v => coeff i (v a) d)

/-- Basis equality is equivalent to *actual scalar* matrix equality,
including at the empty cut. -/
theorem packet_eq_iff {G : Type*} [TopologicalSpace G] {S : Shape} {i : ℕ}
    (B : Columns G S i) (p q : G × G) :
    packet B p = packet B q ↔ ∀ m b, B m b p = B m b q := by
  constructor
  · intro h m b
    funext a
    exact coeff_injective i (congrFun (congrFun (congrFun h m) a) b)
  · intro h
    funext m a b d
    exact congrArg (fun v => coeff i (v a) d) (h m b)

/-- Multiply coefficients in (ℤ/2^i)[t]/t^i, not coordinatewise. -/
def evaluateVector {G : Type*} [TopologicalSpace G] {S : Shape} {i : ℕ}
    (B : Columns G S i) (m : Fin S.slots) (p : G × G)
    (w : Fin (S.cols m) → A i) (a : Fin (S.rows m)) : A i :=
  ∑ b, w b * B m b p a

theorem evaluateVector_eq {G : Type*} [TopologicalSpace G] {S : Shape} {i : ℕ}
    (B : Columns G S i) {p q : G × G} (e : packet B p = packet B q)
    (m : Fin S.slots) (w : Fin (S.cols m) → A i) :
    evaluateVector B m p w = evaluateVector B m q w := by
  have h := (packet_eq_iff B p q).mp e
  funext a
  exact Finset.sum_congr rfl (fun b _ => congrArg (fun v => w b * v a) (h m b))

variable {Ω : Type*} [Field Ω] [CharZero Ω] [hΩ : IsGalois ℚ Ω]
variable (K : IntermediateField ℚ Ω) [hKfin : FiniteDimensional ℚ K]
  [hKgal : IsGalois K Ω] [hquad : IsGalois ℚ K]

include hKfin hquad in
omit hΩ hKgal in
theorem square_fixes (h2 : Module.finrank ℚ K = 2) (g : Gal(Ω/ℚ)) :
    ∀ x ∈ K, (g ^ 2) x = x := by
  apply (AlgEquiv.restrictNormal_eq_one_iff K (g ^ 2)).mp
  change AlgEquiv.restrictNormalHom K (g ^ 2) = 1
  rw [map_pow]
  have hc : Nat.card Gal(K/ℚ) = 2 := (IsGalois.card_aut_eq_finrank ℚ K).trans h2
  rw [← hc]
  exact pow_card_eq_one'

include hKfin hquad in
omit hΩ hKgal in
/-- The square, not a newly chosen relative lift. -/
def sq (h2 : Module.finrank ℚ K = 2) (g : Gal(Ω/ℚ)) : Gal(Ω/K) :=
  { (g ^ 2).toRingEquiv with commutes' := fun x => square_fixes K h2 g x.1 x.2 }

omit hΩ hKgal in
theorem sq_rat (h2 : Module.finrank ℚ K = 2) (g : Gal(Ω/ℚ)) :
    ratAut K (sq K h2 g) = g ^ 2 := AlgEquiv.ext fun _ => rfl

include hΩ hKfin hKgal hquad in
/-- One actual finite rational field for each original stage. Once the
rational representative and the second arguments are matched there,
the concrete coefficient packets match on the very same inner clock.
Target may be taken to be τ*u, with the old orientation unchanged. -/
theorem select_fields_then_match (S : Shape) (h2 : Module.finrank ℚ K = 2)
    (B : (i : ℕ) → Columns Gal(Ω/K) S i)
    (X : ℕ → IntermediateField ℚ Ω) [∀ i, FiniteDimensional ℚ (X i)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ D : ℕ → FiniteGaloisIntermediateField ℚ Ω,
      (∀ i, X i ≤ (D i).toIntermediateField) ∧
      ∀ (γ target : ℕ → Gal(Ω/ℚ)) (u v : ℕ → Gal(Ω/K)),
        (∀ᶠ i in (U : Filter ℕ), res (D i) (γ i) = res (D i) (target i) ∧
          res (D i) (ratAut K (u i)) = res (D i) (ratAut K (v i))) →
        ∃ M : RawMatch S, M.inner = U ∧
          M.left = (fun i => packet (B i) (sq K h2 (γ i), u i)) ∧
          M.right = (fun i => packet (B i) (sq K h2 (target i), v i)) ∧
          leftSeries M = rightSeries M := by
  classical
  choose D hX hD using (fun i => raw_ambient_control K S i (packet (B i)) (packet_lc (B i)) (X i))
  refine ⟨D, hX, ?_⟩
  intro γ target u v h
  let M : RawMatch S :=
    { inner := U, cofinal := hU
      left := fun i => packet (B i) (sq K h2 (γ i), u i)
      right := fun i => packet (B i) (sq K h2 (target i), v i)
      fullMatch := h.mono (fun i hi => square_packet_eq K S i (packet (B i)) (D i)
        (hD i) _ _ _ _ _ _ (sq_rat K h2 _) (sq_rat K h2 _) hi.1 hi.2) }
  exact ⟨M, rfl, rfl, rfl, matched_series_eq M⟩

end PointwiseConverseRetainedArtinRows
