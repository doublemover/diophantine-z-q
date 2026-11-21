module
public import ActualTZHybridGrid318
public import ActualTZGridMarginalJoin318
public import ActualTZPhysicalShortZero318
public import ActualTZCanonicalCellRange318
public import ActualTZRetainedHorizon318
import all ActualTZExactZeroIntegerGrid318
import all ActualTZLiteralWrapClipping318
public section
noncomputable section
namespace ActualTZHybridCanonicalWrap318
open scoped BigOperators
open ActualTZHybridGlobalLocalStencil318 ActualTZHybridGrid318 ActualTZExactZeroIntegerGrid318
open ActualTZCanonicalWrapFibres318 ActualTZRetainedHorizon318 ActualTZLiteralWrapClipping318
attribute [local instance] Classical.propDecidable
variable {a t s : ℕ}

/-- Literal off-grid local and global test. Explicitly different
coordinate widths; a single canonical cyclic x is shared by the
whole mask. Fixed D,C do not depend on the model cutoff. -/
structure Context (a t s : ℕ) (I : Type*) where
  y N n J M q b D C : ℕ
  hn : 0<n
  hJ : 0<J
  hM : 0<M
  hq : 0<q
  global_small : q*J≤n
  local_small : primorial y*M^2≤C*n
  sample : primorial y*n≤N
  cut : D≤y
  unit : 1≤b ∧ b≤primorial y ∧ (primorial y).Coprime b
  divided : Fin s→ℤ
  divided_bound : ∀ j,(divided j).natAbs≤D
  divided_ne : ∃ j,divided j≠0
  site : I→Bits a t
  distinct : Function.Injective site

namespace Context
variable {I : Type*} [Fintype I] [DecidableEq I] (L : Context a t s I)

abbrev Pair (I : Type*) := {u : I×I // u.1≠u.2}
@[expose] def cap : ℕ := a+2*t*s*L.D*L.C
@[expose] def keyPrime : ℕ := primorial L.y*L.q
abbrev Keys := Wrap I L.cap
abbrev G := GridOf a t s L.J L.M
abbrev lens := lengths a t s L.J L.M
abbrev start := starts a t s L.M
abbrev minLen := min L.J L.M

@[expose] def pt (z : L.G) : Vals a t s := point L.lens L.start z ∘ flat a t s
@[expose] def actualSlope (i : Fin s) : ℤ := (primorial L.y:ℤ)*L.divided i
@[expose] def offset (z : L.G) (i : I) : ℤ := off L.q L.actualSlope (L.site i) (L.pt z)

theorem offset_cap (z : L.G) (i : I) : |L.offset z i|≤(L.cap:ℤ)*(L.n:ℤ) := by
  apply off_bound _ _ _ L.J L.M (primorial L.y) L.q L.n L.D L.C L.global_small L.local_small
  · intro j
    unfold actualSlope
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤(primorial L.y:ℤ))]
    have h := L.divided_bound j
    rw [←Int.natCast_natAbs]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by positivity)
  · intro j
    have hx (b : Bool) : 0≤L.pt z (.inl (b,j))∧L.pt z (.inl (b,j))<(L.J:ℤ) := by
      unfold pt
      rw [Function.comp_apply,point_at]
      simp only [lower,zero_add]
      exact ⟨by positivity,by exact_mod_cast (ActualTZHybridGrid318.unflat z (.inl (b,j))).isLt⟩
    exact abs_le.2 ⟨by linarith only [(hx true).1,(hx false).2],
      by linarith only [(hx true).2,(hx false).1]⟩
  · intro r j
    unfold pt
    rw [Function.comp_apply,point_at]
    change |1+((ActualTZHybridGrid318.unflat z (.inr (r,.inl j))).val:ℤ)|≤(L.M:ℤ)
    have h : ((ActualTZHybridGrid318.unflat z (.inr (r,.inl j))).val:ℤ)<(L.M:ℤ) := by
      exact_mod_cast (ActualTZHybridGrid318.unflat z (.inr (r,.inl j))).isLt
    rw [abs_of_nonneg (by positivity)]
    omega
  · intro r
    have hx (b : Bool) : -(L.M:ℤ)≤L.pt z (.inr (r,.inr b))∧
        L.pt z (.inr (r,.inr b))≤(L.M:ℤ) := by
      unfold pt
      rw [Function.comp_apply,point_at]
      have hh := (ActualTZHybridGrid318.unflat z (.inr (r,.inr b))).isLt
      simp only [lower]
      have hhi : ((ActualTZHybridGrid318.unflat z (.inr (r,.inr b))).val:ℤ)
          <2*(L.M:ℤ)+1 := by exact_mod_cast hh
      have hlo : 0≤((ActualTZHybridGrid318.unflat z (.inr (r,.inr b))).val:ℤ) := by positivity
      omega
    exact abs_le.2 ⟨by linarith only [(hx true).1,(hx false).2],
      by linarith only [(hx true).2,(hx false).1]⟩

@[expose] def code (z : L.G) (x : Fin L.n) : L.Keys :=
  key L.n L.cap L.hn (L.offset z) (L.offset_cap z) x
@[expose] def size (z : L.G) (r : L.Keys) : ℕ := (fibre (L.code z) r).card
@[expose] def wrapped (z : L.G) (r : L.Keys) (i : I) : ℤ :=
  L.offset z i-decode L.cap r i*(L.n:ℤ)

@[expose] def unrenamed (r : L.Keys) (i : Pair I) : Poly a t s :=
  physical (primorial L.y) L.n L.q L.actualSlope (L.site i.val.1) (L.site i.val.2)
    (decode L.cap r i.val.1) (decode L.cap r i.val.2)

@[expose] def poly (r : L.Keys) (i : Pair I) : MvPolynomial (Fin (dim a t s)) ℤ :=
  MvPolynomial.rename (flat a t s) (L.unrenamed r i)

@[expose] def v (z : L.G) (r : L.Keys) (i : Pair I) : ℤ :=
  MvPolynomial.eval (point L.lens L.start z) (L.poly r i)

@[expose] def θ (z : L.G) (r : L.Keys) : ℝ :=
  kept L.n ((L.n:ℝ)^((3:ℝ)/4)) L.size (fun z r i=>L.v z r i=0) z r
@[expose] def hit (p : ℕ) (z : L.G) (r : L.Keys) : Prop :=
  ∃ i : Pair I,(p:ℤ)∣L.v z r i

@[expose] def mass (_ : L.G) : ℝ := (uniform L.lens:ℝ)
@[expose] def base (_ : I) : ℕ := L.b

theorem poly_degree (r : L.Keys) (i : Pair I) : (L.poly r i).totalDegree≤2 :=
  (MvPolynomial.totalDegree_rename_le _ _).trans (degree _ _ _ _ _ _ _ _)

theorem regular_poly (p : ℕ) (hp : p.Prime) (hY : L.y<p) (hP : ¬p∣L.keyPrime)
    (r : L.Keys) (i : Pair I) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (L.poly r i)≠0 := by
  obtain ⟨j,hj⟩ := L.divided_ne
  have h := survives (primorial L.y) L.n L.q p L.D hp (L.cut.trans_lt hY) hP L.divided j
    hj (L.divided_bound j) (L.site i.val.1) (L.site i.val.2)
    (fun he=>i.prop (L.distinct he)) (decode L.cap r i.val.1) (decode L.cap r i.val.2)
  simpa only [poly,unrenamed,MvPolynomial.map_rename,
    MvPolynomial.rename_eq_zero_iff_of_injective _ (flat a t s).injective] using h

theorem poly_nonzero (r : L.Keys) (i : Pair I) : L.poly r i≠0 := by
  obtain ⟨p,hp,hP⟩ := Nat.exists_infinite_primes (max L.y L.keyPrime+1)
  have hKey : 0<L.keyPrime := mul_pos (primorial_pos _) L.hq
  have hNo : ¬p∣L.keyPrime := fun h=>by have := Nat.le_of_dvd hKey h; omega
  have hh := L.regular_poly p hP (by omega) hNo r i
  intro h
  rw [h,map_zero] at hh
  exact hh rfl

theorem physical_value (z : L.G) (r : L.Keys) (i : Pair I) (x : ℤ) :
    L.v z r i=((primorial L.y:ℤ)*(x+L.wrapped z r i.val.1)+L.b)-
      ((primorial L.y:ℤ)*(x+L.wrapped z r i.val.2)+L.b) := by
  unfold v poly
  rw [MvPolynomial.eval_rename]
  change MvPolynomial.eval (L.pt z) (L.unrenamed r i)=_
  unfold unrenamed
  rw [eval_physical (primorial L.y) L.n L.q L.actualSlope (L.site i.val.1) (L.site i.val.2)
    (decode L.cap r i.val.1) (decode L.cap r i.val.2) x (L.b:ℤ) (L.pt z)]
  unfold wrapped offset
  ring

theorem size_total (z : L.G) : (∑ r : L.Keys,L.size z r)=L.n := fibres_cover (L.code z)
theorem size_le (z : L.G) (r : L.Keys) : L.size z r≤L.n :=
  (Finset.card_filter_le _ _).trans_eq Fintype.card_fin

theorem θ_bounds (z : L.G) (r : L.Keys) : 0≤L.θ z r ∧ L.θ z r≤wrapMass L.n L.size z r := by
  unfold θ kept wrapMass
  split_ifs
  · exact ⟨le_rfl,by positivity⟩
  · exact ⟨by positivity,le_rfl⟩

theorem θ_unit (z : L.G) (r : L.Keys) : L.θ z r≤1 := by
  have hn : (0:ℝ)<L.n := by exact_mod_cast L.hn
  exact (L.θ_bounds z r).2.trans ((div_le_one hn).2 (by exact_mod_cast L.size_le z r))

theorem kept_cells (z : L.G) (r : L.Keys) (h : 0<L.θ z r) :
    (L.n:ℝ)^((3:ℝ)/4)≤(L.size z r:ℝ) ∧ ∀ i : Pair I,L.v z r i≠0 := by
  have H : ¬((L.size z r:ℝ)<(L.n:ℝ)^((3:ℝ)/4)∨∃ i : Pair I,L.v z r i=0) := by
    intro hc
    simp only [θ,kept,if_pos hc,lt_irrefl] at h
  exact ⟨le_of_not_gt (fun hh=>H (Or.inl hh)),fun i hi=>H (Or.inr ⟨i,hi⟩)⟩

theorem horizon_hit (p : ℕ) (z : L.G) (r : L.Keys) (h : 0<L.θ z r)
    (hh : L.hit p z r) : p≤2*L.N := by
  obtain ⟨i,hi⟩ := hh
  have hSize : 0<L.size z r := by
    have hP := Real.rpow_pos_of_pos (show 0<(L.n:ℝ) by exact_mod_cast L.hn) ((3:ℝ)/4)
    exact_mod_cast hP.trans_le (L.kept_cells z r h).1
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hSize
  have hR (k : I) : residue L.n ((x.val:ℤ)+1+L.offset z k)=
      (x.val:ℤ)+1+L.wrapped z r k :=
    ActualTZCanonicalCellRange318.residue_eq L.hn (L.offset z) (L.offset_cap z) r x hx k
  have H := L.physical_value z r i ((x.val:ℤ)+1)
  rw [←hR i.val.1,←hR i.val.2] at H
  have hb : 1≤(L.b:ℤ)∧(L.b:ℤ)≤(primorial L.y:ℤ) :=
    ⟨by exact_mod_cast L.unit.1,by exact_mod_cast L.unit.2.1⟩
  exact horizon _ _ _ _ (primorial_pos _) L.hn L.sample _ _ _ _ hb hb
    (by rw [←H]; exact (L.kept_cells z r h).2 i)
    (by rw [←H]; exact hi)

theorem full_mass : (∑ z : L.G,L.mass z*(∑ r : L.Keys,wrapMass L.n L.size z r))=1 := by
  have hn : (L.n:ℝ)≠0 := by exact_mod_cast L.hn.ne'
  have h (z : L.G) : (∑ r : L.Keys,wrapMass L.n L.size z r)=1 := by
    unfold wrapMass
    rw [←Finset.sum_div,←Nat.cast_sum,L.size_total,div_self hn]
  simp only [h,mul_one,mass]
  exact_mod_cast uniform_one L.lens (fun i=>(lt_min L.hJ L.hM).trans_le (lengths_min i))

theorem retained_mass : (∑ z : L.G,L.mass z*(∑ r : L.Keys,L.θ z r))≤1 := by
  rw [←L.full_mass]
  exact Finset.sum_le_sum (fun z _=>mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun r _=>(L.θ_bounds z r).2)) (by unfold mass; positivity))

theorem lost :
    (∑ z : L.G,L.mass z*(∑ r : L.Keys,(wrapMass L.n L.size z r-L.θ z r)))≤
      (Fintype.card L.Keys:ℝ)*((L.n:ℝ)^(-(1:ℝ)/4)+
        (Fintype.card (Pair I):ℝ)*((dim a t s:ℝ)*(2/(L.minLen:ℝ)))) :=
  ActualTZPhysicalShortZero318.lost_key_mass L.lens L.start L.minLen 2 L.n (lt_min L.hJ L.hM)
    lengths_min L.hn L.size L.size_le L.poly L.poly_nonzero L.poly_degree

theorem sparse (p : ℕ) (hp : p.Prime) (hy : L.y<p) (hP : ¬p∣L.keyPrime) :
    (∑ z : L.G,L.mass z*(∑ r : L.Keys,L.θ z r*(if L.hit p z r then 1 else 0)))≤
      (Fintype.card L.Keys:ℝ)*(Fintype.card (Pair I):ℝ)*
        ((2:ℝ)^(dim a t s)*(dim a t s:ℝ)*2)*(1/(p:ℝ)+1/(L.minLen:ℝ)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact ActualTZGridMarginalJoin318.weighted_marginal (p:=p) L.lens L.start L.minLen 2
    (lt_min L.hJ L.hM) lengths_min L.poly (L.regular_poly p hp hy hP) L.poly_degree L.θ
    (fun z r=>(L.θ_bounds z r).1) L.θ_unit (L.hit p) (fun _ _ H=>H)

end Context
end ActualTZHybridCanonicalWrap318
