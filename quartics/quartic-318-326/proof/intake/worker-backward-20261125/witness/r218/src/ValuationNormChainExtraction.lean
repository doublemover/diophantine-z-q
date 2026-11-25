module
public import ValuationEvenNormChain
public section
namespace ValuationNormChainExtraction

@[expose] def step (R initial m : ℤ) : Option ℤ → ℤ
  | none => 2*initial
  | some leaf => min (2*initial) (2*leaf-(2*m-1)*R)
@[expose] def chain (R initial : ℤ) : List (ℤ×Option ℤ) → ℤ
  | [] => initial
  | (m,leaf)::rest => chain R (step R initial m leaf) rest
@[expose] def HasOrder (m : ℤ) : Option ℤ → Prop
  | none => True
  | some leaf => m≤leaf

theorem extract (R initial : ℤ) (leaves : List (ℤ×Option ℤ))
    (hR : 1≤R) (hm : ∀ p∈leaves,1≤p.1)
    (hfinal : 0<2*chain R initial leaves+R) :
    0<2*initial+R ∧ ∀ p∈leaves,HasOrder p.1 p.2 := by
  induction leaves generalizing initial with
  | nil => simpa [chain] using hfinal
  | cons p rest ih =>
    obtain ⟨m,leaf⟩ := p
    have htail : ∀ p∈rest,1≤p.1 := by
      intro p hp
      exact hm p (List.mem_cons_of_mem _ hp)
    have hfirst : 1≤m := hm (m,leaf) (by simp)
    obtain ⟨hstep,hrest⟩ := ih _ htail (by simpa [chain] using hfinal)
    have hs : 0<2*initial+R ∧ HasOrder m leaf := by
      cases leaf with
      | none => simp only [step] at hstep; exact ⟨by omega, trivial⟩
      | some leaf =>
        exact NormChainValuation.backward_step R m
          (min (2*initial) (2*leaf-(2*m-1)*R)) initial leaf
          hR hfirst hstep (min_le_left _ _) (min_le_right _ _)
    refine ⟨hs.1,?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with hp|hp
    · simpa [hp] using hs.2
    · exact hrest p hp

variable {K : Type*} [Field K]
structure Leaf (K : Type*) where
  weight : K
  leaf : K
  order : ℤ
  halfValue : Option ℤ

@[expose] def Spec (v : AddValuation K (WithTop ℤ)) (R : ℤ) (p : Leaf K) : Prop :=
  v p.weight=(-(2*p.order-1)*R : ℤ) ∧
  match p.halfValue with
  | none => p.leaf=0
  | some a => v p.leaf=(2*a : ℤ)

@[expose] def actual (initial : K) (leaves : List (Leaf K)) : K :=
  leaves.foldl (fun previous p => previous^2+p.weight*p.leaf) initial
@[expose] def numerical (leaves : List (Leaf K)) : List (ℤ×Option ℤ) :=
  leaves.map (fun p => (p.order,p.halfValue))

theorem weight_odd (R m : ℤ) (hR : Odd R) : Odd (-(2*m-1)*R) := by
  obtain ⟨r,hr⟩ := hR
  exact ⟨-2*m*r-m+r,by rw [hr]; ring⟩

theorem step_value (v : AddValuation K (WithTop ℤ)) (R a : ℤ)
    (p : Leaf K) (initial : K) (hR : Odd R) (hs : Spec v R p)
    (hi : v initial=a) :
    v (initial^2+p.weight*p.leaf)=(step R a p.order p.halfValue : ℤ) := by
  obtain ⟨hw,hl⟩ := hs
  cases he : p.halfValue with
  | none =>
    rw [he] at hl
    simp only [step,he]
    simp only [hl,mul_zero,add_zero,v.map_pow,hi]
    norm_cast
  | some b =>
    rw [he] at hl
    have hh := ValuationEvenNormChain.step_value v p.weight initial p.leaf
      (-(2*p.order-1)*R) a (2*b) hw hi hl (weight_odd R p.order hR) ⟨b,by omega⟩
    have heq : -(2*p.order-1)*R+2*b=2*b-(2*p.order-1)*R := by ring
    rw [heq] at hh
    simpa only [step,he] using hh

theorem value (v : AddValuation K (WithTop ℤ)) (R a : ℤ)
    (leaves : List (Leaf K)) (initial : K) (hR : Odd R)
    (hs : ∀ p∈leaves,Spec v R p) (hi : v initial=a) :
    v (actual initial leaves)=(chain R a (numerical leaves) : ℤ) := by
  induction leaves generalizing initial a with
  | nil => simpa [actual,numerical,chain] using hi
  | cons p rest ih =>
    have hp := hs p (by simp)
    have ht : ∀ x∈rest,Spec v R x := by
      intro x hx
      exact hs x (List.mem_cons_of_mem _ hx)
    simpa only [actual,List.foldl_cons,numerical,List.map_cons,chain] using
      ih (step R a p.order p.halfValue) (initial^2+p.weight*p.leaf) ht
        (step_value v R a p initial hR hp hi)

theorem nonpositive (R initial : ℤ) (leaves : List (ℤ×Option ℤ))
    (hi : initial≤0) : chain R initial leaves≤0 := by
  induction leaves generalizing initial with
  | nil => exact hi
  | cons p rest ih =>
    apply ih
    cases p.2 <;> simp only [step]
    · omega
    · exact le_trans (min_le_left _ _) (by omega)

/-- The actual field-valued chain now supplies the numerical recursion,
including zero leaves, before the backward extraction is applied. -/
theorem extract_actual_contact (v : AddValuation K (WithTop ℤ)) (R n : ℤ)
    (leaves : List (Leaf K)) (hR : Odd R)
    (hs : ∀ p∈leaves,Spec v R p)
    (hm : ∀ p∈leaves,1≤p.order)
    (hn : v (actual 1 leaves)=n) (hthreshold : 0<2*n+R) :
    0<R ∧ ∀ p∈leaves,HasOrder p.order p.halfValue := by
  have hv := value v R 0 leaves 1 hR hs (by simp)
  rw [hn] at hv
  have heq : n=chain R 0 (numerical leaves) := by exact_mod_cast hv
  have hnonpositive := nonpositive R 0 (numerical leaves) (by omega)
  have hp : 0<R := by omega
  refine ⟨hp,?_⟩
  have hms : ∀ p∈numerical leaves,1≤p.1 := by
    intro p hmem
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hmem
    exact hm x hx
  have hex := (extract R 0 (numerical leaves) (by omega) hms
    (by simpa only [←heq] using hthreshold)).2
  intro p hp
  exact hex (p.order,p.halfValue) (List.mem_map.mpr ⟨p,hp,rfl⟩)

end ValuationNormChainExtraction
