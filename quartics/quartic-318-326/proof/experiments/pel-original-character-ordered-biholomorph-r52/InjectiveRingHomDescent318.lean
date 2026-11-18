module
public import Mathlib.Algebra.Ring.Equiv
public section
noncomputable section
namespace InjectiveRingHomDescent318
variable {R S T:Type*} [CommRing R] [CommRing S] [CommRing T]
  (j:R→+*S) (hj:Function.Injective j) (f:T→+*S)

/-- Valuewise membership in the exact image of an injective ring map
produces a ring-homomorphic factor, not just unrelated preimages. -/
@[expose] def descend (hf:∀x:T,f x∈Set.range j):T→+*R where
  toFun x:=Classical.choose (hf x)
  map_zero':=by
    apply hj
    exact (Classical.choose_spec (hf 0)).trans ((map_zero f).trans (map_zero j).symm)
  map_one':=by
    apply hj
    exact (Classical.choose_spec (hf 1)).trans ((map_one f).trans (map_one j).symm)
  map_add' x y:=by
    apply hj
    rw [map_add,Classical.choose_spec (hf x),Classical.choose_spec (hf y)]
    exact (Classical.choose_spec (hf (x+y))).trans (map_add f x y)
  map_mul' x y:=by
    apply hj
    rw [map_mul,Classical.choose_spec (hf x),Classical.choose_spec (hf y)]
    exact (Classical.choose_spec (hf (x*y))).trans (map_mul f x y)
lemma factor (hf:∀x:T,f x∈Set.range j):j.comp (descend j hj f hf)=f:=by
  ext x
  exact Classical.choose_spec (hf x)
lemma unique (hf:∀x:T,f x∈Set.range j) (k:T→+*R) (hk:j.comp k=f):
    k=descend j hj f hf:=by
  ext x
  apply hj
  exact (RingHom.congr_fun hk x).trans (Classical.choose_spec (hf x)).symm

theorem existsUnique_factor (hf:∀x:T,f x∈Set.range j):
    ∃!k:T→+*R,j.comp k=f:=
  ⟨descend j hj f hf,factor j hj f hf,fun k hk=>unique j hj f hf k hk⟩
end InjectiveRingHomDescent318
