module
public import BoundedPrimaryTowerVanishing318
public section
namespace PrimaryTateTower318

/-- The actual inverse system of2-power torsion, including its transition
maps. Cardinalities alone are not substituted for compatibility. -/
def tower (G : Type*) [AddCommGroup G] : AddSubgroup (ℕ → G) where
  carrier := {x | (∀ k : ℕ, (2^k) • x k=0) ∧ (∀ k : ℕ, 2 • x (k+1)=x k)}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    rintro x y ⟨hx,hx'⟩ ⟨hy,hy'⟩
    constructor
    · intro k; simp only [Pi.add_apply,nsmul_add,hx k,hy k,add_zero]
    · intro k; simp only [Pi.add_apply,nsmul_add,hx' k,hy' k]
  neg_mem' := by
    rintro x ⟨hx,hx'⟩
    constructor
    · intro k; simp only [Pi.neg_apply,neg_nsmul,hx k,neg_zero]
    · intro k; simp only [Pi.neg_apply,neg_nsmul,hx' k]

/-- A group equivalence acts on the whole compatible tower at once. -/
def mapEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) : tower G ≃+ tower H where
  toFun x := ⟨fun k => e (x.val k), by
    constructor
    · intro k; rw [←map_nsmul,x.property.1 k,map_zero]
    · intro k; rw [←map_nsmul,x.property.2 k]⟩
  invFun y := ⟨fun k => e.symm (y.val k), by
    constructor
    · intro k; rw [←map_nsmul,y.property.1 k,map_zero]
    · intro k; rw [←map_nsmul,y.property.2 k]⟩
  left_inv x := by
    apply Subtype.ext
    funext k
    exact e.symm_apply_apply (x.val k)
  right_inv y := by
    apply Subtype.ext
    funext k
    exact e.apply_symm_apply (y.val k)
  map_add' x y := by
    apply Subtype.ext
    funext k
    exact e.map_add (x.val k) (y.val k)

/-- Uniform bounded exponent kills the inverse limit, not each finite
transition group individually. -/
theorem subsingleton_of_bounded_exponent (G : Type*) [AddCommGroup G]
    (N : ℕ) (hN : ∀ g : G, (2^N) • g=0) : Subsingleton (tower G) := by
  constructor
  intro x y
  apply Subtype.ext
  funext k
  have hx := BoundedPrimaryTowerVanishing318.tower_zero_of_bounded_exponent
    N hN x.val x.property.2 k
  have hy := BoundedPrimaryTowerVanishing318.tower_zero_of_bounded_exponent
    N hN y.val y.property.2 k
  exact hx.trans hy.symm

theorem finite_cyclic_tower_subsingleton (N : ℕ) :
    Subsingleton (tower (ZMod (2^N))) := by
  apply subsingleton_of_bounded_exponent _ N
  intro g
  simp [nsmul_eq_mul]

end PrimaryTateTower318
