module
public import PELQuaternionIntegralOrder318
public section
noncomputable section
namespace PELPrincipalOrderCoordinates318
open PELQuaternionAlgebra318 PELQuaternionAlternatingForm318 QuaternionAlgebra
set_option maxHeartbeats 1200000
abbrev Coordinates := Fin 4 → ℤ

/-- Exact order basis:1,i,(1+j)/2,i/2+k/10. The last denominator is10,
not a freely rescaled polarization or a guessed lattice of equal rank. -/
@[expose] def embed (x : Coordinates) : B :=
  ⟨(x 0:ℚ)+(x 2:ℚ)/2,(x 1:ℚ)+(x 3:ℚ)/2,(x 2:ℚ)/2,(x 3:ℚ)/10⟩

@[expose] def product (x y : Coordinates) : Coordinates := ![
  x 0*y 0-210*x 1*y 1-84*x 1*y 3+x 2*y 2-126*x 3*y 1-42*x 3*y 3,
  x 0*y 1+x 1*y 0-2*x 1*y 2+3*x 2*y 1+x 2*y 3-x 3*y 2,
  x 0*y 2+x 2*y 0-42*x 1*y 3+x 2*y 2+42*x 3*y 1,
  x 0*y 3+x 3*y 0+5*x 1*y 2-5*x 2*y 1-2*x 2*y 3+3*x 3*y 2]

@[expose] def involution (x : Coordinates) : Coordinates := ![x 0,-x 1-x 3,x 2,x 3]

@[simp] theorem embed_zero : embed 0=0 := by ext <;> norm_num [embed]
theorem embed_add (x y : Coordinates) : embed (x+y)=embed x+embed y := by
  ext <;> simp [embed] <;> ring
theorem embed_neg (x : Coordinates) : embed (-x)= -embed x := by
  ext <;> simp [embed] <;> ring
theorem embed_mul (x y : Coordinates) : embed (product x y)=embed x*embed y := by
  ext <;> simp [embed,product] <;> push_cast <;> ring

theorem embed_rosati (x : Coordinates) : embed (involution x)=rosati (embed x) := by
  rw [rosati_coordinates]
  ext <;> simp [embed,involution] <;> ring

theorem embed_injective : Function.Injective embed := by
  intro x y h
  have h0 := congrArg QuaternionAlgebra.re h
  have h1 := congrArg QuaternionAlgebra.imI h
  have h2 := congrArg QuaternionAlgebra.imJ h
  have h3 := congrArg QuaternionAlgebra.imK h
  simp only [embed] at h0 h1 h2 h3
  have he2 : x 2=y 2 := by exact_mod_cast (show (x 2:ℚ)=(y 2:ℚ) by linarith)
  have he3 : x 3=y 3 := by exact_mod_cast (show (x 3:ℚ)=(y 3:ℚ) by linarith)
  rw [he2] at h0
  rw [he3] at h1
  have he0 : x 0=y 0 := by exact_mod_cast (show (x 0:ℚ)=(y 0:ℚ) by linarith)
  have he1 : x 1=y 1 := by exact_mod_cast (show (x 1:ℚ)=(y 1:ℚ) by linarith)
  ext i
  fin_cases i <;> assumption

/-- A genuine specified subring, with closure proved by the entire
multiplication table. Maximality/reduced discriminant is not presumed. -/
@[expose] def order : Subring B where
  carrier := Set.range embed
  zero_mem' := ⟨0,embed_zero⟩
  one_mem' := ⟨![1,0,0,0],by ext <;> norm_num [embed]⟩
  add_mem' := by
    rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩
    exact ⟨x+y,embed_add x y⟩
  neg_mem' := by
    rintro _ ⟨x,rfl⟩
    exact ⟨-x,embed_neg x⟩
  mul_mem' := by
    rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩
    exact ⟨product x y,embed_mul x y⟩

/-- The specified order has the literal four-integer-coordinate carrier.
This is the lattice interface used by the period quotient. -/
@[expose] def coordinatesEquiv : Coordinates ≃+ order where
  toFun x := ⟨embed x,⟨x,rfl⟩⟩
  invFun x := Classical.choose x.property
  left_inv x := embed_injective (Classical.choose_spec (show embed x∈order from ⟨x,rfl⟩))
  right_inv x := Subtype.ext (Classical.choose_spec x.property)
  map_add' x y := Subtype.ext (embed_add x y)

theorem coordinatesEquiv_value (x : Coordinates) : (coordinatesEquiv x:B)=embed x := rfl

theorem mu_mem : mu∈order := ⟨![0,1,0,0],by ext <;> norm_num [embed,mu]⟩

theorem rosati_mem (x : B) (hx : x∈order) : rosati x∈order := by
  obtain ⟨a,rfl⟩ := hx
  exact ⟨involution a,embed_rosati a⟩

@[expose] def integralForm (x y : Coordinates) : ℤ :=
  -2*x 0*y 1-x 0*y 3+2*x 1*y 0+x 1*y 2-x 2*y 1+x 3*y 0

/-- The same unrescaled trace form becomes integral on the specified larger
order, with unimodular Gram rather than the defective naive order form. -/
theorem pairing_value (x y : Coordinates) : pairing (embed x) (embed y)=(integralForm x y:ℚ) := by
  rw [coordinates]
  simp [embed,integralForm] <;> push_cast <;> ring
end PELPrincipalOrderCoordinates318
