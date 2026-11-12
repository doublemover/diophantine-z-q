module
public import ActualTwoDescentFourInfinitePointConsumer318
public section
noncomputable section
namespace ActualTwoDescentSquareClassFieldMap318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentSquareClassQuotient318
variable {L : Type*} [Field L] [CharZero L]

lemma field_map_ne_zero (f : K →+* L) {a : K} (ha : a ≠ 0) : f a ≠ 0 := by
  intro he
  apply ha
  apply f.injective
  simpa only [map_zero] using he

def squareClassMap (f : K →+* L) : SquareClass K →* SquareClass L :=
  QuotientGroup.map (powMonoidHom (α:=Kˣ) 2).range (powMonoidHom (α:=Lˣ) 2).range
    (Units.map f.toMonoidHom) (by
      rintro u ⟨v,rfl⟩
      refine ⟨Units.map f.toMonoidHom v,?_⟩
      exact (map_pow (Units.map f.toMonoidHom) v 2).symm)

lemma actual_squareclass_map_value (f : K →+* L) (a : K) (ha : a ≠ 0) :
    squareClassMap f (classOf a ha)=classOf (f a) (field_map_ne_zero f ha) := by
  have hu : Units.map f.toMonoidHom (Units.mk0 a ha)=Units.mk0 (f a) (field_map_ne_zero f ha) := by ext; rfl
  change QuotientGroup.mk (Units.map f.toMonoidHom (Units.mk0 a ha))=_
  rw [hu]
  rfl

def squarePairMap (f : K →+* L) : SquareClass K × SquareClass K →* SquareClass L × SquareClass L where
  toFun z := (squareClassMap f z.1,squareClassMap f z.2)
  map_one' := Prod.ext (map_one _) (map_one _)
  map_mul' x y := Prod.ext (map_mul _ _ _) (map_mul _ _ _)

end ActualTwoDescentSquareClassFieldMap318
