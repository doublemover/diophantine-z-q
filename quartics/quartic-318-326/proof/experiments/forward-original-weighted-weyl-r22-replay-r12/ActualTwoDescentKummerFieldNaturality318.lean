module
public import ActualTwoDescentRootFieldNaturality318
public section
noncomputable section
namespace ActualTwoDescentKummerFieldNaturality318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentSimpleRootCoordinates318
open ActualTwoDescentRootKummerHom318 ActualTwoDescentKummerHom318
open ActualTwoDescentSquareClassFieldMap318 ActualTwoDescentActualEllipticFieldMap318
open ActualTwoDescentRootFieldNaturality318
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
variable [DecidableEq K] [DecidableEq L]

/-- Naturality for every actual point, including infinity and the three two-torsion roots. -/
theorem actual_kummer_field_naturality (f : K →+* L) (n : K) (hn : n ≠ 0) (P : Point n) :
    kummerClass (f n) (field_map_ne_zero f hn) (ellipticFieldMap f n hn P)=
      squarePairMap f (kummerClass n hn P) := by
  apply Prod.ext
  · change rootClass (firstRoot (f n) _) _=squareClassMap f (rootClass (firstRoot n hn) P)
    rw [←actual_first_root_map f n hn]
    exact actual_root_class_map f n hn (firstRoot n hn) P
  · change rootClass (secondRoot (f n) _) _=squareClassMap f (rootClass (secondRoot n hn) P)
    rw [←actual_second_root_map f n hn]
    exact actual_root_class_map f n hn (secondRoot n hn) P

/-- Actual scalar extension preserves divisibility by two, without assuming a local-to-global converse. -/
theorem actual_doubling_field_map (f : K →+* L) (n : K) (hn : n ≠ 0) (P : Point n)
    (h : ∃ Q : Point n, Q+Q=P) :
    ∃ Q : Point (f n), Q+Q=ellipticFieldMap f n hn P := by
  obtain ⟨Q,rfl⟩ := h
  exact ⟨ellipticFieldMap f n hn Q,(map_add _ Q Q).symm⟩

end ActualTwoDescentKummerFieldNaturality318
