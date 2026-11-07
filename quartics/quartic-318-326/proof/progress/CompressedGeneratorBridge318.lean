module
public import GlobalGeneratorPoints318
public import CompressedTranslation318
public section
namespace CompressedGeneratorBridge318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A transparent curve-equality transport, preserving the actual group. -/
def transport {A B:WeierstrassCurve.Affine K} (h:A=B) : A.Point≃+B.Point := by
  subst h
  exact AddEquiv.refl _

theorem transport_some {A B:WeierstrassCurve.Affine K} (h:A=B) (x y:K)
    (ha:A.Nonsingular x y) :
    transport h (Point.some x y ha)=Point.some x y (by simpa only [←h] using ha) := by
  subst h; rfl

theorem curve_eq : CompressedPoint318.E=LocalGenerator318.E := by
  ext <;> norm_num [CompressedPoint318.E,LocalGenerator318.E,CompressedOrientation318.D,D,i,pair,pow_succ]

theorem generator_eq : transport curve_eq CompressedTranslation318.P=LocalGenerator318.P := by
  rw [CompressedTranslation318.P,transport_some,LocalGenerator318.P,Point.some.injEq]
  constructor <;> ext <;> norm_num [CompressedOrientation318.k,CompressedOrientation318.m,xP,yP,pair,pow_succ]

/-- The locally reconstructed H−V=P equation now uses exactly the same
actual group and generator as the global and anchor packages. -/
theorem source_translation (S:ℚ) (w:CircuitReplay.Assignment)
    (source:CircuitReplay.Constraints (Raw318FinalReplay.stage0 S) w) :
    transport curve_eq (CompressedTranslation318.H S w source)-
      transport curve_eq (CompressedTranslation318.V S w source)=P := by
  rw [←map_sub,CompressedTranslation318.source_translation,generator_eq]

end CompressedGeneratorBridge318
