module
public import FourRootAutomorphisms318
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Algebraic.Integral
public section
noncomputable section
namespace InfinityFieldCoordinates318
attribute [-instance] DivisionRing.toRatAlgebra
set_option maxHeartbeats 900000
open Polynomial
variable (c:Fin 4→ℚˣ)
abbrev K:=RatFunc ℚ
abbrev L:=KummerTensorField318.Raw (SourceKummerField318.parameter c)
local instance actualField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
@[expose] def root (i:Fin 4) : L c := FourRootAutomorphisms318.generator (SourceKummerField318.parameter c) i
@[expose] def t : L c := algebraMap K (L c) RatFunc.X
@[expose] def constant (q:ℚ) : L c := algebraMap ℚ (L c) q
@[expose] def u : L c := constant c (c 0:ℚ)/root c 0
@[expose] def ratio (j:Fin 3) : L c := root c j.succ/root c 0

theorem root_ne_zero (i:Fin 4) : root c i≠0 :=
  FourRootAutomorphisms318.generator_ne_zero _ i

theorem root_square (i:Fin 4) : root c i^2=
    constant c (c i:ℚ)*(t c-constant c (LinearContactSquareclass318.contacts i)) := by
  rw [root,FourRootAutomorphisms318.generator_square]
  simp only [SourceKummerField318.parameter,map_mul,map_sub,RatFunc.algebraMap_C,RatFunc.algebraMap_X,←RatFunc.algebraMap_eq_C]
  change _=algebraMap ℚ (L c) (c i:ℚ)*(t c-algebraMap ℚ (L c) (LinearContactSquareclass318.contacts i))
  rw [←IsScalarTower.algebraMap_apply ℚ K (L c),←IsScalarTower.algebraMap_apply ℚ K (L c)]
  rfl

theorem root_zero_square : root c 0^2=constant c (c 0:ℚ)*t c := by
  simpa [LinearContactSquareclass318.contacts,constant] using root_square c 0

theorem constant_ne_zero {q:ℚ} (hq:q≠0) : constant c q≠0 := by
  simpa only [constant,map_zero] using (algebraMap ℚ (L c)).injective.ne hq

theorem t_ne_zero : t c≠0 := by
  simpa only [t,map_zero] using (algebraMap K (L c)).injective.ne RatFunc.X_ne_zero

theorem u_ne_zero : u c≠0 := div_ne_zero (constant_ne_zero c (c 0).ne_zero) (root_ne_zero c 0)

theorem u_square : u c^2=constant c (c 0:ℚ)/t c := by
  rw [u,div_pow,root_zero_square]
  field_simp [constant_ne_zero c (c 0).ne_zero,t_ne_zero c]

theorem reciprocal_contact_square : (t c)⁻¹=
    constant c (↑((c 0)⁻¹):ℚ)*u c^2 := by
  rw [u_square]
  have hc:constant c (↑((c 0)⁻¹):ℚ)*constant c (c 0:ℚ)=1 := by
    rw [constant,constant,←map_mul,Units.inv_mul,map_one]
  field_simp [t_ne_zero c]
  exact hc.symm

theorem ratio_square (j:Fin 3) : ratio c j^2=
    constant c ((c j.succ:ℚ)/(c 0:ℚ))*
      (1-constant c (LinearContactSquareclass318.contacts j.succ/(c 0:ℚ))*u c^2) := by
  rw [ratio,div_pow,root_square,root_zero_square,u_square]
  simp only [constant,map_div₀]
  have hc : algebraMap ℚ (L c) (c 0:ℚ)≠0 := constant_ne_zero c (c 0).ne_zero
  field_simp [hc,t_ne_zero c]

theorem recover_t : t c=constant c (c 0:ℚ)/u c^2 := by
  rw [u_square]
  field_simp [t_ne_zero c,constant_ne_zero c (c 0).ne_zero]

theorem recover_root_zero : root c 0=constant c (c 0:ℚ)/u c := by
  rw [u]
  field_simp [root_ne_zero c 0,constant_ne_zero c (c 0).ne_zero]

theorem recover_root (j:Fin 3) : root c j.succ=
    constant c (c 0:ℚ)/u c*ratio c j := by
  rw [←recover_root_zero,ratio]
  field_simp [root_ne_zero c 0]
end InfinityFieldCoordinates318

namespace InfinityFieldCoordinates318
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance actualField2 : Field (L c):=(KummerTensorField318.source_raw_field c).toField

theorem t_transcendental : Transcendental ℚ (t c) :=
  (transcendental_algebraMap_iff (algebraMap K (L c)).injective).mpr RatFunc.transcendental_X

theorem u_transcendental : Transcendental ℚ (u c) := by
  intro hu
  apply t_transcendental c
  rw [recover_t,div_eq_mul_inv]
  exact (isAlgebraic_algebraMap (c 0:ℚ)).mul (hu.pow 2).inv

theorem polynomial_coordinate_injective :
    Function.Injective (Polynomial.aeval (u c):Polynomial ℚ→ₐ[ℚ]L c) :=
  transcendental_iff_injective.mp (u_transcendental c)

/-- The genuine rational-function field of the infinity coordinate embeds
in the already constructed original contact function field. -/
@[expose] def coordinateField : RatFunc ℚ→ₐ[ℚ]L c :=
  RatFunc.liftAlgHom (Polynomial.aeval (u c))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polynomial_coordinate_injective c))
end InfinityFieldCoordinates318
