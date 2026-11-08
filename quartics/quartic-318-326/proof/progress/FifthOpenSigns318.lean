module
public import FixedCoordinateFrameFunctor318
public import FifthInvariantScalar318
public import ContactDifferentialCharacters318
public section
noncomputable section
namespace FifthOpenSigns318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthOverlapCoordinates318 FifthInvariantScalar318
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField:Field L:=(KummerTensorField318.source_raw_field units).toField
local instance rawCharZero:CharZero L:=Algebra.charZero_of_charZero (RatFunc ℚ) L
/-- Q-linear version of the literal entire unbranched source sign map. -/
@[expose] def sign (b:Fin 4→Bool):O→ₐ[ℚ]O:=
  { (ContactGlobalSigns318.openEquiv units b).toRingHom with
    commutes':=RingHom.map_rat_algebraMap _ }
lemma sign_t (b:Fin 4→Bool):sign b t=t:=by
  change ContactGlobalSigns318.openEquiv units b
    (algebraMap ContactKummerOrder318.OpenBase O
      (algebraMap (Polynomial ℚ) ContactKummerOrder318.OpenBase Polynomial.X))=_
  exact (ContactGlobalSigns318.openEquiv units b).commutes _
@[expose] def epsilon (b:Fin 4→Bool):ℚ:=∏i:Fin 4,if b i then -1 else 1
lemma epsilon_square (b:Fin 4→Bool):epsilon b^2=1:=by
  rw [epsilon,←Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  split_ifs <;> norm_num
lemma sign_full_root (b:Fin 4→Bool):
    FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b
      FifthCharacterField318.root=algebraMap ℚ L (epsilon b)*FifthCharacterField318.root:=by
  rw [FifthCharacterField318.root,CharacterRoot318.sign_action]
  congr 1
  change algebraMap (RatFunc ℚ) L (∏i:Fin 4,if b i then -1 else 1)=
    algebraMap ℚ L (∏i:Fin 4,if b i then -1 else 1)
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp only [map_neg,map_one]
lemma sign_full_inverse (b:Fin 4→Bool):
    FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b
      FifthCharacterField318.root⁻¹=algebraMap ℚ L (epsilon b)*FifthCharacterField318.root⁻¹:=by
  rw [map_inv₀,sign_full_root,mul_inv_rev]
  have he:(algebraMap ℚ L (epsilon b))⁻¹=algebraMap ℚ L (epsilon b):=by
    apply inv_eq_of_mul_eq_one_left
    rw [←map_mul,←pow_two,epsilon_square,map_one]
  rw [he,mul_comm]
/-- Differential pullback on the exact entire common chart respects the dt
frame through the actual original root-sign field action. -/
theorem raw_pullback (b:Fin 4→Bool) (ω:KaehlerDifferential ℚ O):
    SourceOpenFractionField318.openEmbedding units
      (ContactUnbranchedDifferentialFrame318.frame units (AlgHomDifferential318.map (sign b) ω))=
    FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b
      (SourceOpenFractionField318.openEmbedding units
        (ContactUnbranchedDifferentialFrame318.frame units ω)):=by
  rw [FixedCoordinateFrameFunctor318.map_frame (ContactUnbranchedDifferentialFrame318.frame units)
    t (by rw [t_coordinate];exact ContactUnbranchedDifferentialFrame318.frame_D units)
      (sign b) (sign_t b)]
  exact SourceSignFieldComparison318.open_embedding units b _
end FifthOpenSigns318
