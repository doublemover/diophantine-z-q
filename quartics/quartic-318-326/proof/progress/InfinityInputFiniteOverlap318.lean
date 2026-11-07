module
public import InfinityInputScheme318
public import InfinityInputFractions318
public import RelativeChordScheme318
public section
noncomputable section
namespace InfinityInputFiniteOverlap318
open InfinityInputAlgebra318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Actual quotient-algebra agreement with ordinary chord addition on the genuine finite
input overlap. The premises are solely literal input-coordinate transition identities. -/
theorem output_maps_agree (A B:R) (φ:OutputRing A B →ₐ[R] S)
    (γ:RelativeChordAlgebra318.ChordRing A B →ₐ[R] S)
    (hu:φ (pairMap A B (u A B))=γ (RelativeChordAlgebra318.x1 A B)*φ (pairMap A B (v A B)))
    (hv:γ (RelativeChordAlgebra318.y1 A B)*φ (pairMap A B (v A B))=1)
    (hx:φ (pairMap A B (x A B))=γ (RelativeChordAlgebra318.x2 A B))
    (hy:φ (pairMap A B (y A B))=γ (RelativeChordAlgebra318.y2 A B)) :
    φ.comp (outputMap A B)=γ.comp (RelativeChordAlgebra318.chordMap A B) := by
  let f:=φ.comp (pairMap A B)
  have hm (a:PairRing A B) (n:ℕ) : f (a^n)=(f a)^n := by
    induction n with
    | zero =>
        simp only [pow_zero]
        exact f.toRingHom.map_one
    | succ n ih => simp only [pow_succ,map_mul,ih]
  have h1 : f 1=1 := f.toRingHom.map_one
  have h2 : f 2=2 := map_natCast f.toRingHom 2
  have h3 : f 3=3 := map_natCast f.toRingHom 3
  have h4 : f 4=4 := map_natCast f.toRingHom 4
  have hF:=congrArg f (right_relation A B)
  have hG:=congrArg f (left_relation A B)
  simp only [map_sub,map_mul,hm,map_zero,coeff,Algebra.ofId_apply,AlgHom.commutes] at hF hG
  have hH : f (denominator A B)=InfinityInputPolynomial318.denominator
      (1-algebraMap R S A*f (u A B)*f (v A B)-algebraMap R S B*f (v A B)^2)
      (f (u A B)) (f (x A B)) := by
    simp only [denominator,InfinityInputPolynomial318.denominator,parameter,map_sub,map_mul,
      hm,h1,coeff,Algebra.ofId_apply,AlgHom.commutes]
  have hNX : f (numeratorX A B)=InfinityInputPolynomial318.numeratorX (algebraMap R S A) (algebraMap R S B)
      (1-algebraMap R S A*f (u A B)*f (v A B)-algebraMap R S B*f (v A B)^2)
      (f (u A B)) (f (x A B)) (f (y A B)) := by
    simp only [numeratorX,InfinityInputPolynomial318.numeratorX,parameter,map_sub,map_mul,map_add,
      hm,h1,h2,h3,h4,coeff,Algebra.ofId_apply,AlgHom.commutes]
  have hNY : f (numeratorY A B)=InfinityInputPolynomial318.numeratorY (algebraMap R S A) (algebraMap R S B)
      (1-algebraMap R S A*f (u A B)*f (v A B)-algebraMap R S B*f (v A B)^2)
      (f (u A B)) (f (x A B)) (f (y A B)) := by
    simp only [numeratorY,InfinityInputPolynomial318.numeratorY,parameter,map_sub,map_mul,map_add,
      hm,h1,h2,h3,h4,coeff,Algebra.ofId_apply,AlgHom.commutes]
  have hXi : f (v A B)*(f (x A B)*f (v A B)-f (u A B))^2*f (numeratorX A B)=
      f (denominator A B)^2*(f (v A B)*(f (y A B)*f (v A B)-1)^2-
        (f (u A B)+f (x A B)*f (v A B))*(f (x A B)*f (v A B)-f (u A B))^2) := by
    rw [hH,hNX]
    exact InfinityInputChordIdentities318.x_identity _ _ _ _ _ _ hF hG
  have hYi : f (v A B)*(f (x A B)*f (v A B)-f (u A B))*f (numeratorY A B)=
      (f (y A B)*f (v A B)-1)*f (denominator A B)*
        (f (u A B)*f (denominator A B)^2-f (v A B)*f (numeratorX A B))-
      (f (x A B)*f (v A B)-f (u A B))*f (denominator A B)^3 := by
    rw [hH,hNX,hNY]
    exact InfinityInputChordIdentities318.y_identity _ _ _ _ _ _ hF hG
  have hv' : f (v A B)*γ (RelativeChordAlgebra318.y1 A B)=1 := by rw [mul_comm]; exact hv
  have hk : f (denominator A B)*φ (↑(denominatorUnit A B)⁻¹)=1 := by
    have hh:=congrArg φ (Units.mul_inv (denominatorUnit A B))
    simpa only [map_mul,map_one,denominatorUnit,IsUnit.unit_spec,f,AlgHom.comp_apply] using hh
  have hd : IsUnit (f (x A B)*f (v A B)-f (u A B)) := by
    apply InfinityInputFractions318.chord_denominator_unit _ _ _ _ _ hG
    · exact IsUnit.of_mul_eq_one _ hv'
    · rw [←hH]
      exact (denominator_unit A B).map φ
  have hs:=congrArg γ (RelativeChordAlgebra318.slope_identity A B)
  simp only [map_mul,map_sub] at hs
  have hl : γ (RelativeChordAlgebra318.slope A B)*(f (x A B)*f (v A B)-f (u A B))=
      f (y A B)*f (v A B)-1 := by
    change γ (RelativeChordAlgebra318.slope A B)*(φ (pairMap A B (x A B))*φ (pairMap A B (v A B))-
      φ (pairMap A B (u A B)))=φ (pairMap A B (y A B))*φ (pairMap A B (v A B))-1
    rw [hx,hy,hu]
    linear_combination φ (pairMap A B (v A B))*hs-hv
  have hux : f (u A B)*γ (RelativeChordAlgebra318.y1 A B)=γ (RelativeChordAlgebra318.x1 A B) := by
    change φ (pairMap A B (u A B))*γ (RelativeChordAlgebra318.y1 A B)=_
    rw [hu]
    calc
      _=γ (RelativeChordAlgebra318.x1 A B)*(γ (RelativeChordAlgebra318.y1 A B)*φ (pairMap A B (v A B))) := by ring
      _=_ := by rw [hv,mul_one]
  obtain ⟨hxo,hyo⟩:=InfinityInputFractions318.chord_coordinates _ _ _ _ _ _ _ _ _ _ _ hv' hk hd hl hXi hYi
  have hfx : f (x A B)=γ (RelativeChordAlgebra318.x2 A B) := hx
  rw [hux,hfx] at hxo
  rw [hux,hxo] at hyo
  apply AffineEquationFunctor318.hom_ext
  · simp only [AlgHom.comp_apply,outputMap_x,outX,map_mul,map_pow,RelativeChordAlgebra318.chordMap_x,
      RelativeChordAlgebra318.x3,map_sub]
    exact hxo
  · simp only [AlgHom.comp_apply,outputMap_y,outY,map_mul,map_pow,RelativeChordAlgebra318.chordMap_y,
      RelativeChordAlgebra318.y3,RelativeChordAlgebra318.x3,map_sub]
    exact hyo

open AlgebraicGeometry CategoryTheory in
/-- The corresponding actual Scheme morphisms agree, with the same explicit input transition. -/
theorem scheme_agreement (A B:R) (φ:OutputRing A B →ₐ[R] S)
    (γ:RelativeChordAlgebra318.ChordRing A B →ₐ[R] S)
    (hu:φ (pairMap A B (u A B))=γ (RelativeChordAlgebra318.x1 A B)*φ (pairMap A B (v A B)))
    (hv:γ (RelativeChordAlgebra318.y1 A B)*φ (pairMap A B (v A B))=1)
    (hx:φ (pairMap A B (x A B))=γ (RelativeChordAlgebra318.x2 A B))
    (hy:φ (pairMap A B (y A B))=γ (RelativeChordAlgebra318.y2 A B)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ InfinityInputScheme318.addition A B=
      Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B := by
  dsimp only [InfinityInputScheme318.addition,InfinityInputScheme318.finiteAddition,
    RelativeChordScheme318.addition,RelativeChordScheme318.chordOpen,ShortAffineScheme318.scheme]
  rw [←Category.assoc,←Category.assoc,←Spec.map_comp,←Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (output_maps_agree A B φ γ hu hv hx hy))

end InfinityInputFiniteOverlap318
