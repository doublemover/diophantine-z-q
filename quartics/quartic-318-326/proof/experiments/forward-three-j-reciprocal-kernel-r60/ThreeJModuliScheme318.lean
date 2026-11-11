module
public import ThreeJArithmeticAlgebraMap318
public section
noncomputable section
namespace ThreeJModuliScheme318
open AlgebraicGeometry CategoryTheory Polynomial
open ThreeJModuliOpen318 ThreeJArithmeticAlgebraMap318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Source := Spec (CommRingCat.of Ring)
abbrev Target := Spec (CommRingCat.of Fixed)
@[expose] def toLaurent : Source ⟶ Spec (CommRingCat.of ThreeJLaurentEquiv318.Laurent) :=
  Spec.map (CommRingCat.ofHom inclusion.toRingHom)
instance toLaurent_open : IsOpenImmersion toLaurent := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap ThreeJLaurentEquiv318.Laurent Ring)))
  infer_instance
@[expose] def embedding : Source ⟶ ProjectiveJLine318.scheme ℚ :=
  toLaurent ≫ ProjectiveLineOverlap318.embedding
instance embedding_open : IsOpenImmersion embedding := by unfold embedding; infer_instance

/-- An actual morphism into the original integral diamond quotient after
rational open base change. No analytification or scheme isomorphism is assumed. -/
@[expose] def arithmeticMap : Source ⟶ Target :=
  Spec.map (CommRingCat.ofHom fixedMap)
@[expose] def targetStructure : Target ⟶ OpenJAffineScheme318.baseScheme 3 :=
  Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base 3) Fixed))
@[expose] def baseMorphism : Source ⟶ OpenJAffineScheme318.baseScheme 3 :=
  Spec.map (CommRingCat.ofHom ThreeJModuliOpen318.baseMap)

theorem arithmetic_base_square : arithmeticMap ≫ targetStructure=baseMorphism := by
  rw [arithmeticMap,targetStructure,baseMorphism,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fixedMap_base

@[expose] def rationalJ : Source ⟶ Spec (CommRingCat.of (Polynomial ℚ)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) j).toRingHom)

/-- The rational j map used for the literal family is precisely the
restriction of the constructed global projective j morphism. -/
theorem global_j_square : embedding ≫ ThreeProjectiveJMap318.map=
    rationalJ ≫ JLineAtlas318.chart ℚ 1 := by
  rw [embedding,Category.assoc,ThreeJFiniteLaurentMap318.original_scheme_square,
    ←Category.assoc]
  congr 1
  rw [toLaurent,ThreeJFiniteLaurentMap318.finiteTargetMap,←Spec.map_comp]
  unfold rationalJ
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro q
    change inclusion (ThreeJLaurentEquiv318.baseMap (Polynomial.C q))=
      Polynomial.aeval (R:=ℚ) j (Polynomial.C q)
    rw [ThreeJLaurentEquiv318.baseMap,Polynomial.aeval_C,Polynomial.aeval_C] <;>
      exact inclusion.commutes q
  · change inclusion (ThreeJLaurentEquiv318.baseMap Polynomial.X)=
      Polynomial.aeval (R:=ℚ) j Polynomial.X
    rw [ThreeJLaurentEquiv318.baseMap,Polynomial.aeval_X,Polynomial.aeval_X]
    rfl

/-- The actual source open is D(j(j-1728)) inside the original Laurent chart. -/
theorem source_open_range : toLaurent.opensRange=PrimeSpectrum.basicOpen deleted := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range Ring deleted

end ThreeJModuliScheme318
