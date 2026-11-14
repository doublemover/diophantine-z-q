module
public import ActualOriginalPositiveCountAsymptotic318
public section
noncomputable section
namespace ActualOriginalPositiveRayScaling318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalPositiveRealPoint318 ActualOriginalRealGoodRegion318

@[expose] def scaleCoordinates {R : Type*} [CommRing R] (d : R) (x : Coordinates R) : Coordinates R :=
  ((d*x.1.1,d*x.1.2),(d*x.2.1.1,d*x.2.1.2),d*x.2.2)
lemma actual_scale_one {R : Type*} [CommRing R] (x : Coordinates R) : scaleCoordinates 1 x=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩,w⟩
  simp only [scaleCoordinates,one_mul]
lemma actual_scale_mul {R : Type*} [CommRing R] (a b : R) (x : Coordinates R) :
    scaleCoordinates a (scaleCoordinates b x)=scaleCoordinates (a*b) x := by
  rcases x with ⟨⟨x0,x1⟩,⟨x2,x3⟩,x4⟩
  simp only [scaleCoordinates,mul_assoc]
lemma actual_equation_scale {R : Type*} [CommRing R] (κ d : R) (x : Coordinates R) :
    equation κ (scaleCoordinates d x)=d^2*equation κ x := by
  dsimp [equation,scaleCoordinates]
  ring
lemma actual_integer_scale_embed (d : ℤ) (x : Coordinates ℤ) :
    integerEmbed (scaleCoordinates d x)=scaleCoordinates (d : ℝ) (integerEmbed x) := by
  simp [integerEmbed,scaleCoordinates]
lemma actual_real_scale_smul (d : ℝ) (x : Coordinates ℝ) : scaleCoordinates d x=d • x := by
  rcases x with ⟨⟨a,b⟩,⟨c,e⟩,w⟩
  rfl
lemma actual_form_scale (γ d : ℝ) (x : Coordinates ℝ) :
    originalForm γ (scaleCoordinates d x)=d^2*originalForm γ x := by
  dsimp [originalForm,scaleCoordinates]
  ring

/-- Every original positive form and coordinate is preserved in BOTH
directions along a positive ray. This does not preserve primality. -/
lemma actual_region_scale_iff {J : Type*} [Fintype J] (γ : J → ℝ)
    (d : ℝ) (hd : 0<d) (x : Coordinates ℝ) : scaleCoordinates d x∈region γ ↔ x∈region γ := by
  simp only [region,Set.mem_setOf_eq,scaleCoordinates]
  have hsq := sq_pos_of_pos hd
  have hf (j : J) : originalForm (γ j) ((d*x.1.1,d*x.1.2),(d*x.2.1.1,d*x.2.1.2),d*x.2.2)=
      d^2*originalForm (γ j) x := actual_form_scale (γ j) d x
  simp_rw [hf,mul_pos_iff_of_pos_left hd,mul_pos_iff_of_pos_left hsq]

end ActualOriginalPositiveRayScaling318
