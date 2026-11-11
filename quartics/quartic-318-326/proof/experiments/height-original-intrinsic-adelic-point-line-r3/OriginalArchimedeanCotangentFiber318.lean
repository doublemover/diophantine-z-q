module
public import OriginalArchimedeanFrameNorm318
public import BranchOriginalCoordinate318
public section
noncomputable section
namespace OriginalArchimedeanCotangentFiber318
open NumberField OriginalPointFinitePlaceRoots318 OriginalArchimedeanMarkedPoint318
open OriginalArchimedeanSectionCoefficient318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)
    (w : InfinitePlace (K c t)) (i : Fin 4)
abbrev A := ContactBicanonicalCoefficients318.BranchRing c i
abbrev Omega := KaehlerDifferential ℚ (A c i)
@[expose] def point : A c i →+* ℂ := w.embedding.comp (ContactBranchPoint318.branchPoint c t hn i)

/-- The coordinate normalizing the ORIGINAL intrinsic algebraic frame is
literally the SAME original marked root used in the analytic derivative. -/
lemma point_coordinate : point c t hn w i (ContactFrameNormalization318.sourceCoordinate c i)=
    markedRoot c t w i := by
  rw [BranchOriginalCoordinate318.coordinate_eq_root]
  change w.embedding (ContactBranchPoint318.branchPoint c t hn i
    (algebraMap (ContactKummerOrder318.SourceOrder c) (A c i)
      (ContactRootReciprocals318.root c i)))=_
  rw [ContactBranchPoint318.branchPoint_algebraMap]
  change w.embedding (RationalContactPoint318.sourcePoint c t
    (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i))=_
  rw [←OriginalPointFinitePlaceRoots318.roots_original]
  rfl

/-- Entire intrinsic algebraic cotangent fiber evaluated in the genuine
analytic t tangent direction. Actual scalar point and original normalized
frame are retained; this is a semilinear map on ALL differentials. -/
@[expose] def differential : Omega c i →ₛₗ[point c t hn w i] ℂ where
  toFun ω := point c t hn w i (ContactDifferentialFrames318.sourceLocalizationFrame c i ω)*
    branchDerivative c t w i
  map_add' ω η := by simp only [map_add,add_mul]
  map_smul' a ω := by simp only [map_smul,smul_eq_mul,map_mul];ring

lemma differential_coordinate : differential c t hn w i
    (KaehlerDifferential.D ℚ (A c i) (ContactFrameNormalization318.sourceCoordinate c i))=
      branchDerivative c t w i := by
  change point c t hn w i (ContactDifferentialFrames318.sourceLocalizationFrame c i _)*_=_
  rw [ContactFrameNormalization318.source_coordinate_normalized,map_one,one_mul]

/-- The SAME map sends d(t) to1, consistent with the literal t chart and
not merely a scalar chosen from the two section values. -/
lemma differential_parameter : differential c t hn w i
    (KaehlerDifferential.D ℚ (A c i) (ContactBicanonicalCoefficients318.branchT c i))=1 := by
  rw [ContactBranchDifferential318.D_branchT,LinearMap.map_smulₛₗ,differential_coordinate]
  simp only [smul_eq_mul,map_mul,map_ofNat,map_ratCast,point_coordinate]
  rw [branchDerivative]
  have hr := markedRoot_ne c t hn w i
  have hc : ((c i:ℚ):ℂ)≠0 := Rat.cast_ne_zero.mpr (Units.ne_zero _)
  push_cast
  field_simp

/-- Every differential is the actual original coordinate differential
multiplied by its original normalized frame coefficient. -/
lemma differential_all (ω : Omega c i) :
    differential c t hn w i ω=point c t hn w i
      (ContactDifferentialFrames318.sourceLocalizationFrame c i ω)*
        differential c t hn w i
          (KaehlerDifferential.D ℚ (A c i) (ContactFrameNormalization318.sourceCoordinate c i)) := by
  rw [differential_coordinate]
  rfl
end OriginalArchimedeanCotangentFiber318
