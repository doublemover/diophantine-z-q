module
public import OriginalScalarExceptionalMap318
public section
namespace OriginalScalarExceptionalRows318
open OriginalMarkedIntPolynomialCertificate318 OriginalRadixHZCertificate318
open OriginalScalarProjectiveObstruction318 OriginalScalarExceptionalMap318
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
@[expose] def f18 : List ℤ := [-1,10,4]
@[expose] def g18 : List ℤ := [343,18615]
@[expose] def q18 : List ℤ := [-1961455104,4903637760,490363776]
theorem proj18 : ∀ a b : ZMod 13, a≠0 ∨ b≠0 → homog (a^2) (b^2) g18≠0 := by decide +kernel
theorem cert18 {K : Type*} [CommRing K] (z : K) : Ev z (condition f18 g18 q18)=0 := by
  exact certificate z (2^39) _ (by decide +kernel) (by decide +kernel)
theorem nz18 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f18≠0 :=
  excludes z x hd hz _ _ _ (cert18 z) (no_rat_square 13 (by decide) _ proj18 x)
 @[expose] def f19 : List ℤ := [-4,21,9]
@[expose] def g19 : List ℤ := [437771929,131234882541,565573186116]
@[expose] def q19 : List ℤ := [-4733989958505507840000,81041399527749050880000,-322174316620513728000000,274458703546688371200000,230124511871795520000000,42155053440025236480000,2103995537113559040000]
theorem proj19 : ∀ a b : ZMod 5, a≠0 ∨ b≠0 → homog (a^2) (b^2) g19≠0 := by decide +kernel
theorem cert19 {K : Type*} [CommRing K] (z : K) : Ev z (condition f19 g19 q19)=0 := by
  exact certificate z (2^87) _ (by decide +kernel) (by decide +kernel)
theorem nz19 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f19≠0 :=
  excludes z x hd hz _ _ _ (cert19 z) (no_rat_square 5 (by decide) _ proj19 x)
 @[expose] def f20 : List ℤ := [-19,41,19]
@[expose] def g20 : List ℤ := [1715,48399]
@[expose] def q20 : List ℤ := [-490363776,5394001536,490363776]
theorem proj20 : ∀ a b : ZMod 11, a≠0 ∨ b≠0 → homog (a^2) (b^2) g20≠0 := by decide +kernel
theorem cert20 {K : Type*} [CommRing K] (z : K) : Ev z (condition f20 g20 q20)=0 := by
  exact certificate z (2^41) _ (by decide +kernel) (by decide +kernel)
theorem nz20 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f20≠0 :=
  excludes z x hd hz _ _ _ (cert20 z) (no_rat_square 11 (by decide) _ proj20 x)
 @[expose] def f21 : List ℤ := [-4,46,19]
@[expose] def g21 : List ℤ := [181447,197319]
@[expose] def q21 : List ℤ := [-232922793600,563918342400,49036377600]
theorem proj21 : ∀ a b : ZMod 5, a≠0 ∨ b≠0 → homog (a^2) (b^2) g21≠0 := by decide +kernel
theorem cert21 {K : Type*} [CommRing K] (z : K) : Ev z (condition f21 g21 q21)=0 := by
  exact certificate z (2^48) _ (by decide +kernel) (by decide +kernel)
theorem nz21 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f21≠0 :=
  excludes z x hd hz _ _ _ (cert21 z) (no_rat_square 5 (by decide) _ proj21 x)
 @[expose] def f22 : List ℤ := [-37,78,37]
@[expose] def g22 : List ℤ := [11662,26499]
@[expose] def q22 : List ℤ := [-1622527200,19109764800,1622527200]
theorem proj22 : ∀ a b : ZMod 5, a≠0 ∨ b≠0 → homog (a^2) (b^2) g22≠0 := by decide +kernel
theorem cert22 {K : Type*} [CommRing K] (z : K) : Ev z (condition f22 g22 q22)=0 := by
  exact certificate z (2^44) _ (by decide +kernel) (by decide +kernel)
theorem nz22 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f22≠0 :=
  excludes z x hd hz _ _ _ (cert22 z) (no_rat_square 5 (by decide) _ proj22 x)
 @[expose] def f23 : List ℤ := [9,-14,13,8]
@[expose] def g23 : List ℤ := [40353607,82783365903,1027027791673128,103206988134000]
@[expose] def q23 : List ℤ := [73694514019010925118095360000,-967240496499518392175001600000,1321895345216008469305835520000,-4099257342307482709694054400000,9492774587073844791774658560000,8603834511719525507537633280000,7484599080055797082306560000000,1685762008184874912076431360000,1082388174654222962672025600000,82906328271387290757857280000]
theorem proj23 : ∀ a b : ZMod 11, a≠0 ∨ b≠0 → homog (a^2) (b^2) g23≠0 := by decide +kernel
theorem cert23 {K : Type*} [CommRing K] (z : K) : Ev z (condition f23 g23 q23)=0 := by
  exact certificate z (2^113) _ (by decide +kernel) (by decide +kernel)
theorem nz23 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f23≠0 :=
  excludes z x hd hz _ _ _ (cert23 z) (no_rat_square 11 (by decide) _ proj23 x)
 @[expose] def f24 : List ℤ := [1,15,-38,-15,1]
@[expose] def g24 : List ℤ := [-588245,514626567,221771664]
@[expose] def q24 : List ℤ := [13525685595730022400,-175833912744490291200,159302519238598041600,175833912744490291200,13525685595730022400]
theorem proj24 : ∀ a b : ZMod 11, a≠0 ∨ b≠0 → homog (a^2) (b^2) g24≠0 := by decide +kernel
theorem cert24 {K : Type*} [CommRing K] (z : K) : Ev z (condition f24 g24 q24)=0 := by
  exact certificate z (2^78) _ (by decide +kernel) (by decide +kernel)
theorem nz24 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f24≠0 :=
  excludes z x hd hz _ _ _ (cert24 z) (no_rat_square 11 (by decide) _ proj24 x)
 @[expose] def f25 : List ℤ := [7,-96,158,96,7]
@[expose] def g25 : List ℤ := [1372,11169]
@[expose] def q25 : List ℤ := [1021591200]
theorem proj25 : ∀ a b : ZMod 5, a≠0 ∨ b≠0 → homog (a^2) (b^2) g25≠0 := by decide +kernel
theorem cert25 {K : Type*} [CommRing K] (z : K) : Ev z (condition f25 g25 q25)=0 := by
  exact certificate z (2^41) _ (by decide +kernel) (by decide +kernel)
theorem nz25 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f25≠0 :=
  excludes z x hd hz _ _ _ (cert25 z) (no_rat_square 5 (by decide) _ proj25 x)
end OriginalScalarExceptionalRows318
#print axioms OriginalScalarExceptionalRows318.nz18
#print axioms OriginalScalarExceptionalRows318.nz19
#print axioms OriginalScalarExceptionalRows318.nz20
#print axioms OriginalScalarExceptionalRows318.nz21
#print axioms OriginalScalarExceptionalRows318.nz22
#print axioms OriginalScalarExceptionalRows318.nz23
#print axioms OriginalScalarExceptionalRows318.nz24
#print axioms OriginalScalarExceptionalRows318.nz25
