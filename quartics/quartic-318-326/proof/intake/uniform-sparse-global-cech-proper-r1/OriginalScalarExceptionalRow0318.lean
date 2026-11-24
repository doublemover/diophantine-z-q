module
public import OriginalScalarExceptionalMap318
public section
namespace OriginalScalarExceptionalRows318
open OriginalMarkedIntPolynomialCertificate318 OriginalRadixHZCertificate318
open OriginalScalarProjectiveObstruction318 OriginalScalarExceptionalMap318
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
@[expose] def f1 : List ℤ := [-2,11,-52,25,2]
@[expose] def g1 : List ℤ := [11640522536041,-30633518512715622,-37915542547983705591,-35582750263712855144088,2530531419379922376295056]
@[expose] def q1 : List ℤ := [180685600824235665130812433288396800000000,-3082948064063521036294487142983270400000000,6095315815305075015897250679213260800000000,17146781196968676752687333024641843200000000,-46639470712755831061890959342567424000000000,-38470505306741363920390869096942796800000000,101454964862808325970951181291434803200000000,82314995631747299537289573612080332800000000,-4212233069214993943362064851035750400000000,-23566766451254800229366512294920192000000000,-9720320681841303047584175122061721600000000,-1818148858293871380378800109964492800000000,-180685600824235665130812433288396800000000]
theorem proj1 : ∀ a b : ZMod 5, a≠0 ∨ b≠0 → homog (a^2) (b^2) g1≠0 := by decide +kernel
theorem cert1 {K : Type*} [CommRing K] (z : K) : Ev z (condition f1 g1 q1)=0 := by
  exact certificate z (2^158) _ (by decide +kernel) (by decide +kernel)
theorem nz1 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f1≠0 :=
  excludes z x hd hz _ _ _ (cert1 z) (no_rat_square 5 (by decide) _ proj1 x)
 @[expose] def f2 : List ℤ := [2,1]
@[expose] def g2 : List ℤ := [-343,160089]
@[expose] def q2 : List ℤ := [0,12259094400,-24518188800]
theorem proj2 : ∀ a b : ZMod 5, a≠0 ∨ b≠0 → homog (a^2) (b^2) g2≠0 := by decide +kernel
theorem cert2 {K : Type*} [CommRing K] (z : K) : Ev z (condition f2 g2 q2)=0 := by
  exact certificate z (2^39) _ (by decide +kernel) (by decide +kernel)
theorem nz2 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f2≠0 :=
  excludes z x hd hz _ _ _ (cert2 z) (no_rat_square 5 (by decide) _ proj2 x)
 @[expose] def f3 : List ℤ := [5,2]
@[expose] def g3 : List ℤ := [-288463,606849]
@[expose] def q3 : List ℤ := [-294218265600,4241646662400,-8471034230400,-735545664000]
theorem proj3 : ∀ a b : ZMod 5, a≠0 ∨ b≠0 → homog (a^2) (b^2) g3≠0 := by decide +kernel
theorem cert3 {K : Type*} [CommRing K] (z : K) : Ev z (condition f3 g3 q3)=0 := by
  exact certificate z (2^49) _ (by decide +kernel) (by decide +kernel)
theorem nz3 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f3≠0 :=
  excludes z x hd hz _ _ _ (cert3 z) (no_rat_square 5 (by decide) _ proj3 x)
 @[expose] def f4 : List ℤ := [-1,2,1]
@[expose] def g4 : List ℤ := [-686,40953]
@[expose] def q4 : List ℤ := [3064773600,-42906830400,-3064773600]
theorem proj4 : ∀ a b : ZMod 5, a≠0 ∨ b≠0 → homog (a^2) (b^2) g4≠0 := by decide +kernel
theorem cert4 {K : Type*} [CommRing K] (z : K) : Ev z (condition f4 g4 q4)=0 := by
  exact certificate z (2^40) _ (by decide +kernel) (by decide +kernel)
theorem nz4 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f4≠0 :=
  excludes z x hd hz _ _ _ (cert4 z) (no_rat_square 5 (by decide) _ proj4 x)
 @[expose] def f5 : List ℤ := [-1,12,5]
@[expose] def g5 : List ℤ := [-343,4964]
@[expose] def q5 : List ℤ := [1702652000,-4086364800,-340530400]
theorem proj5 : ∀ a b : ZMod 3, a≠0 ∨ b≠0 → homog (a^2) (b^2) g5≠0 := by decide +kernel
theorem cert5 {K : Type*} [CommRing K] (z : K) : Ev z (condition f5 g5 q5)=0 := by
  exact certificate z (2^39) _ (by decide +kernel) (by decide +kernel)
theorem nz5 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f5≠0 :=
  excludes z x hd hz _ _ _ (cert5 z) (no_rat_square 3 (by decide) _ proj5 x)
 @[expose] def f6 : List ℤ := [-21,44,21]
@[expose] def g6 : List ℤ := [-12691,59568]
@[expose] def q6 : List ℤ := [3064773600,-36777283200,-3064773600]
theorem proj6 : ∀ a b : ZMod 5, a≠0 ∨ b≠0 → homog (a^2) (b^2) g6≠0 := by decide +kernel
theorem cert6 {K : Type*} [CommRing K] (z : K) : Ev z (condition f6 g6 q6)=0 := by
  exact certificate z (2^44) _ (by decide +kernel) (by decide +kernel)
theorem nz6 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f6≠0 :=
  excludes z x hd hz _ _ _ (cert6 z) (no_rat_square 5 (by decide) _ proj6 x)
 @[expose] def f7 : List ℤ := [1,-14,23,14,1]
@[expose] def g7 : List ℤ := [-2401,3723]
@[expose] def q7 : List ℤ := [-12259094400]
theorem proj7 : ∀ a b : ZMod 5, a≠0 ∨ b≠0 → homog (a^2) (b^2) g7≠0 := by decide +kernel
theorem cert7 {K : Type*} [CommRing K] (z : K) : Ev z (condition f7 g7 q7)=0 := by
  exact certificate z (2^42) _ (by decide +kernel) (by decide +kernel)
theorem nz7 {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ) (hd : horner z dd≠0)
    (hz : horner z nn=(x:K)^2*horner z vv) : horner z f7≠0 :=
  excludes z x hd hz _ _ _ (cert7 z) (no_rat_square 5 (by decide) _ proj7 x)
end OriginalScalarExceptionalRows318
#print axioms OriginalScalarExceptionalRows318.nz1
#print axioms OriginalScalarExceptionalRows318.nz2
#print axioms OriginalScalarExceptionalRows318.nz3
#print axioms OriginalScalarExceptionalRows318.nz4
#print axioms OriginalScalarExceptionalRows318.nz5
#print axioms OriginalScalarExceptionalRows318.nz6
#print axioms OriginalScalarExceptionalRows318.nz7
