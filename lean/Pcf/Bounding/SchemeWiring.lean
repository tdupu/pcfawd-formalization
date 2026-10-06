/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.SchemeExtraction
import Pcf.NormalizationDynamics
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Wiring actual scheme stalks into divisor dynamics

`PcfSetupChart` and `NormalizationPcfSetupChart` use an abstract critical set and an A6
field which sends membership in that set to non-étaleness on a chart.  That implication is
logically as strong as the desired bounding conclusion.

This file gives the noncircular replacement.  The unnormalized divisor carrier is the
actual type `SchemeDivisorPoint A`; its critical set is identified with non-formal-étaleness
of the actual stalk map of the iterate `g ^ m`; and the chart field supplies only a
`SchemeStalkBoundingLocalizationPresentation`: quotient-ring algebra maps to the actual
stalks, their localization properties, and their commutative square. The coordinate and
arrow isomorphisms and bounding conclusion are then theorems.

The remaining geometric construction is deliberately visible: one must construct the
local chart and the quotient-ring localization presentation from the original finite morphism.
No field below asserts that a critical point is non-étale on a chart, or that a point
outside the bound is étale.
-/

universe u v w

open CategoryTheory
open AlgebraicGeometry

namespace Pcf

set_option linter.style.haveILetI false

/-- The map on divisors induced by a scheme morphism, given the honest codimension-one
preservation statement. -/
def schemeDivisorMap {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (hcodim : ∀ x : SchemeDivisorPoint X, Order.coheight (g x.1) = 1) :
    SchemeDivisorPoint X → SchemeDivisorPoint Y :=
  fun x ↦ ⟨g x.1, hcodim x⟩

@[simp]
theorem schemeDivisorMap_val {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (hcodim : ∀ x : SchemeDivisorPoint X, Order.coheight (g x.1) = 1)
    (x : SchemeDivisorPoint X) :
    (schemeDivisorMap g hcodim x).1 = g x.1 :=
  rfl

/-- Iterating the divisor pushforward has the same underlying point as iterating the
actual scheme endomorphism. -/
theorem schemeDivisorMap_iterate_val {X : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ X)
    (hcodim : ∀ x : SchemeDivisorPoint X, Order.coheight (g x.1) = 1)
    (m : ℕ) (x : SchemeDivisorPoint X) :
    ((schemeDivisorMap g hcodim)^[m] x).1 =
      (CategoryTheory.End.of g ^ m).base x.1 := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, pow_succ]
      rw [ih (schemeDivisorMap g hcodim x)]
      exact (AlgebraicGeometry.Scheme.Hom.comp_apply g
        (CategoryTheory.End.of g ^ m) x.1).symm

/-- Normalized divisor dynamics together with the actual unnormalized scheme map.

Unlike `NormalizationUnnormDyn`, this structure does not contain an arbitrary `crit1`
field.  Its non-étale locus is fixed to be `schemeDivisorCrit1 (g ^ m)`.  The remaining
fields are the standard divisor and tower facts needed by the abstract dynamical proof. -/
structure SchemeNormalizationUnnormDyn (A : AlgebraicGeometry.Scheme.{u}) (PN : Type v) where
  /-- The actual self-map of the possibly nonnormal scheme. -/
  g : A ⟶ A
  /-- The actual self-map is finite, as in the manuscript. -/
  finite : AlgebraicGeometry.IsFinite g
  /-- The actual self-map is locally of finite presentation, so stalk formal étaleness
  is the intended pointwise étaleness criterion. -/
  finitePresentation : AlgebraicGeometry.LocallyOfFinitePresentation g
  /-- The self-map sends codimension-one points to codimension-one points. -/
  g_preserves_divisors : ∀ Q : SchemeDivisorPoint A,
    Order.coheight (g Q.1) = 1
  /-- The normalized divisorial dynamics. -/
  norm : DivDyn PN
  /-- Pushforward from normalized divisors to divisors of the actual scheme. -/
  normalization : PN → SchemeDivisorPoint A
  /-- Normalization commutes with divisor pushforward. -/
  normalization_step : ∀ Q, normalization (norm.step Q) =
    schemeDivisorMap g g_preserves_divisors (normalization Q)
  /-- The normalization map has finite fibers on divisors. -/
  normalization_finite_fiber : ∀ Q, (normalization ⁻¹' {Q}).Finite
  /-- The codimension-one non-unramified locus of each iterate. -/
  crit0 : ℕ → Set (SchemeDivisorPoint A)
  /-- Normalized ramification maps into the unnormalized non-unramified locus. -/
  crit_subset_crit0 : ∀ m Q, 1 < norm.iterRam m Q → normalization Q ∈ crit0 m
  /-- Formal étaleness implies unramifiedness. -/
  crit0_subset_crit1 : ∀ m,
    crit0 m ⊆ schemeDivisorCrit1 (CategoryTheory.End.of g ^ m)
  /-- The actual codimension-one non-étale locus has finitely many components. -/
  crit1_finite : ∀ m,
    (schemeDivisorCrit1 (CategoryTheory.End.of g ^ m)).Finite
  /-- Non-unramifiedness persists in the tower. -/
  crit0_tower : ∀ n, crit0 1 ⊆ crit0 (n + 1)
  /-- Non-étaleness in the first map of the tower persists in one factor. -/
  crit1_tower : ∀ n, ∀ Q ∈ schemeDivisorCrit1 (CategoryTheory.End.of g ^ 1),
    Q ∈ schemeDivisorCrit1 (CategoryTheory.End.of g ^ (n + 1)) ∨
      schemeDivisorMap g g_preserves_divisors Q ∈
        schemeDivisorCrit1 (CategoryTheory.End.of g ^ n)

namespace SchemeNormalizationUnnormDyn

variable {A : AlgebraicGeometry.Scheme.{u}} {PN : Type v}
  (D : SchemeNormalizationUnnormDyn A PN)

/-- Every categorical iterate of the actual self-map is finite. -/
theorem finite_iterate (m : ℕ) :
    AlgebraicGeometry.IsFinite (CategoryTheory.End.of D.g ^ m) := by
  letI : AlgebraicGeometry.IsFinite D.g := D.finite
  induction m with
  | zero => simpa using
      (inferInstance : AlgebraicGeometry.IsFinite (𝟙 A))
  | succ m ih =>
      rw [pow_succ]
      letI : AlgebraicGeometry.IsFinite (CategoryTheory.End.of D.g ^ m) := ih
      change AlgebraicGeometry.IsFinite (D.g ≫ (CategoryTheory.End.of D.g ^ m))
      infer_instance

/-- Every categorical iterate of the actual self-map is locally of finite presentation. -/
theorem finitePresentation_iterate (m : ℕ) :
    AlgebraicGeometry.LocallyOfFinitePresentation (CategoryTheory.End.of D.g ^ m) := by
  letI : AlgebraicGeometry.LocallyOfFinitePresentation D.g := D.finitePresentation
  induction m with
  | zero => simpa using
      (inferInstance : AlgebraicGeometry.LocallyOfFinitePresentation (𝟙 A))
  | succ m ih =>
      rw [pow_succ]
      letI : AlgebraicGeometry.LocallyOfFinitePresentation
          (CategoryTheory.End.of D.g ^ m) := ih
      change AlgebraicGeometry.LocallyOfFinitePresentation
        (D.g ≫ (CategoryTheory.End.of D.g ^ m))
      infer_instance

/-- The ordinary two-carrier dynamics obtained by forgetting that its critical loci came
from actual scheme stalk maps. -/
def toNormalizationUnnormDyn :
    NormalizationUnnormDyn PN (SchemeDivisorPoint A) where
  norm := D.norm
  step := schemeDivisorMap D.g D.g_preserves_divisors
  normalization := D.normalization
  normalization_step := D.normalization_step
  normalization_finite_fiber := D.normalization_finite_fiber
  crit0 := D.crit0
  crit1 := fun m ↦ schemeDivisorCrit1 (CategoryTheory.End.of D.g ^ m)
  crit_subset_crit0 := D.crit_subset_crit0
  crit0_subset_crit1 := D.crit0_subset_crit1
  crit1_finite := D.crit1_finite
  crit0_tower := D.crit0_tower
  crit1_tower := D.crit1_tower

@[simp]
theorem toNormalizationUnnormDyn_step :
    D.toNormalizationUnnormDyn.step = schemeDivisorMap D.g D.g_preserves_divisors :=
  rfl

@[simp]
theorem toNormalizationUnnormDyn_crit1 (m : ℕ) :
    D.toNormalizationUnnormDyn.crit1 m =
      schemeDivisorCrit1 (CategoryTheory.End.of D.g ^ m) :=
  rfl

end SchemeNormalizationUnnormDyn

/-- The chart route to Theorem `thm:normal-invariant` with an actual unnormalized
scheme and actual stalk-defined critical loci.

The ramification dynamics remains on the normalization carrier `PN`; divisors of the
possibly nonnormal invariant subscheme are literally `SchemeDivisorPoint A`. -/
structure SchemeNormalizationPcfSetupChart (A : AlgebraicGeometry.Scheme.{u})
    (PX : Type v) (PN : Type w) where
  /-- The ambient divisorial dynamics. -/
  amb : DivDyn PX
  /-- The invariant ambient divisor. -/
  fixedPrime : PX
  /-- Invariance of the ambient divisor. -/
  fixed : amb.step fixedPrime = fixedPrime
  /-- Normalized divisor dynamics over the actual unnormalized scheme. -/
  res : SchemeNormalizationUnnormDyn A PN
  /-- The singular correction terms. -/
  sing : Set (SchemeDivisorPoint A)
  /-- Finiteness of the singular correction terms. -/
  sing_finite : sing.Finite
  /-- Divisors of the restriction contained in an ambient divisor intersection. -/
  meets : PX → Set (SchemeDivisorPoint A)
  /-- Finiteness of a proper divisor intersection. -/
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- The noncircular chart link. It presents the two actual stalk rings of `g ^ m` as
  localizations of the quotient rings and proves the quotient-ring square commutes. The
  coordinate isomorphisms and arrow comparison are derived, and no non-étaleness
  implication is a field. -/
  chart : ∀ (m : ℕ), 1 ≤ m → ∀ (Q : SchemeDivisorPoint A), Q ∉ sing →
    (∀ E ∈ (amb.iter m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    ∀ (Q' : SchemeDivisorPoint A), res.toNormalizationUnnormDyn.step^[m] Q' = Q →
      SchemeStalkBoundingLocalizationPresentation
        (CategoryTheory.End.of res.g ^ m) Q'.1

local instance invariantStep0FinitePreimageAlgebra
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ X) [AlgebraicGeometry.IsFinite f]
    (m : ℕ) (U : X.affineOpens) :
    Algebra Γ(X, U)
      Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m) U) :=
  ((CategoryTheory.End.of f ^ m).app U).hom.toAlgebra

/-- Literal geometric Step-0 data at one divisor flag of an invariant reduced divisor.

The fields are the assertions made before Steps 1--4 of the manuscript's bounding
proof: an affine neighborhood, regularity exclusions, codimension two in the ambient
scheme, avoidance of every other branch component, and the two named local covering
theorems.  There is no field about formal étaleness, `crit₁`, a bounding chart, or the
conclusion of the bounding theorem. -/
structure InvariantDivisorStep0LocalData
    (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ X)
    [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsDominant f]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [IsNormalScheme X]
    (A : SchemeDivisorPoint X) (m : ℕ)
    (Q Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme) where
  /-- The affine neighborhood supplied by Step 0. -/
  U : X.affineOpens
  /-- Characteristic zero on its coordinate ring. -/
  rationalAlgebra : Algebra ℚ Γ(X, U)
  /-- The selected target divisor point belongs to the affine neighborhood. -/
  target_mem : (pointClosureIdealSheaf A.1).subschemeι Q.1 ∈ (U : X.Opens)
  /-- The specified source divisor point belongs to the finite affine preimage. -/
  source_mem : Q'.1 ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
    (finitePreimageAffine (CategoryTheory.End.of f ^ m) U : X.Opens)
  /-- A divisor of the invariant divisor has ambient codimension two. -/
  ambient_coheight : Order.coheight
    ((pointClosureIdealSheaf A.1).subschemeι Q.1) = 2
  /-- The target point is outside the ambient singular locus. -/
  ambient_regular : (pointClosureIdealSheaf A.1).subschemeι Q.1 ∉
    stalkSingularLocus X
  /-- The target point is outside the divisor singular locus. -/
  divisor_regular : Q.1 ∉ stalkSingularLocus
    (pointClosureIdealSheaf A.1).subscheme
  /-- The target point lies on no branch component of the ambient iterate other than
  the invariant divisor. -/
  branch_avoid :
    letI : Nonempty (U : X.Opens) :=
      ⟨⟨(pointClosureIdealSheaf A.1).subschemeι Q.1, target_mem⟩⟩
    letI : Nonempty
        (finitePreimageAffine (CategoryTheory.End.of f ^ m) U : X.Opens) :=
      ⟨⟨(pointClosureIdealSheaf A.1).subschemeι Q'.1, source_mem⟩⟩
    (⟨(pointClosureIdealSheaf A.1).subschemeι Q.1, target_mem⟩ : (U : X.Opens)) ∉
      finiteAffineOtherBranchLocus
        (f := CategoryTheory.End.of f ^ m) U
        (affinePrimeOfSchemeDivisorPoint A U
          (A.mem_affine_of_pointClosurePoint_mem U Q.1 target_mem))
  /-- Zariski--Nagata purity on the actual ambient iterate chart. -/
  purity : Stacks.ZariskiNagataPurity
    (Localization.AtPrime
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine (CategoryTheory.End.of f ^ m) U) Q'.1 source_mem).under
          Γ(X, U)))
    (Localization (Algebra.algebraMapSubmonoid
      Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m) U)
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine (CategoryTheory.End.of f ^ m) U) Q'.1 source_mem).under
          Γ(X, U)).primeCompl))
  /-- Abhyankar's lemma for the equation constructed by the regular-local argument. -/
  abhyankar : ∀ a : Localization.AtPrime
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine (CategoryTheory.End.of f ^ m) U) Q'.1 source_mem).under
          Γ(X, U)),
    Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine (CategoryTheory.End.of f ^ m) U) Q'.1 source_mem).under
            Γ(X, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m) U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine (CategoryTheory.End.of f ^ m) U) Q'.1 source_mem).under
            Γ(X, U)).primeCompl)) a

/-- Global dynamical data for an actual finite dominant endomorphism and an invariant
divisor, with only the literal Step-0 geometry left to supply pointwise.

The restricted self-map is required to equal the canonical map on the reduced point
closure.  The `localData` field contains no chart and no étaleness conclusion; the chart
is derived below from purity and Abhyankar. -/
structure InvariantDivisorSchemeNormalizationPcfSetup
    (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ X)
    [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsDominant f]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [IsNormalScheme X]
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1)
    (PX : Type v) (PN : Type w) where
  amb : DivDyn PX
  fixedPrime : PX
  fixed : amb.step fixedPrime = fixedPrime
  res : SchemeNormalizationUnnormDyn (pointClosureIdealSheaf A.1).subscheme PN
  /-- Identification of the stored restriction with the actual invariant-divisor map. -/
  res_g : res.g = A.invariantClosureMap f hA
  sing : Set (SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
  sing_finite : sing.Finite
  meets : PX → Set (SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- Step-0 geometry for every point tested by the bounding argument. -/
  localData : ∀ (m : ℕ), 1 ≤ m →
    ∀ (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme), Q ∉ sing →
    (∀ E ∈ (amb.iter m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    ∀ (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme),
      res.toNormalizationUnnormDyn.step^[m] Q' = Q →
      InvariantDivisorStep0LocalData X f A m Q Q'

namespace InvariantDivisorSchemeNormalizationPcfSetup

variable {X : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ X}
  [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsDominant f]
  [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
  [IsNormalScheme X]
  {A : SchemeDivisorPoint X} {hA : f A.1 = A.1}
  {PX : Type v} {PN : Type w}
  (S : InvariantDivisorSchemeNormalizationPcfSetup X f A hA PX PN)

/-- Construct the dynamics-facing chart setup from the actual ambient endomorphism,
invariant divisor, and literal Step-0 data. -/
noncomputable def toSchemeNormalizationPcfSetupChart :
    SchemeNormalizationPcfSetupChart
      (pointClosureIdealSheaf A.1).subscheme PX PN where
  amb := S.amb
  fixedPrime := S.fixedPrime
  fixed := S.fixed
  res := S.res
  sing := S.sing
  sing_finite := S.sing_finite
  meets := S.meets
  meets_finite := S.meets_finite
  chart := by
    intro m hm Q hs hmeets Q' hQ'Q
    let d := S.localData m hm Q hs hmeets Q' hQ'Q
    letI : Algebra ℚ Γ(X, d.U) := d.rationalAlgebra
    letI : Nonempty (d.U : X.Opens) :=
      ⟨⟨(pointClosureIdealSheaf A.1).subschemeι Q.1, d.target_mem⟩⟩
    letI : Nonempty
        (finitePreimageAffine (CategoryTheory.End.of f ^ m) d.U : X.Opens) :=
      ⟨⟨(pointClosureIdealSheaf A.1).subschemeι Q'.1, d.source_mem⟩⟩
    have hval := congrArg Subtype.val hQ'Q
    change ((schemeDivisorMap S.res.g S.res.g_preserves_divisors)^[m] Q').1 = Q.1
      at hval
    rw [schemeDivisorMap_iterate_val] at hval
    have hxz :
        (CategoryTheory.End.of (A.invariantClosureMap f hA) ^ m).base Q'.1 = Q.1 := by
      simpa only [← S.res_g] using hval
    have hresult :=
      A.invariantClosureStalkBoundingLocalizationOfStep0At
        f hA m d.U Q'.1 d.source_mem Q d.target_mem hxz
          d.ambient_coheight d.ambient_regular d.divisor_regular d.branch_avoid
          d.purity d.abhyankar
    simpa only [S.res_g] using hresult

end InvariantDivisorSchemeNormalizationPcfSetup

namespace SchemeNormalizationPcfSetupChart

variable {A : AlgebraicGeometry.Scheme.{u}} {PX : Type v} {PN : Type w}
  (S : SchemeNormalizationPcfSetupChart A PX PN)

/-- The bounding conclusion for actual divisors, derived from purity and Abhyankar on the
identified local stalk chart. -/
theorem key1 (m : ℕ) (hm : 1 ≤ m) (Q : SchemeDivisorPoint A) (hs : Q ∉ S.sing)
    (hmeets : ∀ E ∈ (S.amb.iter m).branch, E ≠ S.fixedPrime → Q ∉ S.meets E) :
    Q ∉ S.res.toNormalizationUnnormDyn.branch1 m := by
  rintro ⟨Q', hcrit, hQ'Q⟩
  have hchart := S.chart m hm Q hs hmeets Q' hQ'Q
  have hnot : Q' ∉ schemeDivisorCrit1 (CategoryTheory.End.of S.res.g ^ m) :=
    hchart.not_mem_schemeDivisorCrit1
  exact hnot hcrit

/-- Forget the explicit scheme and charts after deriving the bounding conclusion. -/
def toNormalizationPcfSetup :
    NormalizationPcfSetup PX PN (SchemeDivisorPoint A) where
  amb := S.amb
  fixedPrime := S.fixedPrime
  fixed := S.fixed
  res := S.res.toNormalizationUnnormDyn
  sing := S.sing
  sing_finite := S.sing_finite
  meets := S.meets
  meets_finite := S.meets_finite
  key1 := S.key1

/-- The unnormalized restriction is `1`-PCF on the actual-stalk chart route. -/
theorem res_pcf1 (h : S.amb.PCF) : S.res.toNormalizationUnnormDyn.PCF1 :=
  S.toNormalizationPcfSetup.res_pcf1 h

/-- The normalized restriction is PCF on the actual-stalk chart route. -/
theorem norm_pcf (h : S.amb.PCF) : S.res.norm.PCF :=
  S.toNormalizationPcfSetup.norm_pcf h

/-- Periodic-prime form of `norm_pcf`. -/
theorem norm_pcf_of_iter {D : DivDyn PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.amb = D.iter n) (h : D.PCF) : S.res.norm.PCF :=
  S.toNormalizationPcfSetup.norm_pcf_of_iter hn hS h

end SchemeNormalizationPcfSetupChart

namespace InvariantDivisorSchemeNormalizationPcfSetup

variable {X : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ X}
  [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsDominant f]
  [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
  [IsNormalScheme X]
  {A : SchemeDivisorPoint X} {hA : f A.1 = A.1}
  {PX : Type v} {PN : Type w}
  (S : InvariantDivisorSchemeNormalizationPcfSetup X f A hA PX PN)

/-- The bounding conclusion for the actual invariant-divisor restriction, derived from
the literal Step-0 package and the two named local covering inputs. -/
theorem key1 (m : ℕ) (hm : 1 ≤ m)
    (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (hs : Q ∉ S.sing)
    (hmeets : ∀ E ∈ (S.amb.iter m).branch,
      E ≠ S.fixedPrime → Q ∉ S.meets E) :
    Q ∉ S.res.toNormalizationUnnormDyn.branch1 m :=
  S.toSchemeNormalizationPcfSetupChart.key1 m hm Q hs hmeets

/-- The actual unnormalized invariant-divisor restriction is `1`-PCF. -/
theorem res_pcf1 (h : S.amb.PCF) : S.res.toNormalizationUnnormDyn.PCF1 :=
  S.toSchemeNormalizationPcfSetupChart.res_pcf1 h

/-- The normalized invariant-divisor dynamics is PCF. -/
theorem norm_pcf (h : S.amb.PCF) : S.res.norm.PCF :=
  S.toSchemeNormalizationPcfSetupChart.norm_pcf h

/-- Periodic-prime form of the normalized PCF conclusion. -/
theorem norm_pcf_of_iter {D : DivDyn PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.amb = D.iter n) (h : D.PCF) : S.res.norm.PCF :=
  S.toSchemeNormalizationPcfSetupChart.norm_pcf_of_iter hn hS h

end InvariantDivisorSchemeNormalizationPcfSetup

end Pcf
