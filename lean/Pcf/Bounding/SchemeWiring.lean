/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeExtraction
public import Pcf.Bounding.CriticalLoci
public import Pcf.NormalizationDynamics
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.RingHom.Unramified

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

@[expose] public section

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

/-- A quasi-finite quasi-compact scheme morphism has finite fibers on its
codimension-one point map whenever it preserves codimension one. -/
theorem schemeDivisorMap_finite_fiber {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [AlgebraicGeometry.LocallyQuasiFinite g]
    [AlgebraicGeometry.QuasiCompact g]
    (hcodim : ∀ x : SchemeDivisorPoint X, Order.coheight (g x.1) = 1)
    (y : SchemeDivisorPoint Y) :
    (schemeDivisorMap g hcodim ⁻¹' {y}).Finite := by
  change ((fun x : SchemeDivisorPoint X ↦
    (⟨g x.1, hcodim x⟩ : SchemeDivisorPoint Y)) ⁻¹' {y}).Finite
  exact Pcf.Scheme.Hom.finite_divisorPoint_subtype_fiber g hcodim y

/-- A commuting square of scheme morphisms induces a commuting square on
codimension-one points. -/
theorem schemeDivisorMap_comm_of_comm
    {X Y : AlgebraicGeometry.Scheme.{u}}
    (fX : X ⟶ X) (fY : Y ⟶ Y) (nu : X ⟶ Y)
    (hfX : ∀ x : SchemeDivisorPoint X, Order.coheight (fX x.1) = 1)
    (hfY : ∀ y : SchemeDivisorPoint Y, Order.coheight (fY y.1) = 1)
    (hnu : ∀ x : SchemeDivisorPoint X, Order.coheight (nu x.1) = 1)
    (hsquare : fX ≫ nu = nu ≫ fY) (x : SchemeDivisorPoint X) :
    schemeDivisorMap nu hnu (schemeDivisorMap fX hfX x) =
      schemeDivisorMap fY hfY (schemeDivisorMap nu hnu x) := by
  apply Subtype.ext
  change nu (fX x.1) = fY (nu x.1)
  simpa only [AlgebraicGeometry.Scheme.Hom.comp_apply] using
    congrArg (fun h : X ⟶ Y ↦ h x.1) hsquare

/-- Iterating the divisor pushforward has the same underlying point as iterating the
actual scheme endomorphism. -/
theorem schemeDivisorMap_iterate_val {X : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ X)
    (hcodim : ∀ x : SchemeDivisorPoint X, Order.coheight (g x.1) = 1)
    (m : ℕ) (x : SchemeDivisorPoint X) :
    ((schemeDivisorMap g hcodim)^[m] x).1 =
      (CategoryTheory.End.of g ^ m).asHom.base x.1 := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, pow_succ]
      rw [ih (schemeDivisorMap g hcodim x)]
      exact (AlgebraicGeometry.Scheme.Hom.comp_apply g
        (CategoryTheory.End.of g ^ m).asHom x.1).symm

set_option backward.isDefEq.respectTransparency false in
/-- Failure of formal unramifiedness in the first morphism persists in a composite. -/
theorem schemeCrit0At_comp {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (hx : schemeCrit0At f x) :
    schemeCrit0At (f ≫ g) x := by
  intro hc
  apply hx
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hc
  exact RingHom.FormallyUnramified.of_comp hc

/-- The actual stalk-defined non-unramified divisor locus persists along iterates (U4). -/
theorem schemeDivisorCrit0_tower {A : AlgebraicGeometry.Scheme.{u}} (g : A ⟶ A)
    (n : ℕ) :
    schemeDivisorCrit0 (CategoryTheory.End.of g ^ 1).asHom ⊆
      schemeDivisorCrit0 (CategoryTheory.End.of g ^ (n + 1)).asHom := by
  rw [pow_one, pow_succ]
  intro Q hQ
  exact schemeCrit0At_comp g (CategoryTheory.End.of g ^ n).asHom Q.1 hQ

set_option backward.isDefEq.respectTransparency false in
/-- If the first morphism is not formally étale at a point, either the composite fails
there or the second morphism fails at its image. This follows from cancellation of
formal étaleness over a formally unramified ring map. -/
theorem schemeCrit1At_comp {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (hx : schemeCrit1At f x) :
    schemeCrit1At (f ≫ g) x ∨ schemeCrit1At g (f x) := by
  by_contra h
  simp only [schemeCrit1At, not_or, not_not] at h
  have hu : (g.stalkMap (f x)).hom.FormallyUnramified := by
    letI := (g.stalkMap (f x)).hom.toAlgebra
    letI : Algebra.FormallyEtale (Z.presheaf.stalk (g (f x)))
        (Y.presheaf.stalk (f x)) := h.2
    exact (inferInstance : Algebra.FormallyUnramified
      (Z.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)))
  have hc := h.1
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hc
  exact hx (RingHom.FormallyEtale.of_comp hu hc)

/-- The actual stalk-defined non-étale divisor locus satisfies the tower implication
U5. Only preservation of the divisor carrier is needed. -/
theorem schemeDivisorCrit1_tower {A : AlgebraicGeometry.Scheme.{u}} (g : A ⟶ A)
    (hcodim : ∀ Q : SchemeDivisorPoint A, Order.coheight (g Q.1) = 1)
    (n : ℕ) (Q : SchemeDivisorPoint A)
    (hQ : Q ∈ schemeDivisorCrit1 (CategoryTheory.End.of g ^ 1).asHom) :
    Q ∈ schemeDivisorCrit1 (CategoryTheory.End.of g ^ (n + 1)).asHom ∨
      schemeDivisorMap g hcodim Q ∈ schemeDivisorCrit1 (CategoryTheory.End.of g ^ n).asHom := by
  have hx : schemeCrit1At g Q.1 := by simpa [schemeDivisorCrit1] using hQ
  rw [pow_succ]
  change schemeCrit1At (g ≫ (CategoryTheory.End.of g ^ n).asHom) Q.1 ∨
    schemeCrit1At (CategoryTheory.End.of g ^ n).asHom (g Q.1)
  exact schemeCrit1At_comp g (CategoryTheory.End.of g ^ n).asHom Q.1 hx

/-- Normalized divisor dynamics together with the actual unnormalized scheme map.

Unlike `NormalizationUnnormalizedDynamics`, this structure has no arbitrary critical loci. Its
non-unramified and non-étale loci are defined from the actual stalk maps of `g ^ m`.
The inclusion U2, finiteness U3, and tower implications U4 and U5 are theorems.
Normalized ramification comparison U1 remains a field. Finiteness follows from
integrality, Noetherianity, dominance, local finite presentation, and characteristic
zero at the generic stalk; generic formal étaleness of every iterate is derived. -/
structure SchemeNormalizationUnnormDyn (A : AlgebraicGeometry.Scheme.{u}) (PN : Type v) where
  /-- The actual self-map of the possibly nonnormal scheme. -/
  g : A ⟶ A
  /-- The actual self-map is finite, as in the manuscript. -/
  finite : AlgebraicGeometry.IsFinite g
  /-- The actual self-map is dominant, as in the manuscript. -/
  dominant : AlgebraicGeometry.IsDominant g
  /-- The actual self-map is locally of finite presentation, so stalk formal étaleness
  is the intended pointwise étaleness criterion. -/
  finitePresentation : AlgebraicGeometry.LocallyOfFinitePresentation g
  /-- The self-map sends codimension-one points to codimension-one points. -/
  g_preserves_divisors : ∀ Q : SchemeDivisorPoint A,
    Order.coheight (g Q.1) = 1
  /-- The normalized divisorial dynamics. -/
  norm : DivisorDynamics PN
  /-- Pushforward from normalized divisors to divisors of the actual scheme. -/
  normalization : PN → SchemeDivisorPoint A
  /-- Normalization commutes with divisor pushforward. -/
  normalization_step : ∀ Q, normalization (norm.step Q) =
    schemeDivisorMap g g_preserves_divisors (normalization Q)
  /-- The normalization map has finite fibers on divisors. -/
  normalization_finite_fiber : ∀ Q, (normalization ⁻¹' {Q}).Finite
  /-- Normalized ramification maps into the unnormalized non-unramified locus. -/
  crit_subset_crit0 : ∀ m Q, 1 < norm.iterateRamificationIdx m Q →
    normalization Q ∈ schemeDivisorCrit0 (CategoryTheory.End.of g ^ m).asHom
  /-- The invariant divisor is integral. -/
  integral : AlgebraicGeometry.IsIntegral A
  /-- The invariant divisor has Noetherian underlying space. -/
  noetherian : TopologicalSpace.NoetherianSpace A
  /-- Characteristic zero at the generic point. For a finite dominant self-map this
  makes the finite generic field extension separable, hence formally étale. -/
  charZero : CharZero (A.presheaf.stalk (genericPoint A))

namespace SchemeNormalizationUnnormDyn

variable {A : AlgebraicGeometry.Scheme.{u}} {PN : Type v}
  (D : SchemeNormalizationUnnormDyn A PN)

/-- The codimension-one non-unramified locus of each actual iterate. -/
def crit0 (m : ℕ) : Set (SchemeDivisorPoint A) :=
  schemeDivisorCrit0 (CategoryTheory.End.of D.g ^ m).asHom

/-- Formal étaleness implies formal unramifiedness on the actual stalk maps. -/
theorem crit0_subset_crit1 (m : ℕ) :
    D.crit0 m ⊆ schemeDivisorCrit1 (CategoryTheory.End.of D.g ^ m).asHom :=
  schemeDivisorCrit0_subset_crit1 (CategoryTheory.End.of D.g ^ m).asHom

/-- Non-unramifiedness persists in the tower of actual stalk maps. -/
theorem crit0_tower (n : ℕ) : D.crit0 1 ⊆ D.crit0 (n + 1) :=
  schemeDivisorCrit0_tower D.g n

/-- Non-étaleness in the first map of the tower persists in one factor. This is a
theorem about the actual stalk maps, rather than a field of the geometric data. -/
theorem crit1_tower (n : ℕ)
    (Q : SchemeDivisorPoint A)
    (hQ : Q ∈ schemeDivisorCrit1 (CategoryTheory.End.of D.g ^ 1).asHom) :
    Q ∈ schemeDivisorCrit1 (CategoryTheory.End.of D.g ^ (n + 1)).asHom ∨
      schemeDivisorMap D.g D.g_preserves_divisors Q ∈
        schemeDivisorCrit1 (CategoryTheory.End.of D.g ^ n).asHom :=
  schemeDivisorCrit1_tower D.g D.g_preserves_divisors n Q hQ

/-- Every categorical iterate of the actual self-map is finite. -/
theorem finite_iterate (m : ℕ) :
    AlgebraicGeometry.IsFinite (CategoryTheory.End.of D.g ^ m).asHom := by
  letI : AlgebraicGeometry.IsFinite D.g := D.finite
  induction m with
  | zero => simpa using
      (inferInstance : AlgebraicGeometry.IsFinite (𝟙 A))
  | succ m ih =>
      rw [pow_succ]
      letI : AlgebraicGeometry.IsFinite (CategoryTheory.End.of D.g ^ m).asHom := ih
      change AlgebraicGeometry.IsFinite (D.g ≫ (CategoryTheory.End.of D.g ^ m).asHom)
      infer_instance

/-- Every categorical iterate of the actual self-map is locally of finite presentation. -/
theorem finitePresentation_iterate (m : ℕ) :
    AlgebraicGeometry.LocallyOfFinitePresentation (CategoryTheory.End.of D.g ^ m).asHom := by
  letI : AlgebraicGeometry.LocallyOfFinitePresentation D.g := D.finitePresentation
  induction m with
  | zero => simpa using
      (inferInstance : AlgebraicGeometry.LocallyOfFinitePresentation (𝟙 A))
  | succ m ih =>
      rw [pow_succ]
      letI : AlgebraicGeometry.LocallyOfFinitePresentation
          (CategoryTheory.End.of D.g ^ m).asHom := ih
      change AlgebraicGeometry.LocallyOfFinitePresentation
        (D.g ≫ (CategoryTheory.End.of D.g ^ m).asHom)
      infer_instance

/-- The actual codimension-one non-étale locus of every iterate is finite (U3).
Closedness follows from local finite presentation; a formally étale stalk makes
that closed locus proper. -/
theorem crit1_finite (m : ℕ) :
    (schemeDivisorCrit1 (CategoryTheory.End.of D.g ^ m).asHom).Finite := by
  letI : AlgebraicGeometry.IsIntegral A := D.integral
  letI : TopologicalSpace.NoetherianSpace A := D.noetherian
  letI : AlgebraicGeometry.IsFinite D.g := D.finite
  letI : AlgebraicGeometry.IsDominant D.g := D.dominant
  letI : LocallyOfFinitePresentation D.g := D.finitePresentation
  letI : CharZero (A.presheaf.stalk (genericPoint A)) := D.charZero
  letI : LocallyOfFinitePresentation (CategoryTheory.End.of D.g ^ m).asHom :=
    D.finitePresentation_iterate m
  have hgeneric : (D.g.stalkMap (genericPoint A)).hom.FormallyEtale :=
    formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero D.g
  have hetale := exists_formallyEtale_stalk_iterate_of_exists
    D.g ⟨genericPoint A, hgeneric⟩ m
  exact schemeDivisorCrit1_finite_of_exists_formallyEtale
    (CategoryTheory.End.of D.g ^ m).asHom hetale

/-- The ordinary two-carrier dynamics obtained by forgetting that its critical loci came
from actual scheme stalk maps. -/
def toNormalizationUnnormalizedDynamics :
    NormalizationUnnormalizedDynamics PN (SchemeDivisorPoint A) where
  normalized := D.norm
  step := schemeDivisorMap D.g D.g_preserves_divisors
  normalization := D.normalization
  normalization_step := D.normalization_step
  normalization_finite_fiber := D.normalization_finite_fiber
  nonUnramifiedLocus := D.crit0
  nonEtaleLocus := fun m ↦ schemeDivisorCrit1 (CategoryTheory.End.of D.g ^ m).asHom
  mem_nonUnramifiedLocus_of_one_lt_ramificationIdx := D.crit_subset_crit0
  nonUnramifiedLocus_subset_nonEtaleLocus := D.crit0_subset_crit1
  nonEtaleLocus_finite := D.crit1_finite
  nonUnramifiedLocus_tower := D.crit0_tower
  nonEtaleLocus_tower := D.crit1_tower

@[simp]
theorem toNormalizationUnnormDyn_step :
    D.toNormalizationUnnormalizedDynamics.step = schemeDivisorMap D.g D.g_preserves_divisors :=
  rfl

@[simp]
theorem toNormalizationUnnormDyn_crit1 (m : ℕ) :
    D.toNormalizationUnnormalizedDynamics.nonEtaleLocus m =
      schemeDivisorCrit1 (CategoryTheory.End.of D.g ^ m).asHom :=
  rfl

end SchemeNormalizationUnnormDyn

/-- The chart route to Theorem `thm:normal-invariant` with an actual unnormalized
scheme and actual stalk-defined critical loci.

The ramification dynamics remains on the normalization carrier `PN`; divisors of the
possibly nonnormal invariant subscheme are literally `SchemeDivisorPoint A`. -/
structure SchemeNormalizationPcfSetupChart (A : AlgebraicGeometry.Scheme.{u})
    (PX : Type v) (PN : Type w) where
  /-- The ambient divisorial dynamics. -/
  amb : DivisorDynamics PX
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
    (∀ E ∈ (amb.iterate m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    ∀ (Q' : SchemeDivisorPoint A), res.toNormalizationUnnormalizedDynamics.step^[m] Q' = Q →
      SchemeStalkBoundingLocalizationPresentation
        (CategoryTheory.End.of res.g ^ m).asHom Q'.1

local instance invariantStep0FinitePreimageAlgebra
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ X) [AlgebraicGeometry.IsFinite f]
    (m : ℕ) (U : X.affineOpens) :
    Algebra Γ(X, U)
      Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) :=
  ((CategoryTheory.End.of f ^ m).asHom.app U).hom.toAlgebra

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
    (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens)
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
        (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens) :=
      ⟨⟨(pointClosureIdealSheaf A.1).subschemeι Q'.1, source_mem⟩⟩
    (⟨(pointClosureIdealSheaf A.1).subschemeι Q.1, target_mem⟩ : (U : X.Opens)) ∉
      finiteAffineOtherBranchLocus
        (f := (CategoryTheory.End.of f ^ m).asHom) U
        (affinePrimeOfSchemeDivisorPoint A U
          (A.mem_affine_of_pointClosurePoint_mem U Q.1 target_mem))
  /-- Zariski--Nagata purity on the actual ambient iterate chart. -/
  purity : Stacks.ZariskiNagataPurity
    (Localization.AtPrime
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) Q'.1 source_mem).under
          Γ(X, U)))
    (Localization (Algebra.algebraMapSubmonoid
      Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U)
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) Q'.1 source_mem).under
          Γ(X, U)).primeCompl))
  /-- Abhyankar's lemma for the equation constructed by the regular-local argument. -/
  abhyankar : ∀ a : Localization.AtPrime
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) Q'.1 source_mem).under
          Γ(X, U)),
    Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) Q'.1 source_mem).under
            Γ(X, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) Q'.1 source_mem).under
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
  amb : DivisorDynamics PX
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
    (∀ E ∈ (amb.iterate m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    ∀ (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme),
      res.toNormalizationUnnormalizedDynamics.step^[m] Q' = Q →
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
        (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom d.U : X.Opens) :=
      ⟨⟨(pointClosureIdealSheaf A.1).subschemeι Q'.1, d.source_mem⟩⟩
    have hval := congrArg Subtype.val hQ'Q
    change ((schemeDivisorMap S.res.g S.res.g_preserves_divisors)^[m] Q').1 = Q.1
      at hval
    rw [schemeDivisorMap_iterate_val] at hval
    have hxz :
        (CategoryTheory.End.of (A.invariantClosureMap f hA) ^ m).asHom.base Q'.1 = Q.1 := by
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
    (hmeets : ∀ E ∈ (S.amb.iterate m).branch, E ≠ S.fixedPrime → Q ∉ S.meets E) :
    Q ∉ S.res.toNormalizationUnnormalizedDynamics.nonEtaleBranch m := by
  rintro ⟨Q', hcrit, hQ'Q⟩
  have hchart := S.chart m hm Q hs hmeets Q' hQ'Q
  have hnot : Q' ∉ schemeDivisorCrit1 (CategoryTheory.End.of S.res.g ^ m).asHom :=
    hchart.not_mem_schemeDivisorCrit1
  exact hnot hcrit

/-- Forget the explicit scheme and charts after deriving the bounding conclusion. -/
def toNormalizationPCFSetup :
    NormalizationPCFSetup PX PN (SchemeDivisorPoint A) where
  ambient := S.amb
  fixedPrime := S.fixedPrime
  fixed := S.fixed
  restriction := S.res.toNormalizationUnnormalizedDynamics
  singularPrimes := S.sing
  singularPrimes_finite := S.sing_finite
  meets := S.meets
  meets_finite := S.meets_finite
  notMem_nonEtaleBranch_iterate := S.key1

/-- The unnormalized restriction is `1`-PCF on the actual-stalk chart route. -/
theorem res_pcf1 (h : S.amb.IsPCF) : S.res.toNormalizationUnnormalizedDynamics.IsNonEtaleBranchPCF :=
  S.toNormalizationPCFSetup.restriction_isNonEtaleBranchPCF h

/-- The normalized restriction is PCF on the actual-stalk chart route. -/
theorem norm_pcf (h : S.amb.IsPCF) : S.res.norm.IsPCF :=
  S.toNormalizationPCFSetup.normalized_isPCF h

/-- Periodic-prime form of `norm_pcf`. -/
theorem norm_pcf_of_iter {D : DivisorDynamics PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.amb = D.iterate n) (h : D.IsPCF) : S.res.norm.IsPCF :=
  S.toNormalizationPCFSetup.normalized_isPCF_of_iterate hn hS h

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
    (hmeets : ∀ E ∈ (S.amb.iterate m).branch,
      E ≠ S.fixedPrime → Q ∉ S.meets E) :
    Q ∉ S.res.toNormalizationUnnormalizedDynamics.nonEtaleBranch m :=
  S.toSchemeNormalizationPcfSetupChart.key1 m hm Q hs hmeets

/-- The actual unnormalized invariant-divisor restriction is `1`-PCF. -/
theorem res_pcf1 (h : S.amb.IsPCF) : S.res.toNormalizationUnnormalizedDynamics.IsNonEtaleBranchPCF :=
  S.toSchemeNormalizationPcfSetupChart.res_pcf1 h

/-- The normalized invariant-divisor dynamics is PCF. -/
theorem norm_pcf (h : S.amb.IsPCF) : S.res.norm.IsPCF :=
  S.toSchemeNormalizationPcfSetupChart.norm_pcf h

/-- Periodic-prime form of the normalized PCF conclusion. -/
theorem norm_pcf_of_iter {D : DivisorDynamics PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.amb = D.iterate n) (h : D.IsPCF) : S.res.norm.IsPCF :=
  S.toSchemeNormalizationPcfSetupChart.norm_pcf_of_iter hn hS h

end InvariantDivisorSchemeNormalizationPcfSetup

end Pcf
