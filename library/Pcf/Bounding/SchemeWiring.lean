/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
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

`PCFSetupChart` and `NormalizationPCFSetupChart` use an abstract critical set and an A6
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
  exact AlgebraicGeometry.Scheme.Hom.finite_divisorPoint_subtype_fiber g hcodim y

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
theorem schemeStalkNotFormallyUnramifiedAt_comp {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (hx : SchemeStalkNotFormallyUnramifiedAt f x) :
    SchemeStalkNotFormallyUnramifiedAt (f ≫ g) x := by
  intro hc
  apply hx
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hc
  exact RingHom.FormallyUnramified.of_comp hc

/-- The actual stalk-defined non-unramified divisor locus persists along iterates (U4). -/
theorem schemeDivisorNonUnramifiedLocus_tower {A : AlgebraicGeometry.Scheme.{u}} (g : A ⟶ A)
    (n : ℕ) :
    schemeDivisorNonUnramifiedLocus (CategoryTheory.End.of g ^ 1).asHom ⊆
      schemeDivisorNonUnramifiedLocus (CategoryTheory.End.of g ^ (n + 1)).asHom := by
  rw [pow_one, pow_succ]
  intro Q hQ
  exact schemeStalkNotFormallyUnramifiedAt_comp g (CategoryTheory.End.of g ^ n).asHom Q.1 hQ

set_option backward.isDefEq.respectTransparency false in
/-- If the first morphism is not formally étale at a point, either the composite fails
there or the second morphism fails at its image. This follows from cancellation of
formal étaleness over a formally unramified ring map. -/
theorem schemeStalkNotFormallyEtaleAt_comp {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (hx : SchemeStalkNotFormallyEtaleAt f x) :
    SchemeStalkNotFormallyEtaleAt (f ≫ g) x ∨ SchemeStalkNotFormallyEtaleAt g (f x) := by
  by_contra h
  simp only [SchemeStalkNotFormallyEtaleAt, not_or, not_not] at h
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
theorem schemeDivisorNonEtaleLocus_tower {A : AlgebraicGeometry.Scheme.{u}} (g : A ⟶ A)
    (hcodim : ∀ Q : SchemeDivisorPoint A, Order.coheight (g Q.1) = 1)
    (n : ℕ) (Q : SchemeDivisorPoint A)
    (hQ : Q ∈ schemeDivisorNonEtaleLocus (CategoryTheory.End.of g ^ 1).asHom) :
    Q ∈ schemeDivisorNonEtaleLocus (CategoryTheory.End.of g ^ (n + 1)).asHom ∨
      schemeDivisorMap g hcodim Q ∈ schemeDivisorNonEtaleLocus
          (CategoryTheory.End.of g ^ n).asHom := by
  have hx : SchemeStalkNotFormallyEtaleAt g Q.1 := by simpa [schemeDivisorNonEtaleLocus] using hQ
  rw [pow_succ]
  change SchemeStalkNotFormallyEtaleAt (g ≫ (CategoryTheory.End.of g ^ n).asHom) Q.1 ∨
    SchemeStalkNotFormallyEtaleAt (CategoryTheory.End.of g ^ n).asHom (g Q.1)
  exact schemeStalkNotFormallyEtaleAt_comp g (CategoryTheory.End.of g ^ n).asHom Q.1 hx

/-- Normalized divisor dynamics together with the actual unnormalized scheme map.

Unlike `NormalizationUnnormalizedDynamics`, this structure has no arbitrary critical loci. Its
non-unramified and non-étale loci are defined from the actual stalk maps of `g ^ m`.
The inclusion U2, finiteness U3, and tower implications U4 and U5 are theorems.
Normalized ramification comparison U1 remains a field. Finiteness follows from
integrality, Noetherianity, dominance, local finite presentation, and characteristic
zero at the generic stalk; generic formal étaleness of every iterate is derived. -/
structure SchemeNormalizationUnnormalizedDynamics (A : AlgebraicGeometry.Scheme.{u}) (PN : Type v)
    where
  /-- The actual self-map of the possibly nonnormal scheme. -/
  selfMap : A ⟶ A
  /-- The actual self-map is finite, as in the manuscript. -/
  finite : AlgebraicGeometry.IsFinite selfMap
  /-- The actual self-map is dominant, as in the manuscript. -/
  dominant : AlgebraicGeometry.IsDominant selfMap
  /-- The actual self-map is locally of finite presentation, so stalk formal étaleness
  is the intended pointwise étaleness criterion. -/
  finitePresentation : AlgebraicGeometry.LocallyOfFinitePresentation selfMap
  /-- The self-map sends codimension-one points to codimension-one points. -/
  selfMap_preserves_divisors : ∀ Q : SchemeDivisorPoint A,
    Order.coheight (selfMap Q.1) = 1
  /-- The normalized divisorial dynamics. -/
  normalized : DivisorDynamics PN
  /-- Pushforward from normalized divisors to divisors of the actual scheme. -/
  normalization : PN → SchemeDivisorPoint A
  /-- Normalization commutes with divisor pushforward. -/
  normalization_step : ∀ Q, normalization (normalized.step Q) =
    schemeDivisorMap selfMap selfMap_preserves_divisors (normalization Q)
  /-- The normalization map has finite fibers on divisors. -/
  normalization_finite_fiber : ∀ Q, (normalization ⁻¹' {Q}).Finite
  /-- Normalized ramification maps into the unnormalized non-unramified locus. -/
  mem_nonUnramifiedLocus_of_one_lt_ramificationIdx : ∀ m Q, 1 < normalized.iterateRamificationIdx m
      Q →
    normalization Q ∈ schemeDivisorNonUnramifiedLocus (CategoryTheory.End.of selfMap ^ m).asHom
  /-- The invariant divisor is integral. -/
  integral : AlgebraicGeometry.IsIntegral A
  /-- The invariant divisor has Noetherian underlying space. -/
  noetherian : TopologicalSpace.NoetherianSpace A
  /-- Characteristic zero at the generic point. For a finite dominant self-map this
  makes the finite generic field extension separable, hence formally étale. -/
  charZero : CharZero (A.presheaf.stalk (genericPoint A))

namespace SchemeNormalizationUnnormalizedDynamics

variable {A : AlgebraicGeometry.Scheme.{u}} {PN : Type v}
  (D : SchemeNormalizationUnnormalizedDynamics A PN)

/-- The codimension-one non-unramified locus of each actual iterate. -/
def nonUnramifiedLocus (m : ℕ) : Set (SchemeDivisorPoint A) :=
  schemeDivisorNonUnramifiedLocus (CategoryTheory.End.of D.selfMap ^ m).asHom

/-- Formal étaleness implies formal unramifiedness on the actual stalk maps. -/
theorem nonUnramifiedLocus_subset_nonEtaleLocus (m : ℕ) :
    D.nonUnramifiedLocus m ⊆ schemeDivisorNonEtaleLocus
        (CategoryTheory.End.of D.selfMap ^ m).asHom :=
  schemeDivisorNonUnramifiedLocus_subset_nonEtaleLocus (CategoryTheory.End.of D.selfMap ^ m).asHom

/-- Non-unramifiedness persists in the tower of actual stalk maps. -/
theorem nonUnramifiedLocus_tower (n : ℕ) : D.nonUnramifiedLocus 1 ⊆ D.nonUnramifiedLocus (n + 1) :=
  schemeDivisorNonUnramifiedLocus_tower D.selfMap n

/-- Non-étaleness in the first map of the tower persists in one factor. This is a
theorem about the actual stalk maps, rather than a field of the geometric data. -/
theorem nonEtaleLocus_tower (n : ℕ)
    (Q : SchemeDivisorPoint A)
    (hQ : Q ∈ schemeDivisorNonEtaleLocus (CategoryTheory.End.of D.selfMap ^ 1).asHom) :
    Q ∈ schemeDivisorNonEtaleLocus (CategoryTheory.End.of D.selfMap ^ (n + 1)).asHom ∨
      schemeDivisorMap D.selfMap D.selfMap_preserves_divisors Q ∈
        schemeDivisorNonEtaleLocus (CategoryTheory.End.of D.selfMap ^ n).asHom :=
  schemeDivisorNonEtaleLocus_tower D.selfMap D.selfMap_preserves_divisors n Q hQ

/-- Every categorical iterate of the actual self-map is finite. -/
theorem finite_iterate (m : ℕ) :
    AlgebraicGeometry.IsFinite (CategoryTheory.End.of D.selfMap ^ m).asHom := by
  letI : AlgebraicGeometry.IsFinite D.selfMap := D.finite
  induction m with
  | zero => simpa using
      (inferInstance : AlgebraicGeometry.IsFinite (𝟙 A))
  | succ m ih =>
      rw [pow_succ]
      letI : AlgebraicGeometry.IsFinite (CategoryTheory.End.of D.selfMap ^ m).asHom := ih
      change AlgebraicGeometry.IsFinite (D.selfMap ≫ (CategoryTheory.End.of D.selfMap ^ m).asHom)
      infer_instance

/-- Every categorical iterate of the actual self-map is locally of finite presentation. -/
theorem finitePresentation_iterate (m : ℕ) :
    AlgebraicGeometry.LocallyOfFinitePresentation (CategoryTheory.End.of D.selfMap ^ m).asHom := by
  letI : AlgebraicGeometry.LocallyOfFinitePresentation D.selfMap := D.finitePresentation
  induction m with
  | zero => simpa using
      (inferInstance : AlgebraicGeometry.LocallyOfFinitePresentation (𝟙 A))
  | succ m ih =>
      rw [pow_succ]
      letI : AlgebraicGeometry.LocallyOfFinitePresentation
          (CategoryTheory.End.of D.selfMap ^ m).asHom := ih
      change AlgebraicGeometry.LocallyOfFinitePresentation
        (D.selfMap ≫ (CategoryTheory.End.of D.selfMap ^ m).asHom)
      infer_instance

/-- The actual codimension-one non-étale locus of every iterate is finite (U3).
Closedness follows from local finite presentation; a formally étale stalk makes
that closed locus proper. -/
theorem nonEtaleLocus_finite (m : ℕ) :
    (schemeDivisorNonEtaleLocus (CategoryTheory.End.of D.selfMap ^ m).asHom).Finite := by
  letI : AlgebraicGeometry.IsIntegral A := D.integral
  letI : TopologicalSpace.NoetherianSpace A := D.noetherian
  letI : AlgebraicGeometry.IsFinite D.selfMap := D.finite
  letI : AlgebraicGeometry.IsDominant D.selfMap := D.dominant
  letI : LocallyOfFinitePresentation D.selfMap := D.finitePresentation
  letI : CharZero (A.presheaf.stalk (genericPoint A)) := D.charZero
  letI : LocallyOfFinitePresentation (CategoryTheory.End.of D.selfMap ^ m).asHom :=
    D.finitePresentation_iterate m
  have hgeneric : (D.selfMap.stalkMap (genericPoint A)).hom.FormallyEtale :=
    formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero D.selfMap
  have hetale := exists_formallyEtale_stalk_iterate_of_exists
    D.selfMap ⟨genericPoint A, hgeneric⟩ m
  exact schemeDivisorNonEtaleLocus_finite_of_exists_formallyEtale
    (CategoryTheory.End.of D.selfMap ^ m).asHom hetale

/-- The ordinary two-carrier dynamics obtained by forgetting that its critical loci came
from actual scheme stalk maps. -/
def toNormalizationUnnormalizedDynamics :
    NormalizationUnnormalizedDynamics PN (SchemeDivisorPoint A) where
  normalized := D.normalized
  step := schemeDivisorMap D.selfMap D.selfMap_preserves_divisors
  normalization := D.normalization
  normalization_step := D.normalization_step
  normalization_finite_fiber := D.normalization_finite_fiber
  nonUnramifiedLocus := D.nonUnramifiedLocus
  nonEtaleLocus := fun m ↦ schemeDivisorNonEtaleLocus (CategoryTheory.End.of D.selfMap ^ m).asHom
  mem_nonUnramifiedLocus_of_one_lt_ramificationIdx :=
      D.mem_nonUnramifiedLocus_of_one_lt_ramificationIdx
  nonUnramifiedLocus_subset_nonEtaleLocus := D.nonUnramifiedLocus_subset_nonEtaleLocus
  nonEtaleLocus_finite := D.nonEtaleLocus_finite
  nonUnramifiedLocus_tower := D.nonUnramifiedLocus_tower
  nonEtaleLocus_tower := D.nonEtaleLocus_tower

@[simp]
theorem toNormalizationUnnormalizedDynamics_step :
    D.toNormalizationUnnormalizedDynamics.step = schemeDivisorMap D.selfMap
        D.selfMap_preserves_divisors :=
  rfl

@[simp]
theorem toNormalizationUnnormalizedDynamics_nonEtaleLocus (m : ℕ) :
    D.toNormalizationUnnormalizedDynamics.nonEtaleLocus m =
      schemeDivisorNonEtaleLocus (CategoryTheory.End.of D.selfMap ^ m).asHom :=
  rfl

end SchemeNormalizationUnnormalizedDynamics

/-- The chart route to Theorem `thm:normal-invariant` with an actual unnormalized
scheme and actual stalk-defined critical loci.

The ramification dynamics remains on the normalization carrier `PN`; divisors of the
possibly nonnormal invariant subscheme are literally `SchemeDivisorPoint A`. -/
structure SchemeNormalizationPCFSetupChart (A : AlgebraicGeometry.Scheme.{u})
    (PX : Type v) (PN : Type w) where
  /-- The ambient divisorial dynamics. -/
  ambient : DivisorDynamics PX
  /-- The invariant ambient divisor. -/
  fixedPrime : PX
  /-- Invariance of the ambient divisor. -/
  fixed : ambient.step fixedPrime = fixedPrime
  /-- Normalized divisor dynamics over the actual unnormalized scheme. -/
  restriction : SchemeNormalizationUnnormalizedDynamics A PN
  /-- The singular correction terms. -/
  singularPrimes : Set (SchemeDivisorPoint A)
  /-- Finiteness of the singular correction terms. -/
  singularPrimes_finite : singularPrimes.Finite
  /-- Divisors of the restriction contained in an ambient divisor intersection. -/
  meets : PX → Set (SchemeDivisorPoint A)
  /-- Finiteness of a proper divisor intersection. -/
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- The noncircular chart link. It presents the two actual stalk rings of `g ^ m` as
  localizations of the quotient rings and proves the quotient-ring square commutes. The
  coordinate isomorphisms and arrow comparison are derived, and no non-étaleness
  implication is a field. -/
  chart : ∀ (m : ℕ), 1 ≤ m → ∀ (Q : SchemeDivisorPoint A), Q ∉ singularPrimes →
    (∀ E ∈ (ambient.iterate m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    ∀ (Q' : SchemeDivisorPoint A), restriction.toNormalizationUnnormalizedDynamics.step^[m] Q' = Q →
      SchemeStalkBoundingLocalizationPresentation
        (CategoryTheory.End.of restriction.selfMap ^ m).asHom Q'.1

attribute [local instance] invariantIterateFinitePreimageAlgebra

/-- Literal geometric Step-0 data at one divisor flag of an invariant reduced divisor.

The fields are the assertions made before Steps 1--4 of the manuscript's bounding
proof: an affine neighborhood, regularity exclusions, codimension two in the ambient
scheme, avoidance of every other branch component, and the two named local covering
theorems.  There is no field about formal étaleness, `crit₁`, a bounding chart, or the
conclusion of the bounding theorem. -/
structure InvariantDivisorCorrectionLocalData
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
structure InvariantDivisorSchemeNormalizationPCFSetup
    (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ X)
    [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsDominant f]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [IsNormalScheme X]
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1)
    (PX : Type v) (PN : Type w) where
  ambient : DivisorDynamics PX
  fixedPrime : PX
  fixed : ambient.step fixedPrime = fixedPrime
  restriction : SchemeNormalizationUnnormalizedDynamics (pointClosureIdealSheaf A.1).subscheme PN
  /-- Identification of the stored restriction with the actual invariant-divisor map. -/
  restriction_selfMap : restriction.selfMap = A.invariantClosureMap f hA
  singularPrimes : Set (SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
  singularPrimes_finite : singularPrimes.Finite
  meets : PX → Set (SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- Step-0 geometry for every point tested by the bounding argument. -/
  localData : ∀ (m : ℕ), 1 ≤ m →
    ∀ (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme), Q ∉ singularPrimes →
    (∀ E ∈ (ambient.iterate m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    ∀ (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme),
      restriction.toNormalizationUnnormalizedDynamics.step^[m] Q' = Q →
      InvariantDivisorCorrectionLocalData X f A m Q Q'

namespace InvariantDivisorSchemeNormalizationPCFSetup

variable {X : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ X}
  [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsDominant f]
  [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
  [IsNormalScheme X]
  {A : SchemeDivisorPoint X} {hA : f A.1 = A.1}
  {PX : Type v} {PN : Type w}
  (S : InvariantDivisorSchemeNormalizationPCFSetup X f A hA PX PN)

/-- Construct the dynamics-facing chart setup from the actual ambient endomorphism,
invariant divisor, and literal Step-0 data. -/
noncomputable def toSchemeNormalizationPCFSetupChart :
    SchemeNormalizationPCFSetupChart
      (pointClosureIdealSheaf A.1).subscheme PX PN where
  ambient := S.ambient
  fixedPrime := S.fixedPrime
  fixed := S.fixed
  restriction := S.restriction
  singularPrimes := S.singularPrimes
  singularPrimes_finite := S.singularPrimes_finite
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
    change ((schemeDivisorMap S.restriction.selfMap S.restriction.selfMap_preserves_divisors)^[m]
        Q').1 = Q.1
      at hval
    rw [schemeDivisorMap_iterate_val] at hval
    have hxz :
        (CategoryTheory.End.of (A.invariantClosureMap f hA) ^ m).asHom.base Q'.1 = Q.1 := by
      simpa only [← S.restriction_selfMap] using hval
    have hresult :=
      A.invariantClosureStalkBoundingLocalizationOfCorrectionAt
        f hA m d.U Q'.1 d.source_mem Q d.target_mem hxz
          d.ambient_coheight d.ambient_regular d.divisor_regular d.branch_avoid
          d.purity d.abhyankar
    simpa only [S.restriction_selfMap] using hresult

end InvariantDivisorSchemeNormalizationPCFSetup

namespace SchemeNormalizationPCFSetupChart

variable {A : AlgebraicGeometry.Scheme.{u}} {PX : Type v} {PN : Type w}
  (S : SchemeNormalizationPCFSetupChart A PX PN)

/-- The bounding conclusion for actual divisors, derived from purity and Abhyankar on the
identified local stalk chart. -/
theorem notMem_nonEtaleBranch_iterate (m : ℕ) (hm : 1 ≤ m) (Q : SchemeDivisorPoint A)
    (hs : Q ∉ S.singularPrimes)
    (hmeets : ∀ E ∈ (S.ambient.iterate m).branch, E ≠ S.fixedPrime → Q ∉ S.meets E) :
    Q ∉ S.restriction.toNormalizationUnnormalizedDynamics.nonEtaleBranch m := by
  rintro ⟨Q', hcrit, hQ'Q⟩
  have hchart := S.chart m hm Q hs hmeets Q' hQ'Q
  have hnot : Q' ∉ schemeDivisorNonEtaleLocus
      (CategoryTheory.End.of S.restriction.selfMap ^ m).asHom :=
    hchart.notMem_schemeDivisorNonEtaleLocus
  exact hnot hcrit

/-- Forget the explicit scheme and charts after deriving the bounding conclusion. -/
def toNormalizationPCFSetup :
    NormalizationPCFSetup PX PN (SchemeDivisorPoint A) where
  ambient := S.ambient
  fixedPrime := S.fixedPrime
  fixed := S.fixed
  restriction := S.restriction.toNormalizationUnnormalizedDynamics
  singularPrimes := S.singularPrimes
  singularPrimes_finite := S.singularPrimes_finite
  meets := S.meets
  meets_finite := S.meets_finite
  notMem_nonEtaleBranch_iterate := S.notMem_nonEtaleBranch_iterate

/-- The unnormalized restriction is `1`-PCF on the actual-stalk chart route. -/
theorem restriction_isNonEtaleBranchPCF (h : S.ambient.IsPCF) :
    S.restriction.toNormalizationUnnormalizedDynamics.IsNonEtaleBranchPCF :=
  S.toNormalizationPCFSetup.restriction_isNonEtaleBranchPCF h

/-- The normalized restriction is PCF on the actual-stalk chart route. -/
theorem normalized_isPCF (h : S.ambient.IsPCF) : S.restriction.normalized.IsPCF :=
  S.toNormalizationPCFSetup.normalized_isPCF h

/-- Periodic-prime form of `normalized_isPCF`. -/
theorem normalized_isPCF_of_iterate {D : DivisorDynamics PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.ambient = D.iterate n) (h : D.IsPCF) : S.restriction.normalized.IsPCF :=
  S.toNormalizationPCFSetup.normalized_isPCF_of_iterate hn hS h

end SchemeNormalizationPCFSetupChart

namespace InvariantDivisorSchemeNormalizationPCFSetup

variable {X : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ X}
  [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsDominant f]
  [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
  [IsNormalScheme X]
  {A : SchemeDivisorPoint X} {hA : f A.1 = A.1}
  {PX : Type v} {PN : Type w}
  (S : InvariantDivisorSchemeNormalizationPCFSetup X f A hA PX PN)

/-- The bounding conclusion for the actual invariant-divisor restriction, derived from
the literal Step-0 package and the two named local covering inputs. -/
theorem notMem_nonEtaleBranch_iterate (m : ℕ) (hm : 1 ≤ m)
    (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (hs : Q ∉ S.singularPrimes)
    (hmeets : ∀ E ∈ (S.ambient.iterate m).branch,
      E ≠ S.fixedPrime → Q ∉ S.meets E) :
    Q ∉ S.restriction.toNormalizationUnnormalizedDynamics.nonEtaleBranch m :=
  S.toSchemeNormalizationPCFSetupChart.notMem_nonEtaleBranch_iterate m hm Q hs hmeets

/-- The actual unnormalized invariant-divisor restriction is `1`-PCF. -/
theorem restriction_isNonEtaleBranchPCF (h : S.ambient.IsPCF) :
    S.restriction.toNormalizationUnnormalizedDynamics.IsNonEtaleBranchPCF :=
  S.toSchemeNormalizationPCFSetupChart.restriction_isNonEtaleBranchPCF h

/-- The normalized invariant-divisor dynamics is PCF. -/
theorem normalized_isPCF (h : S.ambient.IsPCF) : S.restriction.normalized.IsPCF :=
  S.toSchemeNormalizationPCFSetupChart.normalized_isPCF h

/-- Periodic-prime form of the normalized PCF conclusion. -/
theorem normalized_isPCF_of_iterate {D : DivisorDynamics PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.ambient = D.iterate n) (h : D.IsPCF) : S.restriction.normalized.IsPCF :=
  S.toSchemeNormalizationPCFSetupChart.normalized_isPCF_of_iterate hn hS h

end InvariantDivisorSchemeNormalizationPCFSetup

end Pcf
