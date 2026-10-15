/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Localization.Saturation
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Challenge: PCF all the way down in characteristic zero

This file is the statement half of a Palomar entry. It imports only Mathlib.

## The theorem

Let `k` be a field of characteristic zero, `X` an integral, locally Noetherian scheme with
Noetherian underlying space, `s : X ⟶ Spec k` locally of finite type, and `f : X ⟶ X` a finite
dominant morphism. Assume `f` is post-critically finite on the normalization
(`SchemeNormalizedPCFOfFiniteType`). Then `f` is *PCF all the way down*
(`SchemePCFAllTheWayDown`): for every depth `d`, normalized PCF holds at `X`, and,
recursively, for every codimension-one point `A` of `X` that is preperiodic,
`f^(r+p)(A) = f^r(A)` with `p ≥ 1`, normalized PCF holds for the return map `f^p` on the reduced
closure of `f^r(A)`, and so on through `d` restriction steps.

## What is assumed

The theorem is **conditional**. Its hypothesis `PcfAllTheWayDownLocalTheorems` has exactly
two fields, which are classical results that this formalization does not prove:

* `purity`: Zariski–Nagata purity of the branch locus, Stacks Project Tag 0BMB, in the
  affine form `Stacks.ZariskiNagataPurity`, quantified over all commutative rings in the
  working universe;
* `abhyankar`: Abhyankar's lemma for a regular divisor, Stacks Project Tags 0EYG/0EYH, in
  the affine characteristic-zero standard-cover form `Stacks.AbhyankarLemma`. As its
  docstring records, it requires every positive integer to be invertible, which is stronger
  than the tag's codimension-one tame hypothesis; the assumed statement is therefore weaker
  than the full tag.

No other mathematical input is assumed.

## How to read this file

Every declaration below restates a declaration of the `Pcf` development under the same
name. Comparator checks, for every declaration reached from the final theorem, that it is
identical here and in the development; for a definition or structure this includes its
value, so the data (the sets, maps and numbers) is literally the development's.

Theorems proved by `sorry` are deliberate holes, listed in `comparator.json`. Comparator
checks that each has the same statement on both sides, and the Solution proves it. They are
of two kinds:

* supporting lemmas whose statements occur inside the definitions (instances such as
  `pointClosureSubscheme_isIntegral`, and codimension facts such as `coheight_apply_eq_one`);
* the auxiliary theorems `<definition>._proof_<n>` that Lean generates for the proof
  obligations inside a definition. Most are generated here from the copied proofs. A few are
  stated explicitly under their generated names, because the copied proof would need lemmas
  of the development that are not restated here.

Proofs are irrelevant to the data of a definition, so no hole changes what a definition
means. The few lemmas copied with their proofs (`map_genericPoint_eq_of_isDominant`,
`formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero`, `schemeStalkCharZeroOfField`,
`schemeGenericToNormalization_comp`, `schemeGenericEndomorphism_comp`, and the affine and
stalk `k`-algebra structures) are used only inside proof obligations.

Separatedness, which the manuscript includes in "variety", is not used, so the statement
is slightly more general there. At depth zero it restates the ambient PCF hypothesis.
-/

@[expose] public noncomputable section

set_option linter.auxLemma false
set_option linter.style.haveILetI false

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

/-! ## Abstract divisorial dynamics -/

namespace Pcf

/-- A divisorial dynamical system on a set `P` of primes: the pushforward `step`, positive
ramification indices `ram`, surjectivity of `step` (lying over), and finiteness of the
branch set `{Q | ∃ Q', step Q' = Q ∧ 1 < ram Q'}`. -/
structure DivDyn (P : Type u) where
  /-- Pushforward of primes: `step P'` is the prime `g(P')`. -/
  step : P → P
  /-- `ram P'` is the ramification index `e(P' / g(P'))`. -/
  ram : P → ℕ
  /-- Ramification indices are positive. -/
  ram_pos : ∀ Q, 0 < ram Q
  /-- Lying over: every prime is the image of a prime. -/
  step_surjective : Function.Surjective step
  /-- The branch divisor has finitely many components. -/
  branch_finite' : {Q | ∃ Q', step Q' = Q ∧ 1 < ram Q'}.Finite

namespace DivDyn

variable {P : Type u} (D : DivDyn P)

/-- The branch primes: images of primes with ramification index greater than one. -/
def branch : Set P := {Q | ∃ Q', D.step Q' = Q ∧ 1 < D.ram Q'}

/-- The ramification index of the `m`-th iterate, `∏_{i<m} e(gⁱ(Q))`. -/
def iterRam (m : ℕ) (Q : P) : ℕ := ∏ i ∈ Finset.range m, D.ram (D.step^[i] Q)

/-- The postcritical set `⋃_{n ≥ 0} gⁿ(branch)`. -/
def pcSet : Set P := ⋃ n : ℕ, D.step^[n] '' D.branch

/-- Post-critically finite: the postcritical set is finite. -/
def PCF : Prop := D.pcSet.Finite

end DivDyn

end Pcf

/-! ## The two assumed local theorems -/

namespace Pcf.LocalModel

open Polynomial

variable {R : Type*} [CommRing R]

/-- The polynomial `X ^ e - C (u * a)` defining a standard tame cyclic cover. -/
noncomputable def localPoly (u : Rˣ) (a : R) (e : ℕ) : R[X] :=
  X ^ e - Polynomial.C ((u : R) * a)

end Pcf.LocalModel

namespace Pcf.Stacks

open TensorProduct

/-- `C` is, as an `R`-algebra, a finite product of standard covers
`R[z]/(z^{e_i} - u_i a)` with each `e_i` positive and invertible in `R`. -/
def IsFiniteDisjointUnionOfStandardTameCovers
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C] (a : R) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (u : ι → Rˣ),
    (∀ i, e i ≠ 0) ∧ (∀ i, IsUnit ((e i : ℕ) : R)) ∧
    Nonempty (C ≃ₐ[R] ∀ i, AdjoinRoot (LocalModel.localPoly (u i) a (e i)))

/-- The conclusion of Abhyankar's lemma at a prime `y` of `R`: an étale `R`-algebra `R'`
with a prime over `y`, Noetherian, in which `a` is a nonzerodivisor with regular quotient,
such that `R' ⊗[R] S` is a finite product of standard tame covers for `a`. -/
def HasAbhyankarStandardCoverAt
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (a : R) (y : PrimeSpectrum R) : Prop :=
  ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
    Algebra.Etale R R' ∧
    (∃ y' : PrimeSpectrum R', y'.asIdeal.under R = y.asIdeal) ∧
    IsNoetherianRing R' ∧
    algebraMap R R' a ∈ nonZeroDivisors R' ∧
    IsRegularRing (R' ⧸ Ideal.span {algebraMap R R' a}) ∧
    IsFiniteDisjointUnionOfStandardTameCovers
      R' (R' ⊗[R] S) (algebraMap R R' a)

/-- **Abhyankar's lemma (assumed)**, Stacks Tags 0EYG/0EYH, affine form: if `R` is
Noetherian, `a` is a nonzerodivisor with `R/(a)` regular, `S` is finite over `R` and étale
away from `a`, `S` is the integral closure of `R` in `S[1/a]`, and every positive integer is
a unit in `R`, then every prime of `R` containing `a` has a standard tame cover. -/
def AbhyankarLemma (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) : Prop :=
  IsNoetherianRing R →
  a ∈ nonZeroDivisors R →
  IsRegularRing (R ⧸ Ideal.span {a}) →
  Module.Finite R S →
  (∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal) →
  IsIntegralClosure S R (Localization.Away (algebraMap R S a)) →
  (∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) →
  ∀ y : PrimeSpectrum R, a ∈ y.asIdeal →
    HasAbhyankarStandardCoverAt R S a y

/-- The hypotheses of Stacks Tag 0BMB at a prime `w` of `S`: the local ring of `S` at `w` is
a normal domain, the local ring of `R` below is regular, `R → S` is quasi-finite at `w`,
the heights agree and are positive, and `R → S` is unramified at every height-one prime
specializing to `w`. -/
structure ZariskiNagataPurityInputsAt
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (w : PrimeSpectrum S) : Prop where
  source_isDomain : IsDomain (Localization.AtPrime w.asIdeal)
  source_isIntegrallyClosed : IsIntegrallyClosed (Localization.AtPrime w.asIdeal)
  target_isRegular : IsRegularLocalRing (Localization.AtPrime (w.asIdeal.under R))
  quasiFinite : Algebra.QuasiFiniteAt R w.asIdeal
  equalDimension : w.asIdeal.height = (w.asIdeal.under R).height
  positiveDimension : 1 ≤ w.asIdeal.height
  unramifiedCodimensionOne :
    ∀ w' : PrimeSpectrum S, w' ⤳ w → w'.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt R w'.asIdeal

/-- (Hole; auxiliary proof obligation of `HasZariskiNagataPurityAt`.) -/
theorem HasZariskiNagataPurityAt._proof_1.{u_1} (S : Type u_1) [CommRing S]
    (w : PrimeSpectrum S) : w.asIdeal.IsPrime := by sorry

/-- The conclusion of Stacks Tag 0BMB at `w`: under its hypotheses, `R → S` is étale at
`w`. -/
def HasZariskiNagataPurityAt
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (w : PrimeSpectrum S) : Prop :=
  ZariskiNagataPurityInputsAt R S w →
    @Algebra.IsEtaleAt R S _ _ _ w.asIdeal (HasZariskiNagataPurityAt._proof_1 S w)

/-- **Zariski–Nagata purity (assumed)**, Stacks Tag 0BMB, affine form: for Noetherian `R`
and `S` with `S` of finite type over `R`, the pointwise conclusion holds at every prime. -/
def ZariskiNagataPurity (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  IsNoetherianRing R → IsNoetherianRing S → Algebra.FiniteType R S →
  ∀ w : PrimeSpectrum S, HasZariskiNagataPurityAt R S w

end Pcf.Stacks

/-! ## Divisors, critical loci and ramification of scheme morphisms -/

namespace Pcf

/-- The codimension-one points of a scheme. -/
def SchemeDivisorPoint (X : AlgebraicGeometry.Scheme) :=
  {x : X // Order.coheight x = 1}

/-- A scheme is normal: every ring of sections over an affine open is integrally closed. -/
class IsNormalScheme (X : Scheme.{u}) : Prop where
  component_integrallyClosed : ∀ U : X.affineOpens, IsIntegrallyClosed Γ(X, U)

/-- `g` is not formally unramified at `x`: the stalk map at `x` is not formally
unramified. -/
def schemeCrit0At {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (x : X) : Prop :=
  ¬ (g.stalkMap x).hom.FormallyUnramified

/-- The codimension-one points at which `g` is not formally unramified. -/
def schemeDivisorCrit0 {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) :
    Set (SchemeDivisorPoint X) :=
  {x | schemeCrit0At g x.1}

/-- `g` is not formally étale at `x`: the stalk map at `x` is not formally étale. -/
def schemeCrit1At {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (x : X) : Prop :=
  ¬ (g.stalkMap x).hom.FormallyEtale

/-- The codimension-one points at which `g` is not formally étale. -/
def schemeDivisorCrit1 {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) :
    Set (SchemeDivisorPoint X) :=
  {x | schemeCrit1At g x.1}

/-- All points at which `g` is not formally étale. -/
def schemeCrit1Locus {X Y : Scheme.{u}} (g : X ⟶ Y) : Set X :=
  {x | schemeCrit1At g x}

/-- The map on codimension-one points `x ↦ g x`, given that `g` preserves codimension one. -/
def schemeDivisorMap {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (hcodim : ∀ x : SchemeDivisorPoint X, Order.coheight (g x.1) = 1) :
    SchemeDivisorPoint X → SchemeDivisorPoint Y :=
  fun x ↦ ⟨g x.1, hcodim x⟩

/-- A divisorial dynamical system `norm` on a set `PN` (the divisors of a normalization of
`A`), together with the actual finite dominant, locally finitely presented self-map `g` of
`A`; a map `normalization` from `PN` to the divisors of `A` commuting with pushforward and
with finite fibres; and the inclusion of the ramification of `norm`'s iterates into the
non-formally-unramified locus of the iterates of `g`. `A` is integral, has Noetherian
underlying space, and has characteristic zero at its generic point. -/
structure SchemeNormalizationUnnormDyn (A : AlgebraicGeometry.Scheme.{u}) (PN : Type v) where
  /-- The actual self-map of the possibly nonnormal scheme. -/
  g : A ⟶ A
  /-- The actual self-map is finite. -/
  finite : AlgebraicGeometry.IsFinite g
  /-- The actual self-map is dominant. -/
  dominant : AlgebraicGeometry.IsDominant g
  /-- The actual self-map is locally of finite presentation. -/
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
  /-- Normalized ramification maps into the unnormalized non-unramified locus. -/
  crit_subset_crit0 : ∀ m Q, 1 < norm.iterRam m Q →
    normalization Q ∈ schemeDivisorCrit0 (CategoryTheory.End.of g ^ m).asHom
  /-- The scheme is integral. -/
  integral : AlgebraicGeometry.IsIntegral A
  /-- The scheme has Noetherian underlying space. -/
  noetherian : TopologicalSpace.NoetherianSpace A
  /-- Characteristic zero at the generic point. -/
  charZero : CharZero (A.presheaf.stalk (genericPoint A))

/-- The ramification index at a codimension-one point `x` of the stalk map
`O_{Y, f x} → O_{X, x}`: the ramification index of the maximal ideal of `O_{X,x}` over
`O_{Y, f x}`. -/
noncomputable def schemeDivisorRam {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : SchemeDivisorPoint X) : ℕ :=
  letI := (f.stalkMap x.1).hom.toAlgebra
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)).ramificationIdx
    (Y.presheaf.stalk (f x.1))

/-! ## Reduced closures of points -/

/-- The reduced ideal sheaf of the closure of a point `x`; for a codimension-one point,
the reduced integral divisor carried by `x`. -/
noncomputable def pointClosureIdealSheaf {X : Scheme.{u}} (x : X) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({x} : Set X), isClosed_closure⟩

/-- (Hole.) If `f x = y`, the ideal of `closure {y}` is contained in the image under `f` of the
ideal of `closure {x}`. -/
theorem pointClosureIdealSheaf_le_map_of_apply_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y) :
    pointClosureIdealSheaf y ≤ (pointClosureIdealSheaf x).map f := by sorry

/-- The morphism `closure {x} ⟶ closure {y}` of reduced closed subschemes induced by `f`
when `f x = y`. -/
noncomputable def pointClosureSubschemeMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y) :
    (pointClosureIdealSheaf x).subscheme ⟶
      (pointClosureIdealSheaf y).subscheme :=
  (pointClosureIdealSheaf x).subschemeMap
    (pointClosureIdealSheaf y) f
    (pointClosureIdealSheaf_le_map_of_apply_eq f x y hxy)

/-- (Hole.) Every iterate of a finite endomorphism is finite. -/
instance (priority := low) finite_end_pow_instance {X : Scheme.{u}}
    (f : X ⟶ X) [IsFinite f] (m : ℕ) :
    IsFinite (CategoryTheory.End.of f ^ m).asHom := by sorry

/-- Every iterate of a dominant endomorphism is dominant (used only inside proof
obligations). -/
instance (priority := low) dominant_end_pow_instance {X : Scheme.{u}}
    (f : X ⟶ X) [IsDominant f] (m : ℕ) :
    IsDominant (CategoryTheory.End.of f ^ m).asHom := by
  induction m with
  | zero => simpa using (inferInstance : IsDominant (𝟙 X))
  | succ m ih =>
      rw [pow_succ]
      letI : IsDominant (CategoryTheory.End.of f ^ m).asHom := ih
      change IsDominant (f ≫ (CategoryTheory.End.of f ^ m).asHom)
      infer_instance

/-- (Hole.) A finite dominant morphism of integral schemes whose target has affine rings of
finite type over a field `k` sends codimension-one points to codimension-one points. -/
theorem coheight_apply_eq_one_of_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [IsDominant f] [IsIntegral X] [IsIntegral Y] (k : Type*) [Field k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)] (A : SchemeDivisorPoint X) :
    Order.coheight (f A.1) = 1 := by sorry

/-- (Hole.) A finite dominant morphism of integral schemes to a normal locally Noetherian
target sends codimension-one points to codimension-one points. -/
theorem coheight_apply_eq_one {Y X : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (A : SchemeDivisorPoint X) :
    Order.coheight (f A.1) = 1 := by sorry

/-- The pushforward `A ↦ f A` on codimension-one points, for `f` finite dominant to a normal
locally Noetherian integral target. -/
noncomputable def SchemeDivisorPoint.mapFiniteDominantNormal {Y X : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (A : SchemeDivisorPoint X) : SchemeDivisorPoint Y :=
  ⟨f A.1, coheight_apply_eq_one f A⟩

/-- The self-map of the reduced closure of `A` induced by `f`, when `f A = A`. -/
noncomputable def SchemeDivisorPoint.invariantClosureMap {X : Scheme.{u}} (f : X ⟶ X)
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1) :
    (pointClosureIdealSheaf A.1).subscheme ⟶
      (pointClosureIdealSheaf A.1).subscheme :=
  pointClosureSubschemeMap f A.1 A.1 hA

/-- (Hole.) The restriction of a finite endomorphism to an invariant reduced divisor is
finite. -/
instance SchemeDivisorPoint.invariantClosureMap_isFinite {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] (A : SchemeDivisorPoint X) (hA : f A.1 = A.1) :
    IsFinite (A.invariantClosureMap f hA) := by sorry

/-- (Hole.) The restriction of an endomorphism to an invariant reduced divisor is
dominant. -/
instance SchemeDivisorPoint.invariantClosureMap_dominant
    {X : Scheme.{u}} (f : X ⟶ X) (A : SchemeDivisorPoint X)
    (hA : f A.1 = A.1) : IsDominant (A.invariantClosureMap f hA) := by sorry

/-- (Hole.) The reduced closure of a point is integral. -/
instance pointClosureSubscheme_isIntegral {X : Scheme.{u}} (x : X) :
    IsIntegral (pointClosureIdealSheaf x).subscheme := by sorry

/-- (Hole.) The reduced closure of a point of a locally Noetherian scheme is locally
Noetherian. -/
instance pointClosureSubscheme_locallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] (x : X) :
    IsLocallyNoetherian (pointClosureIdealSheaf x).subscheme := by sorry

/-- (Hole.) The reduced closure of a point of a Noetherian space has Noetherian underlying
space. -/
instance pointClosureSubscheme_noetherian {X : Scheme.{u}}
    [NoetherianSpace X] (x : X) :
    NoetherianSpace (pointClosureIdealSheaf x).subscheme := by sorry

/-! ## The divisor dynamics of a finite dominant self-map of a normal scheme

The theorems named `<definition>._proof_<n>` below are the proof obligations inside the
definitions that follow, stated separately so that each definition is literally the one in
the proof development. They are holes; the Solution proves them. -/

/-- (Hole.) Finitely many non-étale divisors give finitely many branch divisors. -/
theorem divDynOfFiniteDominantNormal._proof_1.{u_1} {X : Scheme.{u_1}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] :
    (schemeDivisorCrit1 f).Finite →
      {Q : SchemeDivisorPoint X |
        ∃ Q' : SchemeDivisorPoint X,
          SchemeDivisorPoint.mapFiniteDominantNormal f Q' = Q ∧ 1 < schemeDivisorRam f Q'}.Finite := by sorry

/-- (Hole.) Ramification indices at codimension-one points are positive. -/
theorem divDynOfFiniteDominantNormal._proof_2.{u_1} {X : Scheme.{u_1}} (f : X ⟶ X)
    [IsFinite f] (x : SchemeDivisorPoint X) : 0 < schemeDivisorRam f x := by sorry

/-- (Hole.) A Noetherian non-étale locus with one formally étale stalk has finitely many
non-étale divisors. -/
theorem divDynOfFiniteDominantNormalOfExistsFormallyEtale._proof_1.{u_1} {X : Scheme.{u_1}}
    (f : X ⟶ X) [IsFinite f] [IsIntegral X] [IsLocallyNoetherian X]
    [NoetherianSpace (schemeCrit1Locus f)] :
    (∃ x : X, (f.stalkMap x).hom.FormallyEtale) → (schemeDivisorCrit1 f).Finite := by sorry

/-- (Hole.) Lying over: the pushforward on codimension-one points is surjective. -/
theorem SchemeDivisorPoint.mapFiniteDominantNormal_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y] :
    Function.Surjective (fun x : SchemeDivisorPoint X ↦
      x.mapFiniteDominantNormal f) := by sorry

/-- The divisor dynamics of `f`: primes are the codimension-one points, `step` is
pushforward by `f`, and `ram` is `schemeDivisorRam f`. The finiteness hypothesis on the
non-étale divisors makes the branch set finite. -/
noncomputable def divDynOfFiniteDominantNormal
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (hcrit : (schemeDivisorCrit1 f).Finite) : DivDyn (SchemeDivisorPoint X) where
  step x := x.mapFiniteDominantNormal f
  ram := schemeDivisorRam f
  ram_pos := divDynOfFiniteDominantNormal._proof_2 f
  step_surjective := SchemeDivisorPoint.mapFiniteDominantNormal_surjective f
  branch_finite' := divDynOfFiniteDominantNormal._proof_1 f hcrit

/-- The same dynamics, with finiteness of the non-étale divisors derived from Noetherianity
of the non-étale locus and the existence of one formally étale stalk. -/
noncomputable def divDynOfFiniteDominantNormalOfExistsFormallyEtale
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace (schemeCrit1Locus f)]
    (hetale : ∃ x : X, (f.stalkMap x).hom.FormallyEtale) :
    DivDyn (SchemeDivisorPoint X) :=
  divDynOfFiniteDominantNormal f (divDynOfFiniteDominantNormalOfExistsFormallyEtale._proof_1 f hetale)

/-! Two supporting facts, with the proofs from the development. They are used only inside
the proof obligations of the definitions below. -/

/-- A dominant morphism between irreducible schemes sends the generic point to the generic
point. -/
theorem map_genericPoint_eq_of_isDominant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert! (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range]

/-- In characteristic zero, the generic stalk map of a finite dominant endomorphism of an
integral scheme is formally étale. -/
theorem formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f] [IsIntegral X]
    [CharZero (X.presheaf.stalk (genericPoint X))] :
    (f.stalkMap (genericPoint X)).hom.FormallyEtale := by
  have hgp : f (genericPoint X) = genericPoint X :=
    map_genericPoint_eq_of_isDominant f
  let e := (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField (X.presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (X.presheaf.stalk (f (genericPoint X))) :=
    hfield.toField
  letI : CharZero (X.presheaf.stalk (f (genericPoint X))) :=
    charZero_of_injective_ringHom e.symm.injective
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  letI : FaithfulSMul (X.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (f.stalkMap (genericPoint X)).hom.injective
  letI : Algebra.QuasiFinite (X.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) := f.quasiFiniteAt (genericPoint X)
  letI : Module.Finite (X.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) :=
    Algebra.QuasiFinite.iff_of_isArtinianRing.mp inferInstance
  letI : PerfectField (X.presheaf.stalk (f (genericPoint X))) :=
    PerfectField.ofCharZero
  rw [RingHom.FormallyEtale]
  exact Algebra.FormallyEtale.of_isSeparable _ _

/-- The same dynamics on a scheme with Noetherian underlying space. -/
noncomputable def divDynOfFiniteDominantNormalNoetherian
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    (hetale : ∃ x : X, (f.stalkMap x).hom.FormallyEtale) :
    DivDyn (SchemeDivisorPoint X) :=
  divDynOfFiniteDominantNormalOfExistsFormallyEtale f hetale

/-- The same dynamics in characteristic zero at the generic point, where the generic stalk
map is formally étale. -/
noncomputable def divDynOfFiniteDominantNormalCharZero
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    [CharZero (X.presheaf.stalk (genericPoint X))] :
    DivDyn (SchemeDivisorPoint X) :=
  divDynOfFiniteDominantNormalNoetherian f
    ⟨genericPoint X,
      formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero f⟩

/-- The divisor dynamics of `gN` on a normal integral scheme `N` that is finite dominant
over a Noetherian integral scheme `A` of characteristic zero at its generic point. -/
noncomputable def divDynOfFiniteNormalization
    {A N : Scheme.{u}} (gN : N ⟶ N) (nu : N ⟶ A)
    [IsFinite gN] [IsDominant gN]
    [IsFinite nu] [IsDominant nu]
    [IsIntegral A] [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    [NoetherianSpace A]
    [CharZero (A.presheaf.stalk (genericPoint A))] :
    DivDyn (SchemeDivisorPoint N) := by
  letI : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace nu
  letI : IsNoetherian N := {}
  have hnu : nu (genericPoint N) = genericPoint A :=
    map_genericPoint_eq_of_isDominant nu
  let e :=
    (A.presheaf.stalkCongr (Inseparable.of_eq hnu)).commRingCatIsoToRingEquiv
  have hfield : IsField (A.presheaf.stalk (nu (genericPoint N))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (A.presheaf.stalk (nu (genericPoint N))) := hfield.toField
  letI : CharZero (A.presheaf.stalk (nu (genericPoint N))) :=
    charZero_of_injective_ringHom e.symm.injective
  letI : CharZero (N.presheaf.stalk (genericPoint N)) :=
    charZero_of_injective_ringHom (nu.stalkMap (genericPoint N)).hom.injective
  exact divDynOfFiniteDominantNormalCharZero gN

/-! ## The canonical global normalization -/

section GlobalNormalization

variable (A : Scheme.{u}) [IsIntegral A]

/-- The inclusion `Spec K(A) ⟶ A` of the generic point. -/
abbrev schemeGenericInclusion : Spec A.functionField ⟶ A :=
  A.fromSpecStalk (genericPoint A)

/-- (Hole.) The generic-point inclusion is quasi-compact. -/
instance schemeGenericInclusion_quasiCompact : QuasiCompact (schemeGenericInclusion A) := by sorry

/-- The normalization of `A`: Mathlib's relative normalization of `A` in its function field. -/
abbrev schemeGlobalNormalization : Scheme.{u} :=
  (schemeGenericInclusion A).normalization

/-- The normalization morphism `Ã ⟶ A`. -/
abbrev schemeGlobalNormalizationMap : schemeGlobalNormalization A ⟶ A :=
  (schemeGenericInclusion A).fromNormalization

/-- The inclusion `Spec K(A) ⟶ Ã` of the function field into the normalization. -/
abbrev schemeGenericToNormalization : Spec A.functionField ⟶ schemeGlobalNormalization A :=
  (schemeGenericInclusion A).toNormalization

/-- The function field factors through the normalization. -/
@[reassoc (attr := simp)]
theorem schemeGenericToNormalization_comp :
    schemeGenericToNormalization A ≫ schemeGlobalNormalizationMap A =
      schemeGenericInclusion A :=
  (schemeGenericInclusion A).toNormalization_fromNormalization

/-- (Hole.) The normalization is integral. -/
instance schemeGlobalNormalization_isIntegral : IsIntegral (schemeGlobalNormalization A) := by sorry

/-- (Hole.) The normalization morphism is integral. -/
instance schemeGlobalNormalizationMap_isIntegralHom :
    IsIntegralHom (schemeGlobalNormalizationMap A) := by sorry

/-- (Hole.) The normalization morphism is dominant. -/
instance schemeGlobalNormalizationMap_isDominant :
    IsDominant (schemeGlobalNormalizationMap A) := by sorry

/-- (Hole.) The normalization morphism is an isomorphism on generic stalks. -/
instance schemeGlobalNormalizationMap_isIso_generic_stalkMap :
    IsIso ((schemeGlobalNormalizationMap A).stalkMap
      (genericPoint (schemeGlobalNormalization A))) := by sorry

/-- (Hole.) The normalization is normal. -/
instance schemeGlobalNormalization_isNormal : IsNormalScheme (schemeGlobalNormalization A) := by sorry

variable {A} (g : A ⟶ A) [IsDominant g]

/-- The morphism `Spec K(A) ⟶ Spec K(A)` induced by a dominant `g` on function fields. -/
def schemeGenericEndomorphism : Spec A.functionField ⟶ Spec A.functionField :=
  Spec.map (g.stalkMap (genericPoint A)) ≫
    Spec.map (A.presheaf.stalkSpecializes
      (specializes_of_eq (map_genericPoint_eq_of_isDominant g)))

variable [IsFinite g]

omit [IsDominant g] in
/-- The comparison from the normalization of `Spec K(A) ⟶ A ⟶ A` (via `g`) to `Ã`. -/
def schemeNormalizationComparison :
    (schemeGenericInclusion A ≫ g).normalization ⟶ schemeGlobalNormalization A :=
  (schemeGenericInclusion A ≫ g).normalizationDesc
    (schemeGenericToNormalization A) (schemeGlobalNormalizationMap A ≫ g) (by simp)

omit [IsFinite g] in
/-- `g` on function fields is compatible with the generic-point inclusion. -/
@[reassoc]
theorem schemeGenericEndomorphism_comp :
    schemeGenericEndomorphism g ≫ schemeGenericInclusion A =
      schemeGenericInclusion A ≫ g := by
  simp only [schemeGenericEndomorphism, Category.assoc, schemeGenericInclusion,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The map from the same normalization to `Ã` induced by `g` on function fields. -/
def schemeNormalizationGenericMap :
    (schemeGenericInclusion A ≫ g).normalization ⟶ schemeGlobalNormalization A :=
  (schemeGenericInclusion A ≫ g).normalizationDesc
    (schemeGenericEndomorphism g ≫ schemeGenericToNormalization A)
    (schemeGlobalNormalizationMap A) (by
      rw [Category.assoc, schemeGenericToNormalization_comp,
        schemeGenericEndomorphism_comp])

omit [IsDominant g] in
/-- (Hole.) The comparison map is an isomorphism. -/
instance schemeNormalizationComparison_isIso :
    IsIso (schemeNormalizationComparison g) := by sorry

section Lift

variable [IsIso (schemeNormalizationComparison g)]

/-- The lift `Ã ⟶ Ã` of `g` to the normalization. -/
def schemeGlobalNormalizationLift : schemeGlobalNormalization A ⟶ schemeGlobalNormalization A :=
  inv (schemeNormalizationComparison g) ≫ schemeNormalizationGenericMap g

end Lift

end GlobalNormalization

/-- (Hole.) The normalization of an integral scheme whose affine rings are of finite type
over a field of characteristic zero is finite over it. -/
theorem schemeGlobalNormalizationMap_isFinite_of_affineFiniteType
    (A : Scheme.{u}) [IsIntegral A]
    (k : Type u) [Field k] [CharZero k]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)] :
    IsFinite (schemeGlobalNormalizationMap A) := by sorry

/-! ## The normalized divisor dynamics of a self-map -/

/-- (Hole.) The normalization map commutes with divisor pushforward. -/
theorem schemeNormalizationUnnormDynOfFiniteType._proof_1.{u_1, u_2} (k : Type u_2) [Field k]
    {A N : Scheme.{u_1}} (g : A ⟶ A) (gN : N ⟶ N) (nu : N ⟶ A)
    [IsFinite g] [IsDominant g] [IsFinite gN] [IsDominant gN] [IsFinite nu] [IsDominant nu]
    [IsIntegral A] [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    [NoetherianSpace A] [CharZero (A.presheaf.stalk (genericPoint A))]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)] :
    gN ≫ nu = nu ≫ g →
      ∀ Q : SchemeDivisorPoint N,
        schemeDivisorMap nu (coheight_apply_eq_one_of_finiteType nu k)
            ((divDynOfFiniteNormalization gN nu).step Q) =
          schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k)
            (schemeDivisorMap nu (coheight_apply_eq_one_of_finiteType nu k) Q) := by sorry

/-- (Hole.) -/
theorem schemeNormalizationUnnormDynOfFiniteType._proof_2.{u_1} {A : Scheme.{u_1}} (g : A ⟶ A)
    [IsFinite g] : IsFinite g := by sorry

/-- (Hole.) -/
theorem schemeNormalizationUnnormDynOfFiniteType._proof_3.{u_1} {A : Scheme.{u_1}} (g : A ⟶ A)
    [IsDominant g] : IsDominant g := by sorry

/-- (Hole.) -/
theorem schemeNormalizationUnnormDynOfFiniteType._proof_4.{u_1} {A : Scheme.{u_1}} (g : A ⟶ A)
    [LocallyOfFinitePresentation g] : LocallyOfFinitePresentation g := by sorry

/-- (Hole.) The normalization map on divisors has finite fibres. -/
theorem schemeNormalizationUnnormDynOfFiniteType._proof_5.{u_1, u_2} (k : Type u_2) [Field k]
    {A N : Scheme.{u_1}} (nu : N ⟶ A) [IsFinite nu] [IsDominant nu]
    [IsIntegral A] [IsIntegral N]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)] (Q : SchemeDivisorPoint A) :
    (schemeDivisorMap nu (coheight_apply_eq_one_of_finiteType nu k) ⁻¹' {Q}).Finite := by sorry

/-- (Hole.) -/
theorem schemeNormalizationUnnormDynOfFiniteType._proof_6.{u_1} {A : Scheme.{u_1}}
    [IsIntegral A] : IsIntegral A := by sorry

/-- (Hole.) -/
theorem schemeNormalizationUnnormDynOfFiniteType._proof_7.{u_1} {A : Scheme.{u_1}}
    [NoetherianSpace A] : NoetherianSpace A := by sorry

/-- The package `SchemeNormalizationUnnormDyn` for `g : A ⟶ A`, a normal scheme `N` finite
dominant over `A` via `nu`, and a lift `gN` with `gN ≫ nu = nu ≫ g`: the normalized dynamics
is `divDynOfFiniteNormalization gN nu` and the normalization map is pushforward by `nu`. -/
noncomputable def schemeNormalizationUnnormDynOfFiniteType
    (k : Type*) [Field k]
    {A N : Scheme.{u}} (g : A ⟶ A) (gN : N ⟶ N) (nu : N ⟶ A)
    [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
    [IsFinite gN] [IsDominant gN]
    [IsFinite nu] [IsDominant nu]
    [IsIntegral A] [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    [NoetherianSpace A]
    [CharZero (A.presheaf.stalk (genericPoint A))]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]
    (hsquare : gN ≫ nu = nu ≫ g)
    (hU1 : ∀ m Q,
      1 < (divDynOfFiniteNormalization gN nu).iterRam m Q →
        schemeDivisorMap nu (coheight_apply_eq_one_of_finiteType nu k) Q ∈
          schemeDivisorCrit0 (CategoryTheory.End.of g ^ m).asHom) :
    SchemeNormalizationUnnormDyn A (SchemeDivisorPoint N) := {
    g := g
    finite := schemeNormalizationUnnormDynOfFiniteType._proof_2 g
    dominant := schemeNormalizationUnnormDynOfFiniteType._proof_3 g
    finitePresentation := schemeNormalizationUnnormDynOfFiniteType._proof_4 g
    g_preserves_divisors := coheight_apply_eq_one_of_finiteType g k
    norm := divDynOfFiniteNormalization gN nu
    normalization := schemeDivisorMap nu (coheight_apply_eq_one_of_finiteType nu k)
    normalization_step := fun Q ↦
      schemeNormalizationUnnormDynOfFiniteType._proof_1 k g gN nu hsquare Q
    normalization_finite_fiber := schemeNormalizationUnnormDynOfFiniteType._proof_5 k nu
    crit_subset_crit0 := hU1
    integral := schemeNormalizationUnnormDynOfFiniteType._proof_6
    noetherian := schemeNormalizationUnnormDynOfFiniteType._proof_7
    charZero := inferInstance }

/-- (Hole.) Normalized ramification lies over the non-formally-unramified locus when `nu` is
birational. -/
theorem schemeNormalizationUnnormDynOfFiniteBirational._proof_1.{u_1, u_2} (k : Type u_2)
    [Field k] {A N : Scheme.{u_1}} (g : A ⟶ A) (gN : N ⟶ N) (nu : N ⟶ A)
    [IsFinite g] [IsFinite gN] [IsDominant gN] [IsFinite nu] [IsDominant nu]
    [IsIntegral A] [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    [NoetherianSpace A] [CharZero (A.presheaf.stalk (genericPoint A))]
    [IsIso (nu.stalkMap (genericPoint N))]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)] :
    gN ≫ nu = nu ≫ g →
      ∀ (m : ℕ) (Q : SchemeDivisorPoint N),
        1 < (divDynOfFiniteNormalization gN nu).iterRam m Q →
          schemeDivisorMap nu (coheight_apply_eq_one_of_finiteType nu k) Q ∈
            schemeDivisorCrit0 (CategoryTheory.End.of g ^ m).asHom := by sorry

set_option backward.isDefEq.respectTransparency false in
/-- The same package when `nu` is birational (an isomorphism on generic stalks). -/
noncomputable def schemeNormalizationUnnormDynOfFiniteBirational
    (k : Type*) [Field k]
    {A N : Scheme.{u}} (g : A ⟶ A) (gN : N ⟶ N) (nu : N ⟶ A)
    [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
    [IsFinite gN] [IsDominant gN]
    [IsFinite nu] [IsDominant nu]
    [IsIntegral A] [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    [TopologicalSpace.NoetherianSpace A]
    [CharZero (A.presheaf.stalk (genericPoint A))]
    [IsIso (nu.stalkMap (genericPoint N))]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]
    (hsquare : gN ≫ nu = nu ≫ g) :
    SchemeNormalizationUnnormDyn A (SchemeDivisorPoint N) :=
  schemeNormalizationUnnormDynOfFiniteType k g gN nu hsquare
    (schemeNormalizationUnnormDynOfFiniteBirational._proof_1 k g gN nu hsquare)

/-- (Hole.) The lift of `g` to the normalization is finite. -/
theorem schemeGlobalNormalizationUnnormDyn._proof_1.{u_1} (k : Type u_1) [Field k] [CharZero k]
    {A : Scheme.{u_1}} (g : A ⟶ A) [IsFinite g] [IsDominant g] [IsIntegral A]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)] :
    IsFinite (schemeGlobalNormalizationLift g) := by sorry

/-- (Hole.) The lift of `g` to the normalization is dominant. -/
theorem schemeGlobalNormalizationUnnormDyn._proof_2.{u_1} {A : Scheme.{u_1}} (g : A ⟶ A)
    [IsFinite g] [IsDominant g] [IsIntegral A] :
    IsDominant (schemeGlobalNormalizationLift g) := by sorry

/-- (Hole.) The normalization is locally Noetherian. -/
theorem schemeGlobalNormalizationUnnormDyn._proof_3.{u_1} (k : Type u_1) [Field k] [CharZero k]
    {A : Scheme.{u_1}} [IsIntegral A] [IsLocallyNoetherian A]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)] :
    IsLocallyNoetherian (schemeGlobalNormalization A) := by sorry

/-- (Hole.) The lift commutes with the normalization map. -/
theorem schemeGlobalNormalizationUnnormDyn._proof_4.{u_1} {A : Scheme.{u_1}} (g : A ⟶ A)
    [IsFinite g] [IsDominant g] [IsIntegral A] :
    schemeGlobalNormalizationLift g ≫ schemeGlobalNormalizationMap A =
      schemeGlobalNormalizationMap A ≫ g := by sorry

/-- The package for `g` on the canonical normalization `Ã ⟶ A` with the lift of `g`, given
`k`-algebra structures of finite type on the affine rings of `A`. -/
noncomputable def schemeGlobalNormalizationUnnormDyn
    (k : Type u) [Field k] [CharZero k]
    {A : Scheme.{u}} (g : A ⟶ A)
    [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
    [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A]
    [CharZero (A.presheaf.stalk (genericPoint A))]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)] :
    SchemeNormalizationUnnormDyn A
      (SchemeDivisorPoint (schemeGlobalNormalization A)) := by
  letI : IsFinite (schemeGlobalNormalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite_of_affineFiniteType A k
  exact @schemeNormalizationUnnormDynOfFiniteBirational k _ A (schemeGlobalNormalization A) g
    (schemeGlobalNormalizationLift g) (schemeGlobalNormalizationMap A) _ _ _
    (schemeGlobalNormalizationUnnormDyn._proof_1 k g) (schemeGlobalNormalizationUnnormDyn._proof_2 g)
    _ _ _ _ (schemeGlobalNormalizationUnnormDyn._proof_3 k) _ _ _ _ _ _
    (schemeGlobalNormalizationUnnormDyn._proof_4 g)

/-- The same package, with the `k`-algebra structures on affine rings induced by a
structure morphism `s : A ⟶ Spec k` locally of finite type. -/
noncomputable def schemeGlobalNormalizationUnnormDynOfFiniteType
    (k : Type u) [Field k] [CharZero k]
    {A : Scheme.{u}} (s : A ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (g : A ⟶ A)
    [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
    [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A]
    [CharZero (A.presheaf.stalk (genericPoint A))] :
    SchemeNormalizationUnnormDyn A
      (SchemeDivisorPoint (schemeGlobalNormalization A)) := by
  let φ (U : A.affineOpens) : k →+* Γ(A, U) :=
    (s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let (U : A.affineOpens) : Algebra k Γ(A, U) := (φ U).toAlgebra
  have (U : A.affineOpens) : Algebra.FiniteType k Γ(A, U) := by
    apply RingHom.finiteType_algebraMap.mp
    change (φ U).FiniteType
    exact (s.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType
  exact schemeGlobalNormalizationUnnormDyn k g

/-! ## PCF all the way down -/

/-- The `k`-algebra structure on each stalk induced by a morphism to `Spec k`. -/
@[instance_reducible]
def schemeStalkAlgebraOfField (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x (by trivial)).hom.comp
    ((s.appLE ⊤ ⊤ (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra

/-- Characteristic zero of the ground field passes to each stalk. -/
theorem schemeStalkCharZeroOfField (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (x : X) :
    CharZero (X.presheaf.stalk x) := by
  let := schemeStalkAlgebraOfField k s x
  exact charZero_of_injective_ringHom (algebraMap k (X.presheaf.stalk x)).injective

/-- Normalized PCF: the normalized divisor dynamics of `f` on the canonical normalization
of `X` (with the `k`-structure from `s`) is post-critically finite. -/
noncomputable def SchemeNormalizedPCFOfFiniteType
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop := by
  letI := schemeStalkCharZeroOfField k s (genericPoint X)
  exact (schemeGlobalNormalizationUnnormDynOfFiniteType k s f).norm.PCF

/-- The `k`-algebra structure on each affine ring induced by a morphism to `Spec k`. -/
@[instance_reducible]
def schemeAffineAlgebraOfField
    (k : Type u) [Field k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    (U : X.affineOpens) : Algebra k Γ(X, U) :=
  ((s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra

/-- These affine algebras are of finite type when `s` is locally of finite type. -/
theorem schemeAffineAlgebraOfField_finiteType
    (k : Type u) [Field k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    [LocallyOfFiniteType s] (U : X.affineOpens) :
    letI := schemeAffineAlgebraOfField k s U
    Algebra.FiniteType k Γ(X, U) := by
  letI := schemeAffineAlgebraOfField k s U
  apply RingHom.finiteType_algebraMap.mp
  exact (s.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType

/-- The codimension-one point `f^r(A)`. -/
noncomputable def schemeDivisorIterateOfFiniteType
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X]
    (r : ℕ) (A : SchemeDivisorPoint X) : SchemeDivisorPoint X := by
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField k s U
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField_finiteType k s U
  exact schemeDivisorMap (End.of f ^ r).asHom
    (coheight_apply_eq_one_of_finiteType (End.of f ^ r).asHom k) A

/-- (Hole.) If `f^(r+p)(A) = f^r(A)` then `f^p` fixes `f^r(A)`. -/
theorem schemeDivisorIterateOfFiniteType_periodic
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X]
    (r p : ℕ) (A : SchemeDivisorPoint X)
    (hA : (End.of f ^ (r + p)).asHom.base A.1 = (End.of f ^ r).asHom.base A.1) :
    (End.of f ^ p).asHom.base (schemeDivisorIterateOfFiniteType k s f r A).1 =
      (schemeDivisorIterateOfFiniteType k s f r A).1 := by sorry

/-- PCF all the way down through `d` steps: normalized PCF for `f` on `X`, and, for `d + 1`,
also PCF all the way down through `d` steps for the return map `f^p` on the reduced closure
of `B = f^r(A)`, for every codimension-one point `A` with `f^(r+p)(A) = f^r(A)` and
`p ≥ 1`. -/
noncomputable def SchemePCFAllTheWayDownAtDepth
    (k : Type u) [Field k] [CharZero k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  match d with
  | 0 => SchemeNormalizedPCFOfFiniteType k s f
  | d + 1 =>
      SchemeNormalizedPCFOfFiniteType k s f ∧
        ∀ (A : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
          (hA : (End.of f ^ (r + p)).asHom.base A.1 = (End.of f ^ r).asHom.base A.1),
          let B := schemeDivisorIterateOfFiniteType k s f r A
          SchemePCFAllTheWayDownAtDepth k d
            ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
            (B.invariantClosureMap (End.of f ^ p).asHom
              (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA))

/-- The two assumed local theorems, for all commutative rings in universe `u`:
Zariski–Nagata purity (Stacks 0BMB) and Abhyankar's lemma (Stacks 0EYG/0EYH). -/
structure PcfAllTheWayDownLocalTheorems : Prop where
  purity : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    Stacks.ZariskiNagataPurity R S
  abhyankar : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R),
    Stacks.AbhyankarLemma R S a

/-- PCF all the way down: `SchemePCFAllTheWayDownAtDepth` at every depth. -/
noncomputable def SchemePCFAllTheWayDown
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  ∀ d, SchemePCFAllTheWayDownAtDepth k d s f

/-- **PCF all the way down in characteristic zero**, conditional on Zariski–Nagata purity
and Abhyankar's lemma. -/
theorem pcfAllTheWayDown_charZero
    (inputs : PcfAllTheWayDownLocalTheorems.{u})
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hpcf : SchemeNormalizedPCFOfFiniteType k s f) :
    SchemePCFAllTheWayDown k s f := by sorry

end Pcf
