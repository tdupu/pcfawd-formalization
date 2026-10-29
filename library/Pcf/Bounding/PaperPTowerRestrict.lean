/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPTower.RestrictionMonodromy
public import Pcf.Bounding.PaperPTowerAffineCharts
public import Pcf.Bounding.PaperPTowerChartClosure
public import Pcf.Bounding.PaperPTowerChartLocality
public import Pcf.Bounding.PaperPTowerUniformLowerBad
public import Pcf.Bounding.PrimeToPMonodromyOpenSquare

/-!
# The PCF clause of `thm:tower-restrict` in characteristic `p`

`paper-p.tex`, Theorem `thm:tower-restrict`: let `(Xₙ, hₙ)` be a PCF tower of
branched covers of normal varieties with monodromy not divisible by `p`, let
`A₀ ⊊ X₀` be an integral closed subvariety and `Aₙ ⊆ Xₙ` integral closed
subvarieties with `hₙ(Aₙ) = Aₙ₋₁`. Then `(Aₙ, hₙ|_{Aₙ})` is a PCF tower with
monodromy not divisible by `p`.

The tower and monodromy clauses were proved in
`Pcf.PaperPTower.CompatibleCentres.restrictedTower` and
`restrictedTower_monodromyNotDivisibleBy`. This file proves the PCF clause.

## Route

The manuscript blows up `X₀` along `A₀` globally. Since the conclusion is a
finiteness statement about codimension-one points of `A₀`, it is proved here
on a finite affine cover of `X₀` instead, with no global normalized blow-up:

* on an affine chart `U = Spec R` containing the generic point of `A₀`, the
  inverse images of `U` in the levels form finite normal affine covers
  (`Tower.chartCover`); their branch images are finite because the tower is
  PCF, and their monodromy is prime to `p`;
* the affine normalized Rees blow-up of `R` along the prime of `A₀` supplies,
  through `thm:bounding` (fixed family `W`) and `prop:bound-blowup`, one
  finite bad set for every level (`exists_uniform_lower_branch_bad_charP`);
* for each level, a codimension-one exceptional source point over the generic
  point of `Aₙ₊₁` exists because that generic point is minimal over the
  extended centre;
* the chart closures of `Aₙ₊₁` and `A₀` are the inverse images of the global
  closures (`pointClosure_isPullback_of_isOpenImmersion`), so normalized
  weighted branch points of `Aₙ₊₁ → A₀` in the chart are branch points of the
  chart map (`mem_weightedBranchPointSet_of_open_chart`).

## Divergence from the manuscript proof

The source proof constructs a global normalized blow-up `Y'` and global lifts
`f'ₙ`. This file uses the affine charts of that construction directly and
glues only the finite bad sets. The hypothesis "`A₀ ⊊ X₀`" is
`C.point 0 ≠ genericPoint (T.X 0)`, and normality of the levels is the
instance hypothesis `∀ n, IsNormalScheme (T.X n)`. PCF of the ambient tower is
`Tower.IsNormalizedPCF`, which coincides with the normal-level `Tower.IsPCF`
branch support. The characteristic-zero clause is not treated here.
-/

@[expose] public section

namespace Pcf.PaperPTower

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Pcf.Bounding.AllCodimBlowup

universe u

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- The spectrum of a normal domain is normal in the affine-coordinate sense. -/
theorem isNormalScheme_spec (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    Pcf.IsNormalScheme (Spec (.of R)) := by
  apply Pcf.isNormalScheme_of_stalk_integrallyClosed
  intro p
  haveI : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso (.of R) p).symm.commRingCatIsoToRingEquiv

/-- The `k`-algebra structure on the sections of an affine open of a scheme over `k`. -/
abbrev chartAlgebra {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (.of k))
    (U : X.affineOpens) : Algebra k Γ(X, U) :=
  ((t.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra

theorem chartAlgebra_finiteType {k : Type u} [Field k] {X : Scheme.{u}}
    (t : X ⟶ Spec (.of k)) [LocallyOfFiniteType t] (U : X.affineOpens) :
    letI := chartAlgebra t U
    Algebra.FiniteType k Γ(X, U) := by
  letI := chartAlgebra t U
  apply RingHom.finiteType_algebraMap.mp
  change ((t.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).FiniteType
  exact (t.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType

/-- For a tower of normal varieties, the normal-level PCF condition of
Definition `def:tower` gives the normalized one. -/
theorem Tower.isNormalizedPCF_of_isPCF {k : Type u} [Field k] (T : Tower k) (h : T.IsPCF) :
    T.IsNormalizedPCF := by
  obtain ⟨hnormal, hfin⟩ := h
  haveI := hnormal
  unfold Tower.IsNormalizedPCF
  convert hfin using 3 with n
  rw [Tower.normalizedBranchGenericPoints_eq_weighted,
    weightedBranchPointSet_eq_schemeDivisorBranchImage]
  rfl

namespace CompatibleCentres

variable {k : Type u} [Field k] {T : Tower k} (C : CompatibleCentres T)

set_option maxHeartbeats 3200000 in
/-- **The per-chart bound.** On one affine chart `U` of `X₀` containing the
generic point of `A₀`, one finite set of points of `X₀` contains every
normalized weighted branch generic point in `U` of every restricted composite
`Aₙ₊₁ → A₀`. -/
theorem chart_restrictedComposite_branch_bound
    (p : ℕ) (hp : p.Prime) [CharP k p] [∀ n, IsNormalScheme (T.X n)]
    (hpcf : T.IsNormalizedPCF) (hmono : T.MonodromyNotDivisibleBy p)
    (hproper : C.point 0 ≠ genericPoint (T.X 0))
    (U : (T.X 0).affineOpens) (hU : C.point 0 ∈ (U : (T.X 0).Opens)) :
    ∃ S : Set (T.X 0), S.Finite ∧
      ∀ n, ∀ D ∈ weightedBranchPointSet (C.restrictedComposite (n + 1)),
      (pointClosureIdealSheaf (C.point 0)).subschemeι D ∈ (U : (T.X 0).Opens) →
      (pointClosureIdealSheaf (C.point 0)).subschemeι D ∈ S := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nonempty (U : (T.X 0).Opens) := ⟨⟨_, hU⟩⟩
  letI : Algebra k Γ(T.X 0, U) := chartAlgebra (T.base 0) U
  haveI : Algebra.FiniteType k Γ(T.X 0, U) := chartAlgebra_finiteType (T.base 0) U
  haveI : IsNoetherianRing Γ(T.X 0, U) := Algebra.FiniteType.isNoetherianRing k _
  haveI : IsIntegrallyClosed Γ(T.X 0, U) := IsNormalScheme.component_integrallyClosed U
  haveI : IsNormalScheme (Spec (.of Γ(T.X 0, U))) := isNormalScheme_spec _
  let Cn := T.chartCover U
  let j : Spec (.of Γ(T.X 0, U)) ⟶ T.X 0 := U.2.fromSpec
  haveI : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have hcomm : ∀ n, (Cn n).specMap ≫ j = T.chartSourceι U n ≫ T.composite (n + 1) :=
    T.chartCover_comm U
  have hpcfC : (⋃ n, schemeDivisorBranchImage (Cn n).specMap).Finite :=
    NormalAffineFiniteCover.originalBranchImages_finite_of_open_towerCharts k T hpcf Cn j
      (T.chartSourceι U) hcomm
  have hmono' : ∀ m, IsPrimeToPMonodromyMap p (T.composite (m + 1)) := by
    simpa [Tower.MonodromyNotDivisibleBy, hp.ne_zero] using hmono
  have hmonoC : ∀ n,
      letI : IsFinite (Cn n).specMap := affineSpecMap_isFinite (Cn n).f (Cn n).finite
      letI : IsDominant (Cn n).specMap := affineSpecMap_isDominant (Cn n).f (Cn n).injective
      IsPrimeToPMonodromyMap p (Cn n).specMap := by
    intro n
    letI : IsFinite (Cn n).specMap := affineSpecMap_isFinite (Cn n).f (Cn n).finite
    letI : IsDominant (Cn n).specMap := affineSpecMap_isDominant (Cn n).f (Cn n).injective
    exact isPrimeToPMonodromyMap_of_openImmersion_square p (Cn n).specMap
      (T.chartSourceι U n) j (T.composite (n + 1)) (hcomm n) (hmono' n)
  -- the centre prime and a nonzero element of it
  let p0 : Spec (.of Γ(T.X 0, U)) := U.2.primeIdealOf ⟨C.point 0, hU⟩
  have hj0 : j p0 = C.point 0 := U.2.fromSpec_primeIdealOf ⟨C.point 0, hU⟩
  let I : Ideal Γ(T.X 0, U) := p0.asIdeal
  have hI : I.FG := IsNoetherian.noetherian I
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (allCodimCentrePrime_ne_bot U (C.point 0) hU hproper)
  let a' : I := ⟨a, haI⟩
  obtain ⟨Bad, hBad, hspec⟩ :=
    NormalAffineFiniteCover.exists_uniform_lower_branch_bad_charP p k I hI a' ha Cn hpcfC hmonoC
  refine ⟨j '' Bad, hBad.image _, ?_⟩
  intro n D hD hDU
  -- the chart at level `n + 1`
  let i := T.chartSourceι U n
  let f := (Cn n).f
  let φ := (Cn n).specMap
  have hmemV : C.point (n + 1) ∈ T.chartOpen U n := by
    change T.composite (n + 1) (C.point (n + 1)) ∈ (U : (T.X 0).Opens)
    rw [C.composite_point]
    exact hU
  let P : Spec (.of (Cn n).S) :=
    (T.chartOpen_isAffine U n).primeIdealOf ⟨C.point (n + 1), hmemV⟩
  have hiP : i P = C.point (n + 1) :=
    (T.chartOpen_isAffine U n).fromSpec_primeIdealOf ⟨C.point (n + 1), hmemV⟩
  have hφP : φ P = p0 := by
    apply j.isOpenEmbedding.injective
    have h := congrArg (fun m => m P) (hcomm n)
    simp only [Scheme.Hom.comp_apply] at h
    change j (φ P) = j p0
    rw [h, hj0]
    change T.composite (n + 1) (i P) = C.point 0
    rw [hiP, C.composite_point]
  have hcomap : P.asIdeal.comap f = I := by
    change (φ P).asIdeal = p0.asIdeal
    rw [hφP]
  letI : Algebra Γ(T.X 0, U) (Cn n).S := f.toAlgebra
  haveI : Algebra.IsIntegral Γ(T.X 0, U) (Cn n).S :=
    ⟨fun x => (RingHom.IsIntegral.of_finite (Cn n).finite) x⟩
  have hmin : P.asIdeal ∈ (I.map f).minimalPrimes := by
    have h := Ideal.IsIntegral.mem_minimalPrimes_map_under (R := Γ(T.X 0, U)) P.asIdeal
    rw [Ideal.under, show (algebraMap Γ(T.X 0, U) (Cn n).S) = f from rfl, hcomap] at h
    exact h
  letI : Algebra k (Cn n).S := (f.comp (algebraMap k Γ(T.X 0, U))).toAlgebra
  haveI : Algebra.FiniteType k (Cn n).S :=
    RingHom.finiteType_algebraMap.mp
      ((Cn n).finite.to_finiteType.comp (RingHom.finiteType_algebraMap.mpr inferInstance))
  let b : I.map f := mappedCenterElement f I a'
  have hb : (b : (Cn n).S) ≠ 0 := mappedCenterElement_ne_zero f (Cn n).injective I a' ha
  obtain ⟨x, hx⟩ := exists_normalizedRees_divisorPoint_over_minimalPrime k (I.map f)
    (hI.map f) b hb P.asIdeal hmin
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a' ha
  letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
  let F := normalizedReesProjMap f (Cn n).injective (Cn n).finite I a' ha
  let α := normalizedReesProjToSpec (I.map f) b hb
  let β := normalizedReesProjToSpec I a' ha
  have hαx : α x.1 = P := PrimeSpectrum.ext (congrArg PrimeSpectrum.asIdeal hx)
  have hbase : φ (α x.1) = β (F x.1) := by
    have h := congrArg (fun m => m x.1)
      (normalizedReesProjToSpec_comm f (Cn n).injective (Cn n).finite I a' ha)
    simp only [Scheme.Hom.comp_apply] at h
    exact h.symm
  have hβF : β (F x.1) = p0 := by rw [← hbase, hαx, hφP]
  have hexc : F x.1 ∈ (normalizedReesExceptionalIdealSheaf I a' ha).support := by
    change F x.1 ∈ ((normalizedReesExceptionalIdealSheaf I a' ha).support :
      Set (Palomar.normalization (reesProj I)))
    rw [normalizedReesExceptionalIdealSheaf_support I a' ha]
    change β (F x.1) ∈ PrimeSpectrum.zeroLocus (I : Set Γ(T.X 0, U))
    rw [hβF, PrimeSpectrum.mem_zeroLocus]
  have key := hspec n x hexc
  dsimp only at key
  -- the two chart closures and their inclusions into the global closures
  let W₀ := (pointClosureIdealSheaf (α x.1)).subscheme
  let Z₀ := (pointClosureIdealSheaf (β (F x.1))).subscheme
  let g := pointClosureSubschemeMap φ (α x.1) (β (F x.1)) hbase
  let hSource := normalizedRees_source_pointClosures_finiteNormalization
    k f (Cn n).injective (Cn n).finite I hI a' ha x.1
  letI : IsLocallyNoetherian W₀ := hSource.2.1
  letI : IsFinite (Palomar.normalizationMap W₀) := hSource.2.2.2
  let sR : Spec (.of Γ(T.X 0, U)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Γ(T.X 0, U)))
  letI : LocallyOfFiniteType sR := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  letI : IsLocallyNoetherian Z₀ := inferInstance
  letI : LocallyOfFiniteType ((pointClosureIdealSheaf (β (F x.1))).subschemeι ≫ sR) :=
    inferInstance
  letI : IsFinite (Palomar.normalizationMap Z₀) :=
    schemeGlobalNormalizationMap_isFinite Z₀ k
      ((pointClosureIdealSheaf (β (F x.1))).subschemeι ≫ sR)
  letI : IsFinite φ := affineSpecMap_isFinite f (Cn n).finite
  letI : IsDominant φ := affineSpecMap_isDominant f (Cn n).injective
  letI : IsFinite g := pointClosureSubschemeMap_isFinite _ _ _ _
  letI : IsDominant g := pointClosureSubschemeMap_isDominant _ _ _ _
  have hjβ : j (β (F x.1)) = C.point 0 := by rw [hβF, hj0]
  have hiα : i (α x.1) = C.point (n + 1) := by rw [hαx, hiP]
  let jc := pointClosureSubschemeMap j (β (F x.1)) (C.point 0) hjβ
  let ic := pointClosureSubschemeMap i (α x.1) (C.point (n + 1)) hiα
  obtain ⟨Dc, hDc⟩ := pointClosure_mem_range_of_isOpenImmersion j _ _ hjβ D (by
    have hr := U.2.range_fromSpec
    change _ ∈ Set.range U.2.fromSpec
    rw [hr]
    exact hDU)
  have hw : g ≫ jc = ic ≫ C.restrictedComposite (n + 1) :=
    pointClosureSubschemeMap_chart_square φ i j (T.composite (n + 1)) (hcomm n)
      (α x.1) (β (F x.1)) (C.point (n + 1)) (C.point 0) hbase hiα hjβ
      (C.composite_point (n + 1))
  have hrange : ∀ w, C.restrictedComposite (n + 1) w ∈ Set.range jc → w ∈ Set.range ic :=
    fun w hw' => pointClosureSubschemeMap_chart_range i j (T.composite (n + 1))
      (T.chartCover_range U n) (α x.1) (β (F x.1)) (C.point (n + 1)) (C.point 0)
      hiα hjβ (C.composite_point (n + 1)) w hw'
  have hDcmem : Dc ∈ weightedBranchPointSet g :=
    Pcf.mem_weightedBranchPointSet_of_open_chart g (C.restrictedComposite (n + 1)) ic jc
      hw hrange Dc (by rw [hDc]; exact hD)
  have hDccoh : Order.coheight Dc = 1 :=
    weightedBranchPointSet_coheight_one k
      ((pointClosureIdealSheaf (β (F x.1))).subschemeι ≫ sR) g hDcmem
  by_contra hnot
  refine key ⟨Dc, hDccoh⟩ ?_ hDcmem
  intro hBadmem
  apply hnot
  refine ⟨(pointClosureIdealSheaf (β (F x.1))).subschemeι Dc, hBadmem, ?_⟩
  have h1 := congrArg (fun m => m Dc) (pointClosureSubschemeMap_subschemeι j _ _ hjβ)
  simp only [Scheme.Hom.comp_apply] at h1
  rw [← h1]
  change (pointClosureIdealSheaf (C.point 0)).subschemeι (jc Dc) = _
  rw [hDc]

set_option maxHeartbeats 800000 in
/-- **`paper-p.tex`, Theorem `thm:tower-restrict`, PCF clause (characteristic
`p`).** For a PCF tower of normal varieties with monodromy not divisible by
`p`, and compatible integral closed subvarieties `Aₙ` with `A₀ ⊊ X₀`, one
finite set contains the normalized weighted branch generic points of every
restricted composite `Aₙ₊₁ → A₀`. -/
theorem restrictedComposite_uniform_branch_bound
    (p : ℕ) (hp : p.Prime) [CharP k p] [∀ n, IsNormalScheme (T.X n)]
    (hpcf : T.IsNormalizedPCF) (hmono : T.MonodromyNotDivisibleBy p)
    (hproper : C.point 0 ≠ genericPoint (T.X 0)) :
    ∃ S : Set (C.level 0), S.Finite ∧
      ∀ n, weightedBranchPointSet (C.restrictedComposite (n + 1)) ⊆ S := by
  classical
  let X₀ := T.X 0
  let ι := (pointClosureIdealSheaf (C.point 0)).subschemeι
  have hcov : (Set.univ : Set X₀) ⊆ ⋃ U : X₀.affineOpens, (U : Set X₀) := by
    intro x _
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X₀.Opens) from trivial)
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  obtain ⟨cov, hcov'⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X₀.affineOpens => (U : Set X₀)) (fun U => U.1.isOpen) hcov
  let SU : X₀.affineOpens → Set X₀ := fun U =>
    if hU : C.point 0 ∈ (U : X₀.Opens) then
      Classical.choose (C.chart_restrictedComposite_branch_bound p hp hpcf hmono hproper U hU)
    else ∅
  have hSU (U : X₀.affineOpens) : (SU U).Finite := by
    by_cases hU : C.point 0 ∈ (U : X₀.Opens)
    · simp only [SU, hU, ↓reduceDIte]
      exact (Classical.choose_spec
        (C.chart_restrictedComposite_branch_bound p hp hpcf hmono hproper U hU)).1
    · simp only [SU, hU, ↓reduceDIte]
      exact Set.finite_empty
  let SX : Set X₀ := ⋃ U ∈ cov, SU U
  have hSX : SX.Finite := Set.Finite.biUnion cov.finite_toSet fun U _ => hSU U
  refine ⟨ι ⁻¹' SX, hSX.preimage ι.isClosedEmbedding.injective.injOn, ?_⟩
  intro n D hD
  obtain ⟨U, hUcov, hDU⟩ : ∃ U ∈ cov, ι D ∈ (U : X₀.Opens) := by
    have := hcov' (Set.mem_univ (ι D))
    simp only [Set.mem_iUnion] at this
    obtain ⟨U, hU, hx⟩ := this
    exact ⟨U, hU, hx⟩
  have hyU : C.point 0 ∈ (U : X₀.Opens) :=
    (Pcf.pointClosure_specializes (C.point 0) D).mem_open U.1.isOpen hDU
  have hspec := (Classical.choose_spec
    (C.chart_restrictedComposite_branch_bound p hp hpcf hmono hproper U hyU)).2 n D hD hDU
  refine Set.mem_biUnion hUcov ?_
  simp only [SU, hyU, ↓reduceDIte]
  exact hspec

/-- **`paper-p.tex`, Theorem `thm:tower-restrict` (characteristic `p`).**
The restricted tower `(Aₙ, hₙ|_{Aₙ})` of a PCF tower of normal varieties with
monodromy not divisible by `p`, along compatible integral closed
subvarieties with `A₀ ⊊ X₀`, is a PCF tower (normalized weighted branch
loci) with monodromy not divisible by `p`. The tower structure itself is
`restrictedTower`.

`paper-p.tex` correspondence: Remark 5.6 (`rem:higher-codim`), Theorem 8.2 (`thm:tower-restrict`).
-/
theorem restrictedTower_isNormalizedPCF_and_monodromy
    (p : ℕ) (hp : p.Prime) [CharP k p] [∀ n, IsNormalScheme (T.X n)]
    (hpcf : T.IsNormalizedPCF) (hmono : T.MonodromyNotDivisibleBy p)
    (hproper : C.point 0 ≠ genericPoint (T.X 0)) :
    (C.restrictedTower p hp hmono).IsNormalizedPCF ∧
      (C.restrictedTower p hp hmono).MonodromyNotDivisibleBy p :=
  ⟨C.restrictedTower_isNormalizedPCF_of_uniform_branch_bound p hp hmono
      (C.restrictedComposite_uniform_branch_bound p hp hpcf hmono hproper),
    C.restrictedTower_monodromyNotDivisibleBy p hp hmono⟩

/-- `thm:tower-restrict` (characteristic `p`) with the ambient hypothesis in
the normal-level form `Tower.IsPCF`, which includes normality of every level.

`paper-p.tex` correspondence: Theorem 8.2 (`thm:tower-restrict`). -/
theorem restrictedTower_isNormalizedPCF_and_monodromy_of_isPCF
    (p : ℕ) (hp : p.Prime) [CharP k p]
    (hpcf : T.IsPCF) (hmono : T.MonodromyNotDivisibleBy p)
    (hproper : C.point 0 ≠ genericPoint (T.X 0)) :
    letI : ∀ n, IsNormalScheme (T.X n) := hpcf.1
    (C.restrictedTower p hp hmono).IsNormalizedPCF ∧
      (C.restrictedTower p hp hmono).MonodromyNotDivisibleBy p :=
  letI : ∀ n, IsNormalScheme (T.X n) := hpcf.1
  C.restrictedTower_isNormalizedPCF_and_monodromy p hp
    (T.isNormalizedPCF_of_isPCF hpcf) hmono hproper

#print axioms chart_restrictedComposite_branch_bound
#print axioms restrictedComposite_uniform_branch_bound
#print axioms restrictedTower_isNormalizedPCF_and_monodromy
#print axioms restrictedTower_isNormalizedPCF_and_monodromy_of_isPCF
#print axioms Tower.isNormalizedPCF_of_isPCF

end CompatibleCentres

end
end Pcf.PaperPTower
