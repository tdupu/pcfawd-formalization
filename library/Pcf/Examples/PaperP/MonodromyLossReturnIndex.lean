/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossReturnPCF
public import Pcf.Examples.PaperP.WildGlobalIndex
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Index `3` of the monodromy-loss return at `y = 0`

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: "It has index `3` at
`y = 0`, so its Galois closure has degree divisible by `3`."

The actual return `g : ℙ¹ ⟶ ℙ¹` sends `0` to `∞`. On the source chart
`v ≠ 0, u⁴ + v⁴ ≠ 0` (coordinate `t = u/v`) and the target chart `u ≠ 0`
(coordinate `w = v/u`) it is the polynomial chart map
`w ↦ t³ / (-i (t⁴ + 1))`, by the repository's all-chart identification
`Pcf.paperPForms_anyPolynomialDoubleChart_comp_map`. The local parameter `w`
therefore pulls back to `t³` times a unit at `t = 0`, so the actual stalk
ramification index of `g` at the scheme point `0` is `3`.

Consequently `g` does not have prime-to-`3` monodromy in the repository's
sense `Pcf.IsPrimeToPMonodromyMap`, the formal counterpart of "the Galois
closure has degree divisible by `3`": prime-to-`p` monodromy forces every
divisorial index to be prime to `p` (`Pcf.schemeDivisor_tame_of_primeToP`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace Pcf.Examples.PaperP.MonodromyLossReturn
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### A localized DVR length computation -/

/-- A quotient-length calculation in a localized DVR (copy of the private helper of
`WildAffineIndex`, with an explicit ring map). -/
theorem ramificationIdx_eq_of_localIdealPower'
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S)
    (I : Ideal R) (q : Ideal S) [q.IsPrime] (hq : q.comap f = I) (n : ℕ)
    [IsDiscreteValuationRing (Localization.AtPrime q)]
    (hmap : I.map ((algebraMap S (Localization.AtPrime q)).comp f) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n) :
    letI := f.toAlgebra
    q.ramificationIdx R = n := by
  letI := f.toAlgebra
  rw [Ideal.ramificationIdx_def, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q)]
  change (Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸
    (q.comap f).map ((algebraMap S (Localization.AtPrime q)).comp f))).toNat = n
  rw [hq, hmap, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]

universe u

/-- `Wild.specMap_ramificationIndexAt` for an explicit ring map rather than an
`Algebra` instance. -/
theorem specMap_ramificationIndexAt' {R S : Type u} [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] (φ : R →+* S) (q : Spec (.of S)) (P : Ideal R) [P.IsPrime]
    (hP : q.asIdeal.comap φ = P) [IsDiscreteValuationRing (Localization.AtPrime P)]
    (hinj : Function.Injective ((Spec.map (CommRingCat.ofHom φ)).stalkMap q).hom) :
    Pcf.Palomar.ramificationIndexAt (Spec.map (CommRingCat.ofHom φ)) q =
      (letI := φ.toAlgebra; q.asIdeal.ramificationIdx R) := by
  letI := φ.toAlgebra
  exact Wild.specMap_ramificationIndexAt q P hP hinj

/-! ### The polynomial charts around `0` and `∞` -/

variable (k : Type u) [Field k] (i : k)
local notation "t" => (X 0 : MvPolynomial (Fin 1) k)

/-- Source chart relabelling: the source chart is the standard chart `v ≠ 0`. -/
abbrev eS : Index ≃ Index := Equiv.refl _
/-- Target chart relabelling: the target chart is `u ≠ 0`, the chart around `∞`. -/
abbrev eT : Index ≃ Index := Equiv.swap (Sum.inl 0) (Sum.inr ())

/-- The forms reindexed for the source chart `v ≠ 0` and target chart `u ≠ 0`. -/
noncomputable abbrev chartForms : Index → Coordinates k :=
  Pcf.paperPReindexedForms (forms k i) eS eT.symm

/-- The polynomial ring of the chart `v ≠ 0, u⁴ + v⁴ ≠ 0`, coordinate `t = u/v`. -/
abbrev ChartRing := Pcf.PaperPChartRing (chartForms k i)

theorem chartDen : Pcf.paperPDehomogenize (chartForms k i (Sum.inr ())) =
    C (-i) * (t ^ 4 + 1) := by
  simp [Pcf.paperPReindexedForms, forms, Pcf.paperPDehomogenize]

theorem chartNum : Pcf.paperPDehomogenize (chartForms k i (Sum.inl 0)) = t ^ 3 := by
  simp [Pcf.paperPReindexedForms, forms, Pcf.paperPDehomogenize]

variable {i}

/-- The constant term of the chart denominator is `-i ≠ 0`. -/
theorem constantCoeff_chartDen (hi : i ^ 2 = -1) :
    constantCoeff (Pcf.paperPDehomogenize (chartForms k i (Sum.inr ()))) ≠ 0 := by
  rw [chartDen]
  simpa using i_ne_zero hi

variable (i)

/-- The prime `(t)` of `k[t]`. -/
noncomputable abbrev P0 : Ideal (MvPolynomial (Fin 1) k) := Ideal.span {t}

omit i in
theorem P0_eq_ker : P0 k = RingHom.ker (constantCoeff : MvPolynomial (Fin 1) k →+* k) := by
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp
  · intro x hx
    have hs : (Set.univ : Set (Fin 1)).image (X : Fin 1 → MvPolynomial (Fin 1) k) = {t} := by
      ext y
      simp [eq_comm]
    change x ∈ Ideal.span {t}
    rw [← hs, mem_ideal_span_X_image]
    intro m hm
    refine ⟨0, Set.mem_univ _, ?_⟩
    intro h0
    have hm0 : m = 0 := by
      refine Finsupp.ext fun a => ?_
      rw [Fin.fin_one_eq_zero a]
      exact h0
    subst hm0
    rw [RingHom.mem_ker, constantCoeff_eq] at hx
    exact (mem_support_iff.mp hm) hx

omit i in
theorem P0_isMaximal : (P0 k).IsMaximal := by
  rw [P0_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨C a, constantCoeff_C _ _⟩)

omit i in
theorem P0_height : (P0 k).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr (MvPolynomial.X_ne_zero (0 : Fin 1)))
    (MvPolynomial.X_prime (R := k) (i := (0 : Fin 1))).not_isUnit

omit i in
instance P0_isPrime : (P0 k).IsPrime := (P0_isMaximal k).isPrime

omit i in
theorem P0_isDVR : IsDiscreteValuationRing (Localization.AtPrime (P0 k)) := by
  exact Pcf.isDiscreteValuationRing_localizationAtPrime_of_heightOne _ (P0_height k)

variable {i}

theorem chartDen_notMem (hi : i ^ 2 = -1) :
    Pcf.paperPDehomogenize (chartForms k i (Sum.inr ())) ∉ P0 k := by
  rw [P0_eq_ker, RingHom.mem_ker]
  exact constantCoeff_chartDen k hi

theorem chartDen_ne_zero (hi : i ^ 2 = -1) :
    Pcf.paperPDehomogenize (chartForms k i (Sum.inr ())) ≠ 0 := by
  intro h
  apply chartDen_notMem k hi
  rw [h]
  exact zero_mem _

theorem powers_le (hi : i ^ 2 = -1) :
    Submonoid.powers (Pcf.paperPDehomogenize (chartForms k i (Sum.inr ()))) ≤
      nonZeroDivisors (MvPolynomial (Fin 1) k) :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (chartDen_ne_zero k hi)

/-- The chart ring is a domain. -/
theorem chartRing_isDomain (hi : i ^ 2 = -1) : IsDomain (ChartRing k i) :=
  IsLocalization.isDomain_localization (powers_le k hi)

/-- The prime `(t)` of the localized chart ring. -/
noncomputable abbrev Q0 : Ideal (ChartRing k i) :=
  Ideal.map (algebraMap (MvPolynomial (Fin 1) k) (ChartRing k i)) (P0 k)

theorem Q0_isPrime (hi : i ^ 2 = -1) : (Q0 k (i := i)).IsPrime := by
  haveI := (P0_isMaximal k).isPrime
  apply IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (Pcf.paperPDehomogenize (chartForms k i (Sum.inr ())))) _ _ inferInstance
  rw [Set.disjoint_left]
  rintro _ ⟨n, rfl⟩ hn
  exact chartDen_notMem k hi ((P0_isMaximal k).isPrime.mem_of_pow_mem n hn)

theorem Q0_eq : Q0 k (i := i) =
    Ideal.span {algebraMap (MvPolynomial (Fin 1) k) (ChartRing k i) t} := by
  change Ideal.map _ (Ideal.span _) = _
  rw [Ideal.map_span, Set.image_singleton]

theorem t_mem_Q0 : algebraMap (MvPolynomial (Fin 1) k) (ChartRing k i) t ∈ Q0 k (i := i) := by
  rw [Q0_eq]
  exact Ideal.subset_span rfl

theorem Q0_isDVR (hi : i ^ 2 = -1) :
    haveI := Q0_isPrime k hi
    haveI := chartRing_isDomain k hi
    IsDiscreteValuationRing (Localization.AtPrime (Q0 k (i := i))) := by
  haveI := Q0_isPrime k hi
  haveI := chartRing_isDomain k hi
  haveI : IsNoetherianRing (ChartRing k i) :=
    IsLocalization.isNoetherianRing
      (Submonoid.powers (Pcf.paperPDehomogenize (chartForms k i (Sum.inr ())))) _ inferInstance
  haveI : IsIntegrallyClosed (ChartRing k i) :=
    isIntegrallyClosed_of_isLocalization _
      (Submonoid.powers (Pcf.paperPDehomogenize (chartForms k i (Sum.inr ()))))
      (powers_le k hi)
  apply Pcf.isDiscreteValuationRing_localizationAtPrime_of_heightOne
  rw [Q0_eq]
  apply Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
  · apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro h
    have hinj := IsLocalization.injective (ChartRing k i) (powers_le k hi)
    exact MvPolynomial.X_ne_zero (0 : Fin 1) (hinj (h.trans (map_zero _).symm))
  · intro hu
    have h := t_mem_Q0 k (i := i)
    exact (Q0_isPrime k hi).ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

variable (i)

/-- The chart pullback `k[w] → k[t]_{t⁴+1}`, `w ↦ t³ / (-i (t⁴ + 1))`. -/
noncomputable abbrev chartPullback : MvPolynomial (Fin 1) k →+* ChartRing k i :=
  (Pcf.paperPChartPullback (chartForms k i)).toRingHom

theorem chartPullback_X : chartPullback k i t =
    algebraMap (MvPolynomial (Fin 1) k) (ChartRing k i) (t ^ 3) *
      ↑((Pcf.paperPChartDenominatorUnit (chartForms k i))⁻¹) := by
  change Pcf.paperPChartPullback (chartForms k i) (X 0) = _
  rw [Pcf.paperPChartPullback_X, chartNum]

variable {i}

theorem Q0_comap (hi : i ^ 2 = -1) : (Q0 k (i := i)).comap (chartPullback k i) = P0 k := by
  haveI := Q0_isPrime k hi
  symm
  apply (P0_isMaximal k).eq_of_le (Ideal.comap_ne_top _ (Q0_isPrime k hi).ne_top)
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
    chartPullback_X, map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (t_mem_Q0 k) 3 (by decide))

/-- **The chart index.** The prime `(t)` has ramification index `3` over `(w)`. -/
theorem chart_ramificationIdx (hi : i ^ 2 = -1) :
    haveI := Q0_isPrime k hi
    letI := (chartPullback k i).toAlgebra
    (Q0 k (i := i)).ramificationIdx (MvPolynomial (Fin 1) k) = 3 := by
  haveI := Q0_isPrime k hi
  haveI := chartRing_isDomain k hi
  haveI := Q0_isDVR k hi
  let L := Localization.AtPrime (Q0 k (i := i))
  apply ramificationIdx_eq_of_localIdealPower' (chartPullback k i) (P0 k) _ (Q0_comap k hi) 3
  rw [Ideal.map_span, Set.image_singleton, RingHom.comp_apply, chartPullback_X, map_mul,
    map_pow, map_pow]
  rw [Ideal.span_singleton_mul_right_unit
    (((Pcf.paperPChartDenominatorUnit (chartForms k i))⁻¹).isUnit.map
      (algebraMap (ChartRing k i) L)), ← Ideal.span_singleton_pow]
  congr 1
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  change _ = Ideal.map _ (Ideal.map _ (Ideal.span {t}))
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton]
  rfl

/-! ### Transport to the actual global return -/

/-- The actual open immersion of the polynomial chart `v ≠ 0, u⁴ + v⁴ ≠ 0`. -/
noncomputable abbrev sourceChart : Spec (.of (ChartRing k i)) ⟶ Proj (grading k) :=
  Pcf.paperPAnySourceChartToProj (forms k i) 4 (forms_homogeneous k i) eS eT

/-- The actual open immersion of the polynomial chart `u ≠ 0` around `∞`. -/
noncomputable abbrev targetChart : Spec (.of (MvPolynomial (Fin 1) k)) ⟶ Proj (grading k) :=
  Pcf.paperPAnyTargetChartToProj (K := k) eT

/-- The scheme point `(t)` of the source chart. -/
noncomputable def chartZero (hi : i ^ 2 = -1) : Spec (.of (ChartRing k i)) :=
  ⟨Q0 k (i := i), Q0_isPrime k hi⟩

variable (hi : i ^ 2 = -1) [CharP k 3]
include hi

omit [CharP k 3] in
/-- The actual return restricts on these charts to `Spec` of the chart pullback. -/
theorem chart_square :
    sourceChart k (i := i) ≫ schemeMap k i hi =
      Spec.map (CommRingCat.ofHom (chartPullback k i)) ≫ targetChart k :=
  Pcf.paperPForms_anyPolynomialDoubleChart_comp_map (forms k i) 4 (forms_homogeneous k i)
    (by decide) (forms_cover k hi) eS eT

omit [CharP k 3] in
theorem chartMap_ramificationIndexAt :
    Pcf.Palomar.ramificationIndexAt (Spec.map (CommRingCat.ofHom (chartPullback k i)))
      (chartZero k hi) = 3 := by
  haveI := chartRing_isDomain k hi
  haveI := (P0_isMaximal k).isPrime
  haveI := P0_isDVR k
  have hinjF : Function.Injective ((schemeMap k i hi).stalkMap
      (sourceChart k (i := i) (chartZero k hi))).hom :=
    Pcf.stalkMap_injective_of_dominant_integral _ _
  have hinj := Wild.stalkMap_injective_of_openSquare _ _ _ _ (chart_square k hi) _ hinjF
  rw [specMap_ramificationIndexAt' (chartPullback k i) (chartZero k hi) (P0 k)
    (Q0_comap k hi) hinj]
  exact chart_ramificationIdx k hi

/-- The source chart point `(t)` is the projective scheme point `0`. -/
theorem sourceChart_chartZero :
    sourceChart k (i := i) (chartZero k hi) = BasilicaProjectiveScheme.zero k := by
  by_contra hne
  have h1 := ramificationIndexAt_eq_one_of_ne k hi _ hne
  rw [Wild.ramificationIndexAt_of_openSquare _ _ _ _ (chart_square k hi),
    chartMap_ramificationIndexAt] at h1
  omega

/-- **"It has index `3` at `y = 0`."** The actual stalk ramification index of
the actual return `g : ℙ¹ ⟶ ℙ¹` at the scheme point `0` is `3`. -/
theorem ramificationIndexAt_zero :
    Pcf.Palomar.ramificationIndexAt (schemeMap k i hi) (BasilicaProjectiveScheme.zero k) = 3 := by
  rw [← sourceChart_chartZero k hi,
    Wild.ramificationIndexAt_of_openSquare _ _ _ _ (chart_square k hi),
    chartMap_ramificationIndexAt]

/-- The same index in the repository's divisorial notation. -/
theorem schemeDivisorRamificationIdx_zeroDivisor :
    Pcf.schemeDivisorRamificationIdx (schemeMap k i hi)
      (BasilicaProjectiveScheme.zeroDivisor k) = 3 :=
  ramificationIndexAt_zero k hi

/-- The index at `0` is ramified and wild: it is `> 1` and divisible by the
characteristic `3`. -/
theorem wildlyRamified_zero :
    1 < Pcf.Palomar.ramificationIndexAt (schemeMap k i hi) (BasilicaProjectiveScheme.zero k) ∧
      3 ∣ Pcf.Palomar.ramificationIndexAt (schemeMap k i hi)
        (BasilicaProjectiveScheme.zero k) := by
  rw [ramificationIndexAt_zero k hi]
  exact ⟨by decide, dvd_rfl⟩

/-- **"So its Galois closure has degree divisible by `3`."** The actual return
does not have prime-to-`3` monodromy (`Pcf.IsPrimeToPMonodromyMap 3`): such
monodromy would make every divisorial index prime to `3`. -/
theorem not_isPrimeToPMonodromyMap : ¬ Pcf.IsPrimeToPMonodromyMap 3 (schemeMap k i hi) := by
  intro hmono
  have h := (Pcf.schemeDivisor_tame_of_primeToP 3 Nat.prime_three k
    (BasilicaProjectiveScheme.structureMap k) (schemeMap k i hi) hmono
    (BasilicaProjectiveScheme.zeroDivisor k)).1
  exact h (by rw [schemeDivisorRamificationIdx_zeroDivisor k hi])

#print axioms P0_eq_ker
#print axioms Q0_isDVR
#print axioms Q0_comap
#print axioms chart_ramificationIdx
#print axioms chart_square
#print axioms sourceChart_chartZero
#print axioms ramificationIndexAt_zero
#print axioms not_isPrimeToPMonodromyMap

end Pcf.Examples.PaperP.MonodromyLossReturn
