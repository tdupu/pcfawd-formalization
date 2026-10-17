/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.Chart
public import Pcf.Bounding.Divisors
public import Pcf.Bounding.FiberProduct
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Etale.Field

/-!
# The bounding theorem on the two-dimensional local chart

The generic point of a divisor `E` of the invariant divisor `B` has codimension two in the
normal ambient variety.  Instead of first shrinking to a regular affine open, one may work
in the two-dimensional local ring at that point.  This file packages exactly that local
input and proves that it supplies the global regular-ring fields expected by
`Pcf.BoundingChart`.

This removes regular-locus openness from the algebraic bridge.  The key low-dimensional
facts are proved in `Pcf.Bounding.Divisors`:

* a one-dimensional regular local ring is a domain and a regular ring;
* a two-dimensional normal regular local domain is a regular ring.

Consequently the existing purity-and-Abhyankar derivation applies verbatim to the local
chart.  Noetherianity of the cover is derived from module-finiteness, and height equality
for the finite map is derived from finiteness, injectivity, and normality of the base.
Normality of every prime localization of the cover is derived from the single ordinary
`IsIntegrallyClosed S` hypothesis. Generic étaleness is derived from finiteness,
dominance, and characteristic zero.  Finally, the canonical-localization constructors
derive the finite, faithful, normal local cover and its selected minimal component from
a finite dominant normal algebra and honest height-one divisor ideals.
What remains outside this file is the scheme/stalk construction of the rings and ideals
below and the identification with the divisor dynamics; no field here asserts the
étaleness conclusion of the bounding theorem.
-/

@[expose] public section

/- The vendored low-priority instance `IsRegularLocalRing R → IsDomain R` (mathlib4 PR #29802) is
not used in this file, and it makes instance search for `FaithfulSMul` between localizations time
out here. -/
attribute [-instance] Pcf.Vendor.instIsDomainOfIsRegularLocalRing_pcf

universe u

set_option linter.style.haveILetI false

namespace Pcf

/-- In a domain, an element whose quotient lowers Krull dimension from two to one is a
nonzerodivisor.

Only nonzeroness needs proof. If the element were zero, quotienting by its span would be
ring-equivalent to the original ring, contradicting the two dimension equalities. -/
theorem mem_nonZeroDivisors_of_ringKrullDim_eq_two_of_quotient_eq_one
    {R : Type u} [CommRing R] [IsDomain R] {a : R}
    (hdim : ringKrullDim R = 2)
    (hquot : ringKrullDim (R ⧸ Ideal.span {a}) = 1) :
    a ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro ha
  subst a
  have heq : ringKrullDim (R ⧸ (⊥ : Ideal R)) = ringKrullDim R :=
    RingEquiv.ringKrullDim (RingEquiv.quotientBot R)
  have hspan : Ideal.span ({0} : Set R) = ⊥ := by simp
  rw [hspan, heq, hdim] at hquot
  norm_num at hquot

/-- A local effective-Cartier equation with one-dimensional quotient forces the
ambient local ring to have dimension two.

This is the dimension calculation used in Step 0.  It is the equality case of
Stacks Tag 00KW, already proved in Mathlib: quotienting a Noetherian local ring by
a nonzerodivisor in its maximal ideal lowers Krull dimension by exactly one. -/
theorem ringKrullDim_eq_two_of_cartier_quotient_eq_one
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {a : R} (ha : a ∈ nonZeroDivisors R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hquot : ringKrullDim (R ⧸ Ideal.span {a}) = 1) :
    ringKrullDim R = 2 := by
  rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    ha ham, hquot]
  norm_num

/-- A finite normal domain over `R` is the integral closure of `R` inside any principal
localization obtained by inverting a nonzerodivisor of the normal domain.

This is the normalization statement needed by the bounding chart.  The proof embeds the
principal localization into the fraction field, uses normality there, and then applies
transitivity of integrality from module-finiteness. -/
theorem isIntegralClosure_localizationAway_of_finite_of_integrallyClosed
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [IsDomain S] [IsIntegrallyClosed S]
    (a : R) (ha : algebraMap R S a ∈ nonZeroDivisors S) :
    IsIntegralClosure S R (Localization.Away (algebraMap R S a)) := by
  let s : S := algebraMap R S a
  let T := Localization.Away s
  let K := FractionRing S
  have hM : Submonoid.powers s ≤ nonZeroDivisors S := by
    rw [Submonoid.powers_le]
    exact ha
  letI : Algebra T K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      T K (Submonoid.powers s) (nonZeroDivisors S) hM
  letI : IsScalarTower S T K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      T K (Submonoid.powers s) (nonZeroDivisors S) hM
  letI : IsFractionRing T K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers s) T K
  have hinj : Function.Injective (algebraMap T K) :=
    IsFractionRing.injective T K
  let _ : IsIntegrallyClosedIn S T :=
    (IsScalarTower.toAlgHom S T K).isIntegrallyClosedIn hinj inferInstance
  let _ : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  exact IsIntegralClosure.of_isIntegrallyClosedIn

/-- Injectivity of a finite cover survives simultaneous localization of the base at a
prime and of the cover at the image of the prime complement. -/
theorem faithfulSMul_localization_algebraMapSubmonoid
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [FaithfulSMul R S] [IsDomain R] [IsDomain S]
    (q : Ideal R) [q.IsPrime] :
    FaithfulSMul (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact localizationAlgebra_injective _ _
    (FaithfulSMul.algebraMap_injective R S)

/-- Normality of the cover survives localization at the image of a prime complement.

The image submonoid consists of nonzerodivisors because the original finite cover is
dominant and both rings are domains. -/
theorem isIntegrallyClosed_localization_algebraMapSubmonoid
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed S] [FaithfulSMul R S]
    (q : Ideal R) [q.IsPrime] :
    IsIntegrallyClosed
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) := by
  apply isIntegrallyClosed_of_isLocalization _
    (Algebra.algebraMapSubmonoid S q.primeCompl)
  exact map_le_nonZeroDivisors_of_injective _
    (FaithfulSMul.algebraMap_injective R S)
    q.primeCompl_le_nonZeroDivisors

/-- If every positive natural number is a unit in a domain, then the domain has
characteristic zero. -/
theorem charZero_of_isUnit_natCast
    {R : Type u} [CommRing R] [IsDomain R]
    (h : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) : CharZero R := by
  rw [CharZero.charZero_iff_forall_prime_ne_zero]
  intro p hp
  exact (h p hp.ne_zero).ne_zero

/-- Every positive natural number is a unit in a rational algebra. -/
theorem isUnit_natCast_of_algebraRat
    {R : Type u} [CommRing R] [Algebra ℚ R]
    (n : ℕ) (hn : n ≠ 0) : IsUnit (n : R) := by
  rw [← map_natCast (algebraMap ℚ R)]
  exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)).map _

/-- In a rational algebra, ramification index one at a prime of an integral finite-type
algebra implies unramifiedness there.

Mathlib's converse to `Ideal.ramificationIdx_eq_one` asks for separability of the residue
field extension.  The residue field downstairs has characteristic zero because it is a
`ℚ`-algebra, hence is perfect, so that separability is automatic. -/
theorem isUnramifiedAt_of_ramificationIdx_eq_one_of_algebraRat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R] [Algebra.IsIntegral R S] [Algebra.EssFiniteType R S]
    (q : Ideal S) [q.IsPrime]
    (h : q.ramificationIdx R = 1) : Algebra.IsUnramifiedAt R q := by
  letI : Algebra ℚ (q.under R).ResidueField :=
    ((algebraMap R (q.under R).ResidueField).comp (algebraMap ℚ R)).toAlgebra
  haveI : CharZero (q.under R).ResidueField :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℚ _)
  letI : PerfectField (q.under R).ResidueField := PerfectField.ofCharZero
  rw [← Ideal.ramificationIdx_eq_one_iff]
  exact h

/-- A dominant integral extension of domains in characteristic zero is formally étale at
every height-zero prime.

At a height-zero prime of the cover, the localization is its fraction field.  The map
factors through the fraction field of the base; localization is formally étale, and the
resulting algebraic field extension is separable because the base fraction field has
characteristic zero. -/
theorem isEtaleAt_height_zero_of_charZero_of_integral
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S] [FaithfulSMul R S]
    [Algebra.IsIntegral R S] [CharZero R]
    (w : PrimeSpectrum S) (hw : w.asIdeal.height = 0) :
    Algebra.IsEtaleAt R w.asIdeal := by
  have hwbot : w.asIdeal = ⊥ :=
    Ideal.height_eq_zero_iff_eq_bot.mp hw
  change Algebra.FormallyEtale R (Localization.AtPrime w.asIdeal)
  let K := Localization.AtPrime w.asIdeal
  letI : IsFractionRing S K := by
    have hsub : w.asIdeal.primeCompl = nonZeroDivisors S := by
      ext x
      rw [Ideal.mem_primeCompl_iff, mem_nonZeroDivisors_iff_ne_zero, hwbot]
      simp
    change IsLocalization (nonZeroDivisors S) K
    rw [← hsub]
    infer_instance
  letI : Field K := IsFractionRing.toField S
  letI : FaithfulSMul R K := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq R S K]
    exact (FaithfulSMul.algebraMap_injective S K).comp
      (FaithfulSMul.algebraMap_injective R S)
  letI : Algebra (FractionRing R) K := FractionRing.liftAlgebra R K
  letI : IsScalarTower R (FractionRing R) K :=
    FractionRing.isScalarTower_liftAlgebra R K
  letI : Algebra.IsAlgebraic R S := Algebra.IsIntegral.isAlgebraic
  letI : Algebra.IsAlgebraic (FractionRing R) K :=
    isAlgebraic_of_isFractionRing R S (FractionRing R) K
  letI : CharZero (FractionRing R) := charZero_of_injective_algebraMap
    (IsFractionRing.injective R (FractionRing R))
  let _ : Algebra.FormallyEtale R (FractionRing R) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  let _ : Algebra.FormallyEtale (FractionRing R) K :=
    Algebra.FormallyEtale.of_isSeparable (FractionRing R) K
  exact Algebra.FormallyEtale.comp R (FractionRing R) K

/-- Unramifiedness at a source prime survives simultaneous localization of the base and
cover.

The local ring of the localized cover at `w` is canonically the local ring of the
original cover at the contraction of `w`.  Transport formal unramifiedness across this
equivalence, then restrict scalars from `R` to `R_q`. -/
theorem isUnramifiedAt_localization_algebraMapSubmonoid
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal R) [q.IsPrime]
    (w : PrimeSpectrum
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))
    (hglobal : Algebra.IsUnramifiedAt R
      (w.asIdeal.comap
        (algebraMap S
          (Localization (Algebra.algebraMapSubmonoid S q.primeCompl))))) :
    Algebra.IsUnramifiedAt (Localization.AtPrime q) w.asIdeal := by
  let Sq := Localization (Algebra.algebraMapSubmonoid S q.primeCompl)
  let W : Ideal S := w.asIdeal.comap (algebraMap S Sq)
  letI : W.IsPrime := Ideal.comap_isPrime (algebraMap S Sq) w.asIdeal
  let T := Localization.AtPrime w.asIdeal
  haveI : IsLocalization.AtPrime T W :=
    IsLocalization.isLocalization_atPrime_localization_atPrime
      (Algebra.algebraMapSubmonoid S q.primeCompl) w.asIdeal
  let e : Localization.AtPrime W ≃ₐ[S] T :=
    IsLocalization.algEquiv W.primeCompl _ _
  let _ : Algebra.FormallyUnramified R (Localization.AtPrime W) := hglobal
  have hRT : Algebra.FormallyUnramified R T :=
    Algebra.FormallyUnramified.of_equiv (e.restrictScalars R)
  let _ : Algebra.FormallyUnramified R T := hRT
  exact Algebra.FormallyUnramified.of_restrictScalars R
    (Localization.AtPrime q) T

/-- The data of the bounding argument in the local ring at the generic point of a divisor
of `B`.

Compared with `BoundingChart`, global regularity of `R` and `R/(a)` is replaced by the
geometric local facts actually available at that point: `R` is a normal two-dimensional
regular local domain, and `R/(a)` is a one-dimensional regular local ring. -/
structure LocalBoundingChart (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (a : R) (p : Ideal S) : Prop where
  /-- The ambient stalk is a regular local ring. -/
  regular_base : IsRegularLocalRing R
  /-- The ambient stalk is a domain. -/
  domain_base : IsDomain R
  /-- Normality of the ambient variety at the chosen point. -/
  normal_base : IsIntegrallyClosed R
  /-- The chosen point has codimension two in the ambient variety. -/
  dim_base : ringKrullDim R = 2
  /-- The divisor stalk is regular local. -/
  regular_divisor : IsRegularLocalRing (R ⧸ Ideal.span {a})
  /-- The chosen point has codimension one on the divisor. -/
  dim_divisor : ringKrullDim (R ⧸ Ideal.span {a}) = 1
  /-- The local cover is finite. -/
  finite : Module.Finite R S
  /-- The finite local cover is dominant, equivalently its algebra map is injective. -/
  faithful : FaithfulSMul R S
  /-- The local cover is integral. -/
  domain_cover : IsDomain S
  /-- The local cover is normal. -/
  normal_cover : IsIntegrallyClosed S
  /-- Characteristic zero, in the form used for tameness. -/
  tame : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)
  /-- Unramifiedness at codimension-one points away from the divisor. -/
  unramified_codim_one : ∀ w : PrimeSpectrum S, w.asIdeal.height = 1 →
    algebraMap R S a ∉ w.asIdeal → Algebra.IsUnramifiedAt R w.asIdeal
  /-- The selected component is minimal over the pullback of `(a)`. -/
  minimal : p ∈ (Ideal.span {algebraMap R S a}).minimalPrimes
  /-- Zariski–Nagata purity. -/
  purity : Stacks.ZariskiNagataPurity R S
  /-- Abhyankar's lemma. -/
  abhyankar : Stacks.AbhyankarLemma R S a

namespace LocalBoundingChart

/-- Construct the local bounding chart from the canonical localization of a finite
dominant normal cover.

The local base is `R_q`; the local cover is obtained by inverting in `S` the image of
`R \ q`.  Mathlib's localization algebra supplies module-finiteness, and the two lemmas
above supply injectivity and normality.  The cover is a domain by localization.  Finally,
the selected source divisor is required only to be a height-one prime containing the
pulled-back equation: its minimality over that equation is derived.

Thus none of the finite-cover package (`finite`, `faithful`, `domain_cover`,
`normal_cover`) or the minimal-prime assertion is a caller-supplied local-chart field on
this route. -/
theorem ofFiniteNormalLocalization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [FaithfulSMul R S]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    (q : Ideal R) [q.IsPrime]
    (a : Localization.AtPrime q)
    (p : Ideal (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))
    [p.IsPrime]
    (regular_base : IsRegularLocalRing (Localization.AtPrime q))
    (dim_base : ringKrullDim (Localization.AtPrime q) = 2)
    (regular_divisor : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}))
    (dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1)
    (tame : ∀ n : ℕ, n ≠ 0 → IsUnit (n : Localization.AtPrime q))
    (unramified_codim_one : ∀ w : PrimeSpectrum
        (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)),
      w.asIdeal.height = 1 →
        algebraMap (Localization.AtPrime q)
          (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a ∉ w.asIdeal →
        Algebra.IsUnramifiedAt (Localization.AtPrime q) w.asIdeal)
    (height_cover_divisor : p.height = 1)
    (equation_mem : algebraMap (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a ∈ p)
    (purity : Stacks.ZariskiNagataPurity (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a) :
    LocalBoundingChart (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a p := by
  refine
    { regular_base := regular_base
      domain_base := inferInstance
      normal_base := ?_
      dim_base := dim_base
      regular_divisor := regular_divisor
      dim_divisor := dim_divisor
      finite := inferInstance
      faithful := faithfulSMul_localization_algebraMapSubmonoid q
      domain_cover := inferInstance
      normal_cover := isIntegrallyClosed_localization_algebraMapSubmonoid q
      tame := tame
      unramified_codim_one := unramified_codim_one
      minimal := ?_
      purity := purity
      abhyankar := abhyankar }
  · exact isIntegrallyClosed_of_isLocalization _ _
      q.primeCompl_le_nonZeroDivisors
  · apply mem_minimalPrimes_span_singleton_of_height_eq_one _
      equation_mem height_cover_divisor
    intro hzero
    apply mem_nonZeroDivisors_iff_ne_zero.mp
      (mem_nonZeroDivisors_of_ringKrullDim_eq_two_of_quotient_eq_one
        dim_base dim_divisor)
    have hinj : Function.Injective
        (algebraMap (Localization.AtPrime q)
          (Localization (Algebra.algebraMapSubmonoid S q.primeCompl))) :=
      localizationAlgebra_injective _ _
        (FaithfulSMul.algebraMap_injective R S)
    apply hinj
    simpa using hzero

/-- Pointed version of the finite-normal divisor constructor.

The branch hypothesis is only required for ramified source divisors whose contractions
pass through the selected point `q`.  This is precisely the local support information
used in the proof. -/
theorem ofFiniteNormalLocalizationOfDivisorsAt
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R]
    [Module.Finite R S] [FaithfulSMul R S]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    (q D : Ideal R) (P : Ideal S) [q.IsPrime] [D.IsPrime] [P.IsPrime]
    (hunder : P.under R ≤ q)
    (hDP : D.map (algebraMap R S) ≤ P)
    (hPheight : P.height = 1)
    (a : Localization.AtPrime q)
    (ha : D.map (algebraMap R (Localization.AtPrime q)) = Ideal.span {a})
    (regular_base : IsRegularLocalRing (Localization.AtPrime q))
    (dim_base : ringKrullDim (Localization.AtPrime q) = 2)
    (regular_divisor : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}))
    (dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1)
    (ramified_lies_over : ∀ W : HeightOnePrime S,
      W.1.asIdeal.under R ≤ q → 1 < heightOneRamificationIdx (R := R) W →
        D.map (algebraMap R S) ≤ W.1.asIdeal)
    (purity : Stacks.ZariskiNagataPurity (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a) :
    LocalBoundingChart (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a
      (P.map (algebraMap S
        (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))) := by
  let Sq := Localization (Algebra.algebraMapSubmonoid S q.primeCompl)
  have hdisjoint : Disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (P : Set S) := by
    rw [Set.disjoint_left]
    rintro x ⟨r, hr, rfl⟩ hxP
    exact hr (hunder hxP)
  letI : (P.map (algebraMap S Sq)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl) Sq P inferInstance hdisjoint
  have hheight : (P.map (algebraMap S Sq)).height = 1 :=
    (IsLocalization.height_map_of_disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl) P hdisjoint).trans hPheight
  have haD : a ∈ D.map (algebraMap R (Localization.AtPrime q)) := by
    rw [ha]
    exact Ideal.mem_span_singleton_self a
  have heq :
      (D.map (algebraMap R (Localization.AtPrime q))).map
          (algebraMap (Localization.AtPrime q) Sq) =
        (D.map (algebraMap R S)).map (algebraMap S Sq) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    exact IsScalarTower.algebraMap_eq R (Localization.AtPrime q) Sq ▸
      (IsScalarTower.algebraMap_eq R S Sq).symm
  have hequation : algebraMap (Localization.AtPrime q) Sq a ∈
      P.map (algebraMap S Sq) := by
    have hleft : algebraMap (Localization.AtPrime q) Sq a ∈
        (D.map (algebraMap R (Localization.AtPrime q))).map
          (algebraMap (Localization.AtPrime q) Sq) :=
      Ideal.mem_map_of_mem _ haD
    rw [heq] at hleft
    exact Ideal.map_mono hDP hleft
  have hunramified : ∀ w : PrimeSpectrum Sq, w.asIdeal.height = 1 →
      algebraMap (Localization.AtPrime q) Sq a ∉ w.asIdeal →
      Algebra.IsUnramifiedAt (Localization.AtPrime q) w.asIdeal := by
    intro w hw ha_not
    let W : Ideal S := w.asIdeal.comap (algebraMap S Sq)
    letI : W.IsPrime := Ideal.comap_isPrime (algebraMap S Sq) w.asIdeal
    have hWheight : W.height = 1 :=
      (IsLocalization.height_under
        (Algebra.algebraMapSubmonoid S q.primeCompl) w.asIdeal).trans hw
    have hnotle : ¬D.map (algebraMap R S) ≤ W := by
      intro hle
      have hleft : algebraMap (Localization.AtPrime q) Sq a ∈
          (D.map (algebraMap R S)).map (algebraMap S Sq) := by
        rw [← heq]
        exact Ideal.mem_map_of_mem _ haD
      have hmap : algebraMap (Localization.AtPrime q) Sq a ∈
          W.map (algebraMap S Sq) := Ideal.map_mono hle hleft
      exact ha_not (Ideal.map_comap_le hmap)
    have hWq : W.under R ≤ q := by
      have hdisjoint : Disjoint
          (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (W : Set S) :=
        (IsLocalization.disjoint_under_iff
          (Algebra.algebraMapSubmonoid S q.primeCompl) Sq w.asIdeal).2
          (show w.asIdeal.IsPrime from inferInstance).ne_top
      intro r hr
      by_contra hrq
      exact (Set.disjoint_left.mp hdisjoint)
        (show algebraMap R S r ∈
          Algebra.algebraMapSubmonoid S q.primeCompl from ⟨r, hrq, rfl⟩) hr
    let Wh : HeightOnePrime S := ⟨⟨W, inferInstance⟩, hWheight⟩
    have hram_le : heightOneRamificationIdx (R := R) Wh ≤ 1 := by
      apply Nat.le_of_not_gt
      intro hram
      exact hnotle (ramified_lies_over Wh hWq hram)
    have hram_eq : heightOneRamificationIdx (R := R) Wh = 1 :=
      Nat.le_antisymm hram_le (heightOneRamificationIdx_pos (R := R) Wh)
    have hglobal : Algebra.IsUnramifiedAt R W :=
      isUnramifiedAt_of_ramificationIdx_eq_one_of_algebraRat W hram_eq
    exact isUnramifiedAt_localization_algebraMapSubmonoid q w
      hglobal
  exact ofFiniteNormalLocalization q a
    (P.map (algebraMap S Sq)) regular_base dim_base regular_divisor dim_divisor
    isUnit_natCast_of_algebraRat hunramified hheight hequation purity abhyankar

/-- Construct the local chart from a global singleton support statement.

This compatibility wrapper preserves the earlier interface; the proof passes only the
pointed consequence actually used by `ofFiniteNormalLocalizationOfDivisorsAt`. -/
theorem ofFiniteNormalLocalizationOfDivisors
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R]
    [Module.Finite R S] [FaithfulSMul R S]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    (q D : Ideal R) (P : Ideal S) [q.IsPrime] [D.IsPrime] [P.IsPrime]
    (hunder : P.under R ≤ q)
    (hDP : D.map (algebraMap R S) ≤ P)
    (hPheight : P.height = 1)
    (a : Localization.AtPrime q)
    (ha : D.map (algebraMap R (Localization.AtPrime q)) = Ideal.span {a})
    (regular_base : IsRegularLocalRing (Localization.AtPrime q))
    (dim_base : ringKrullDim (Localization.AtPrime q) = 2)
    (regular_divisor : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}))
    (dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1)
    (branch_subset_divisor : heightOneBranchIdeal (R := R) (S := S) ⊆ {D})
    (purity : Stacks.ZariskiNagataPurity (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a) :
    LocalBoundingChart (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a
      (P.map (algebraMap S
        (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))) := by
  apply ofFiniteNormalLocalizationOfDivisorsAt q D P hunder hDP hPheight a ha
    regular_base dim_base regular_divisor dim_divisor _ purity abhyankar
  intro W _ hW
  exact ramified_heightOne_lies_over_of_branchIdeal_subset_singleton
    D branch_subset_divisor W hW

/-- Bundled-divisor constructor from branch avoidance at the selected point.

This is the Step 0 form: `q` may meet the chosen branch divisor `D`, but it lies on no
other member of the honest height-one branch set.  No global singleton-support statement
is required. -/
theorem ofFiniteNormalLocalizationOfHeightOneDivisorsAt
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R]
    [Module.Finite R S] [FaithfulSMul R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    (q : Ideal R) (D : HeightOnePrime R) (P : HeightOnePrime S) [q.IsPrime]
    (hunder : P.1.asIdeal.under R ≤ q)
    (hDP : D.1.asIdeal.map (algebraMap R S) ≤ P.1.asIdeal)
    (a : Localization.AtPrime q)
    (ha : D.1.asIdeal.map (algebraMap R (Localization.AtPrime q)) =
      Ideal.span {a})
    (regular_base : IsRegularLocalRing (Localization.AtPrime q))
    (dim_base : ringKrullDim (Localization.AtPrime q) = 2)
    (regular_divisor : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}))
    (dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1)
    (havoid : ∀ E ∈ heightOneBranch (R := R) (S := S), E ≠ D →
      ¬ E.1.asIdeal ≤ q)
    (purity : Stacks.ZariskiNagataPurity (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a) :
    LocalBoundingChart (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a
      (P.1.asIdeal.map (algebraMap S
        (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))) := by
  apply ofFiniteNormalLocalizationOfDivisorsAt q D.1.asIdeal P.1.asIdeal
    hunder hDP P.2 a ha regular_base dim_base regular_divisor dim_divisor _
      purity abhyankar
  intro W hWq hW
  exact ramified_heightOne_lies_over_of_avoids_other_branch_at
    q D havoid W hW hWq

/-- Bundled-divisor form of `ofFiniteNormalLocalizationOfDivisors`.

Here the target and source components are actual height-one primes, and the branch input
is the honest affine height-one branch set rather than the auxiliary set of unbundled
contracted ideals.  The conversion to the ring-level constructor is a theorem. -/
theorem ofFiniteNormalLocalizationOfHeightOneDivisors
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R]
    [Module.Finite R S] [FaithfulSMul R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    (q : Ideal R) (D : HeightOnePrime R) (P : HeightOnePrime S) [q.IsPrime]
    (hunder : P.1.asIdeal.under R ≤ q)
    (hDP : D.1.asIdeal.map (algebraMap R S) ≤ P.1.asIdeal)
    (a : Localization.AtPrime q)
    (ha : D.1.asIdeal.map (algebraMap R (Localization.AtPrime q)) =
      Ideal.span {a})
    (regular_base : IsRegularLocalRing (Localization.AtPrime q))
    (dim_base : ringKrullDim (Localization.AtPrime q) = 2)
    (regular_divisor : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}))
    (dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1)
    (branch_subset_divisor : heightOneBranch (R := R) (S := S) ⊆ {D})
    (purity : Stacks.ZariskiNagataPurity (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a) :
    LocalBoundingChart (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a
      (P.1.asIdeal.map (algebraMap S
        (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))) := by
  exact ofFiniteNormalLocalizationOfDivisors q D.1.asIdeal P.1.asIdeal
    hunder hDP P.2 a ha regular_base dim_base regular_divisor dim_divisor
    (heightOneBranchIdeal_subset_singleton_of_heightOneBranch_subset_singleton
      D branch_subset_divisor)
    purity abhyankar

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {a : R} {p : Ideal S} (h : LocalBoundingChart R S a p)

include h

/-- A local bounding chart supplies the `BoundingChart` used by the checked Steps 1–4.

The regular-local hypotheses are promoted to regular rings in dimensions two and one.
Noetherianity of `S` follows from finiteness over the regular local base, and equality of
heights follows from finite injectivity and normality of `R`. The equation's
nonzerodivisor property follows from the dimension drop, and the normalization condition
follows from finiteness and normality of `S`; none is separately assumed. -/
theorem toBoundingChart : BoundingChart R S a p := by
  letI : IsRegularLocalRing R := h.regular_base
  letI : IsDomain R := h.domain_base
  letI : IsIntegrallyClosed R := h.normal_base
  letI : IsRegularLocalRing (R ⧸ Ideal.span {a}) := h.regular_divisor
  letI : Module.Finite R S := h.finite
  letI : FaithfulSMul R S := h.faithful
  letI : IsDomain S := h.domain_cover
  letI : IsIntegrallyClosed S := h.normal_cover
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : CharZero R := charZero_of_isUnit_natCast h.tame
  letI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have ha : a ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_ringKrullDim_eq_two_of_quotient_eq_one
      h.dim_base h.dim_divisor
  exact
    { noetherian_base := inferInstance
      noetherian_cover := inferInstance
      finite := inferInstance
      domain := inferInstance
      nonZeroDivisor := ha
      regular :=
        isRegularRing_of_isRegularLocalRing_of_isIntegrallyClosed_dim_two R h.dim_base
      regular_divisor :=
        isRegularRing_of_isRegularLocalRing_of_ringKrullDim_eq_one
          (R ⧸ Ideal.span {a}) h.dim_divisor
      normal := fun w =>
        isIntegrallyClosed_of_isLocalization (Localization.AtPrime w.asIdeal)
          w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors
      tame := h.tame
      dim_eq := fun w ↦
        (height_under_eq_of_finite_of_normal (R := R) w.asIdeal).symm
      generic_etale := isEtaleAt_height_zero_of_charZero_of_integral
      unramified_codim_one := h.unramified_codim_one
      normalization :=
        isIntegralClosure_localizationAway_of_finite_of_integrallyClosed a
          (map_mem_nonZeroDivisors _
            (FaithfulSMul.algebraMap_injective R S) ha)
      prime := h.minimal.1.1
      minimal := h.minimal
      purity := h.purity
      abhyankar := h.abhyankar }

/-- The quotient-ring map cut out by the chosen divisor and its selected inverse-image
component.  Naming this map makes the later localization and stalk interfaces independent
of a locally synthesized `Algebra` instance. -/
noncomputable def restrictionRingHom :
    (R ⧸ Ideal.span {a}) →+* (S ⧸ p) := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  exact algebraMap _ _

/-- The point of the quotient base below a point of the selected inverse-image
component. -/
noncomputable def restrictionPoint (xi : PrimeSpectrum (S ⧸ p)) :
    PrimeSpectrum (R ⧸ Ideal.span {a}) := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  exact ⟨xi.asIdeal.under (R ⧸ Ideal.span {a}), inferInstance⟩

/-- The bounding conclusion on the local chart, derived from purity and Abhyankar. -/
theorem isEtaleAt_restriction (xi : PrimeSpectrum (S ⧸ p)) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    Algebra.IsEtaleAt (R ⧸ Ideal.span {a}) xi.asIdeal := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  exact h.toBoundingChart.isEtaleAt_restriction Stacks.existsPrimeOverBoth xi

/-- The local-ring map at a point of the restricted chart. -/
noncomputable def restrictionLocalRingHom (xi : PrimeSpectrum (S ⧸ p)) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    Localization.AtPrime (h.restrictionPoint xi).asIdeal →+*
      Localization.AtPrime xi.asIdeal := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  exact Localization.localRingHom
    (h.restrictionPoint xi).asIdeal xi.asIdeal
    (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)) (by
      simp only [restrictionPoint, Ideal.under_def])

/-- The induced map of local rings at a point of the restricted chart is formally étale.

`isEtaleAt_restriction` uses Mathlib's affine convention, in which the base ring is not
localized.  This theorem localizes the base at the contracted prime.  It is the form that
can be identified directly with the stalk map of the restricted scheme morphism. -/
theorem formallyEtale_localRingHom (xi : PrimeSpectrum (S ⧸ p)) :
    (h.restrictionLocalRingHom xi).FormallyEtale := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  let q := xi.asIdeal
  let q0 := (h.restrictionPoint xi).asIdeal
  letI : q.LiesOver q0 := ⟨by
    simp only [q0, restrictionPoint, Ideal.under_def]
    rfl⟩
  letI : Algebra (Localization.AtPrime q0) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver q0 q
  haveI : IsScalarTower (R ⧸ Ideal.span {a})
      (Localization.AtPrime q0) (Localization.AtPrime q) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    exact (Localization.localRingHom_to_map q0 q
      (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)) rfl x).symm
  have hglobal : Algebra.FormallyEtale (R ⧸ Ideal.span {a})
      (Localization.AtPrime q) := h.isEtaleAt_restriction xi
  let _ : Algebra.FormallyEtale (R ⧸ Ideal.span {a})
      (Localization.AtPrime q) := hglobal
  have hlocal : Algebra.FormallyEtale (Localization.AtPrime q0)
      (Localization.AtPrime q) :=
    Algebra.FormallyEtale.localization_base q0.primeCompl
  rw [RingHom.FormallyEtale]
  exact hlocal

/-- The concrete codimension-one non-étale locus of the local restriction is empty. -/
theorem affineNonEtaleLocus_restriction_eq_empty :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    affineNonEtaleLocus (R ⧸ Ideal.span {a}) (S ⧸ p) = ∅ := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  exact hq (h.isEtaleAt_restriction q.1)

end LocalBoundingChart

end Pcf
