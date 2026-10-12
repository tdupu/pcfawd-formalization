/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.PrincipalQuotientRegular
import Pcf.Bounding.RegularLocalDomain
import Pcf.Bounding.StandardPiece
import Pcf.Stacks.Abhyankar.StandardCover
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# The integral-closure calculation for the standard root cover

Stacks Project Tag `0EYH` uses, without spelling out the algebra, that the integral closure
of `R` in

`R[1/a][z] / (z ^ e - u * a)`

is `R[z] / (z ^ e - u * a)` when `a` is a nonzerodivisor and `R/(a)` is regular.  This
file proves that omitted calculation.

The key elementary lemma is slightly more general: if `r` is a nonzerodivisor and `(r)` is
radical, then `A` is integrally closed in `A[1/r]`.  Applying it to the distinguished root
`z` works because `C/(z) ≅ R/(a)`, while `C[1/z] = C[1/a]` follows from
`z ^ e = u * a`.

The final declaration has the Noetherian and regular-quotient hypotheses appearing in the
affine standard model in `0EYH`.  The stronger preceding declaration records that regularity
is used only through reducedness of `R/(a)`.  These are the integral-closure calculation,
not the full geometric statement of Tag `0EYH`.
-/

universe u

open Polynomial

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace Pcf.Stacks

variable {R : Type u} [CommRing R]

/-- If `r` is a nonzerodivisor and `(r)` is radical, then `A` is integrally closed in
every localization of `A` away from `r`.

For an integral fraction `b / r^(n+1)`, scale a monic equation by `r^(n+1)` and reduce
modulo `r`.  Radicality gives `r ∣ b`, so one denominator can be cancelled; induction on
`n` finishes. -/
theorem isIntegrallyClosedIn_away_of_span_isRadical
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] {r : A}
    [IsLocalization.Away r S]
    (hr : r ∈ nonZeroDivisors A) (hrad : (Ideal.span ({r} : Set A)).IsRadical) :
    IsIntegrallyClosedIn A S := by
  rw [isIntegrallyClosedIn_iff]
  have hpowers : Submonoid.powers r ≤ nonZeroDivisors A := by
    rw [Submonoid.powers_le]
    exact hr
  refine ⟨IsLocalization.injective S hpowers, ?_⟩
  intro x hx
  by_cases hunit : IsUnit r
  · let e : A ≃ₐ[A] S := IsLocalization.atUnit A S r hunit
    obtain ⟨y, hy⟩ := e.surjective x
    exact ⟨y, (e.commutes y).trans hy⟩
  letI : Nontrivial (A ⧸ Ideal.span ({r} : Set A)) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top hunit)
  obtain ⟨b, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers r) x
  induction n generalizing b with
  | zero =>
      refine ⟨b, ?_⟩
      rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
      simp
  | succ n ih =>
      let den : A := r ^ (n + 1)
      let sden : Submonoid.powers r := ⟨den, n + 1, rfl⟩
      have hx0 := hx
      obtain ⟨p, hpmonic, hproot⟩ := hx
      have hscaledLoc : Polynomial.eval₂ (algebraMap A S)
          (algebraMap A S den * IsLocalization.mk' S b sden)
          (p.scaleRoots den) = 0 :=
        Polynomial.scaleRoots_eval₂_eq_zero (algebraMap A S) hproot
      have hdenmul : algebraMap A S den * IsLocalization.mk' S b sden =
            algebraMap A S b :=
        IsLocalization.mk'_spec' (S := S) b sden
      rw [hdenmul] at hscaledLoc
      have hscaled : Polynomial.eval b (p.scaleRoots den) = 0 := by
        apply IsLocalization.injective S hpowers
        rw [map_zero, ← Polynomial.eval₂_at_apply]
        exact hscaledLoc
      let f : A →+* A ⧸ Ideal.span ({r} : Set A) :=
        Ideal.Quotient.mk (Ideal.span ({r} : Set A))
      have hfden : f den = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        simpa [den, pow_succ] using
          Ideal.mul_mem_left (Ideal.span ({r} : Set A)) (r ^ n)
            (Ideal.mem_span_singleton_self r)
      have hmapPoly : (p.scaleRoots den).map f = X ^ p.natDegree := by
        rw [Polynomial.map_scaleRoots p den f]
        · rw [hfden, Polynomial.scaleRoots_zero, (hpmonic.map f).leadingCoeff,
            one_smul, hpmonic.natDegree_map f]
        · rw [hpmonic.leadingCoeff, map_one]
          exact one_ne_zero
      have hbpow : b ^ p.natDegree ∈ Ideal.span ({r} : Set A) := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        rw [map_pow]
        calc
          f b ^ p.natDegree = Polynomial.eval (f b) (X ^ p.natDegree) := by simp
          _ = Polynomial.eval (f b) ((p.scaleRoots den).map f) := by rw [hmapPoly]
          _ = f (Polynomial.eval b (p.scaleRoots den)) := by
            rw [Polynomial.eval_map]
            simpa [Polynomial.eval₂_at_apply] using
              (Polynomial.hom_eval₂ (p.scaleRoots den) (RingHom.id A) f b).symm
          _ = 0 := by rw [hscaled, map_zero]
      have hbmem : b ∈ Ideal.span ({r} : Set A) :=
        hrad (Ideal.mem_radical_iff.mpr ⟨p.natDegree, hbpow⟩)
      obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton.mp hbmem
      let ssmall : Submonoid.powers r := ⟨r ^ n, n, rfl⟩
      have heq : IsLocalization.mk' S b' ssmall = IsLocalization.mk' S b sden := by
        apply IsLocalization.mk'_eq_of_eq
        dsimp only [ssmall, sden, den]
        rw [hb', pow_succ]
        ring
      have hx' : IsIntegral A (IsLocalization.mk' S b' ssmall) := by
        rw [heq]
        exact hx0
      obtain ⟨y, hy⟩ := ih b' hx'
      exact ⟨y, hy.trans heq⟩

/-- A regular ring is reduced.  This is the reducedness consequence of Stacks Tag `0567`
needed by the standard-cover normalization calculation: localize at each maximal ideal,
use that a regular local ring is a domain (Tag `00NP`), then descend reducedness. -/
theorem isReduced_of_isRegularRing
    {A : Type u} [CommRing A] [IsRegularRing A] : IsReduced A := by
  apply isReduced_ofLocalizationMaximal A
  intro q hq
  letI : q.IsPrime := hq.isPrime
  letI : IsDomain (Localization.AtPrime q) :=
    Pcf.Stacks.isDomain_of_isRegularLocalRing (Localization.AtPrime q)
  infer_instance

/-- Inverting `a` in the standard root algebra also inverts the distinguished root `z`.
Thus `C[1/a]` is a localization of `C` away from `z`. -/
theorem standardCover_isLocalizationAway_root
    (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e) :
    IsLocalization.Away
      (AdjoinRoot.root (Pcf.LocalModel.localPoly u a e))
      (Localization.Away
        (algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) a)) := by
  let C := AdjoinRoot (Pcf.LocalModel.localPoly u a e)
  let z : C := AdjoinRoot.root (Pcf.LocalModel.localPoly u a e)
  let ac : C := algebraMap R C a
  let T := Localization.Away ac
  have hassoc : Associated (z ^ e) ac := by
    rw [show z ^ e = algebraMap R C ((u : R) * a) from
      Pcf.LocalModel.root_pow_eq u a e, map_mul]
    exact associated_unit_mul_left ac (algebraMap R C (u : R))
      ((Units.isUnit u).map (algebraMap R C))
  letI : IsLocalization.Away (z ^ e) T :=
    IsLocalization.Away.of_associated hassoc.symm
  have hle : Submonoid.powers (z ^ e) ≤ Submonoid.powers z := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    refine ⟨e * n, ?_⟩
    change z ^ (e * n) = (z ^ e) ^ n
    exact pow_mul z e n
  have hdvd : ∀ x ∈ Submonoid.powers z,
      ∃ m ∈ Submonoid.powers (z ^ e), x ∣ m := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    refine ⟨(z ^ e) ^ n, ⟨n, rfl⟩, ?_⟩
    change z ^ n ∣ (z ^ e) ^ n
    simpa only [pow_mul] using pow_dvd_pow z (Nat.le_mul_of_pos_left n he)
  exact (IsLocalization.iff_of_le_of_exists_dvd
    (Submonoid.powers (z ^ e)) (Submonoid.powers z) hle hdvd).mp inferInstance

/-- The standard root algebra is integrally closed in its generic-away algebra, assuming
only that `a` is a nonzerodivisor and `R/(a)` is reduced. -/
theorem standardCover_isIntegrallyClosedIn_localizationAway
    (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e)
    (ha : a ∈ nonZeroDivisors R)
    [IsReduced (R ⧸ Ideal.span ({a} : Set R))] :
    IsIntegrallyClosedIn
      (AdjoinRoot (Pcf.LocalModel.localPoly u a e))
      (Localization.Away
        (algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) a)) := by
  let C := AdjoinRoot (Pcf.LocalModel.localPoly u a e)
  let z : C := AdjoinRoot.root (Pcf.LocalModel.localPoly u a e)
  let T := Localization.Away (algebraMap R C a)
  letI : IsLocalization.Away z T :=
    standardCover_isLocalizationAway_root u a he
  exact isIntegrallyClosedIn_away_of_span_isRadical
    (Pcf.LocalModel.root_mem_nonZeroDivisors u a he ha)
    (Pcf.LocalModel.span_root_isRadical u a he)

/-- The standard root algebra is the integral closure of `R` in its generic-away algebra,
assuming only that `a` is a nonzerodivisor and `R/(a)` is reduced. -/
theorem standardCover_isIntegralClosure_localizationAway
    (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e)
    (ha : a ∈ nonZeroDivisors R)
    [IsReduced (R ⧸ Ideal.span ({a} : Set R))] :
    IsIntegralClosure
      (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) R
      (Localization.Away
        (algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) a)) := by
  let C := AdjoinRoot (Pcf.LocalModel.localPoly u a e)
  let T := Localization.Away (algebraMap R C a)
  let _ : IsIntegrallyClosedIn C T :=
    standardCover_isIntegrallyClosedIn_localizationAway u a he ha
  let _ : Algebra.IsIntegral R C :=
    AdjoinRoot.isIntegral_of_monic (Pcf.LocalModel.localPoly_monic u a he)
  exact IsIntegralClosure.of_isIntegrallyClosedIn

/-- The exact affine integral-closure calculation omitted in the proof of Stacks Tag
`0EYH`: for Noetherian `R`, a nonzerodivisor `a`, regular `R/(a)`, positive `e`, and unit
coefficient `u`, the standard root algebra is the integral closure in `C[1/a]`. -/
theorem standardCover_isIntegralClosure_localizationAway_of_regular
    [IsNoetherianRing R]
    (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))] :
    IsIntegralClosure
      (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) R
      (Localization.Away
        (algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) a)) := by
  letI : IsReduced (R ⧸ Ideal.span ({a} : Set R)) :=
    isReduced_of_isRegularRing
  exact standardCover_isIntegralClosure_localizationAway u a he ha

/-- A finite product of integral closures is the integral closure in the corresponding
finite product of ambient rings.

For the nontrivial direction, choose a monic equation for every component of a tuple and
take the product of those finitely many equations.  This formulation also covers an empty
index type: then both products are the zero ring, and the pointwise proof is vacuous. -/
theorem isIntegralClosure_pi_of_fintype
    {ι : Type} [Finite ι]
    {A B : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)]
    [∀ i, Algebra (A i) (B i)]
    [∀ i, IsScalarTower R (A i) (B i)]
    [∀ i, IsIntegralClosure (A i) R (B i)] :
    IsIntegralClosure (∀ i, A i) R (∀ i, B i) := by
  classical
  letI := Fintype.ofFinite ι
  constructor
  · intro x y hxy
    funext i
    apply IsIntegralClosure.algebraMap_injective (A i) R (B i)
    exact congrFun hxy i
  · intro x
    constructor
    · intro hx
      have hxi : ∀ i, IsIntegral R (x i) := fun i =>
        hx.map (Pi.evalAlgHom R B i)
      choose y hy using fun i =>
        (IsIntegralClosure.isIntegral_iff (A := A i)).mp (hxi i)
      refine ⟨fun i => y i, funext fun i => ?_⟩
      exact hy i
    · rintro ⟨y, rfl⟩
      have hi : ∀ i, IsIntegral R (algebraMap (A i) (B i) (y i)) := fun i =>
        IsIntegral.algebraMap (IsIntegralClosure.isIntegral R (B i) (y i))
      choose p hpmon hproot using hi
      refine ⟨∏ i, p i, monic_prod_of_monic Finset.univ p (fun i _ => hpmon i), ?_⟩
      ext i
      change (Pi.evalRingHom B i) (Polynomial.eval₂
        (algebraMap R (∀ i, B i))
        (algebraMap (∀ i, A i) (∀ i, B i) y) (∏ i, p i)) = 0
      rw [Polynomial.hom_eval₂]
      change Polynomial.eval₂ (algebraMap R (B i))
        (algebraMap (A i) (B i) (y i)) (∏ i, p i) = 0
      rw [Polynomial.eval₂_finsetProd]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hproot i)

/-- The coordinate ring of a finite disjoint union of standard root covers is the
integral closure of `R` in the product of the generic-away coordinate rings.

This is the finite-disjoint-union version of the calculation omitted in Tag `0EYH`. -/
theorem standardCovers_isIntegralClosure_localizationsAway_of_regular
    [IsNoetherianRing R]
    {ι : Type} [Finite ι]
    (u : ι → Rˣ) (a : R) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))] :
    IsIntegralClosure
      (∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))) R
      (∀ i, Localization.Away
        (algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))) a)) := by
  letI (i : ι) : IsIntegralClosure
      (AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))) R
      (Localization.Away
        (algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))) a)) :=
    standardCover_isIntegralClosure_localizationAway_of_regular (u i) a (he i) ha
  exact isIntegralClosure_pi_of_fintype

/-- Identify an arbitrary normalization with the finite disjoint union of standard root
covers once their generic-away algebras have been identified.

This is the uniqueness step implicit in Tag `0EYH`.  The input equivalence is precisely the
generic standard-cover description supplied by Tag `0EYG`; the conclusion is not assumed.
The normalization hypothesis on `N` and the proved standard-cover integral-closure theorem
put both algebras inside the same ambient generic ring, where uniqueness of integral closure
gives the result. -/
noncomputable def normalizationEquivStandardCoversOfGenericEquiv
    {N : Type u} [CommRing N] [Algebra R N]
    [IsNoetherianRing R]
    {ι : Type} [Fintype ι]
    (u : ι → Rˣ) (a : R) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [IsIntegralClosure N R (Localization.Away (algebraMap R N a))]
    (g : Localization.Away (algebraMap R N a) ≃ₐ[R]
      (∀ i, Localization.Away
        (algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))) a))) :
    N ≃ₐ[R] (∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))) := by
  let C := ∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))
  let TN := Localization.Away (algebraMap R N a)
  let TC := ∀ i, Localization.Away
    (algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))) a)
  letI : Algebra N TC :=
    (g.toAlgHom.toRingHom.comp (algebraMap N TN)).toAlgebra
  letI : IsScalarTower R N TC := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R TC r = g (algebraMap N TN (algebraMap R N r))
    rw [← IsScalarTower.algebraMap_apply R N TN]
    exact (g.commutes r).symm
  let hN : IsIntegralClosure N R TC :=
    IsIntegralClosure.of_algEquiv N g (fun _ => rfl)
  letI : IsIntegralClosure N R TC := hN
  let hC : IsIntegralClosure C R TC :=
    standardCovers_isIntegralClosure_localizationsAway_of_regular u a e he ha
  letI : IsIntegralClosure C R TC := hC
  exact IsIntegralClosure.equiv R N TC C

/-- The arbitrary-normalization equivalence is compatible with the two embeddings into the
identified generic-away algebra.  Thus the preceding equivalence is the normalization
comparison required by `0EYH`, rather than merely an abstract ring equivalence. -/
theorem algebraMap_normalizationEquivStandardCoversOfGenericEquiv
    {N : Type u} [CommRing N] [Algebra R N]
    [IsNoetherianRing R]
    {ι : Type} [Fintype ι]
    (u : ι → Rˣ) (a : R) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [IsIntegralClosure N R (Localization.Away (algebraMap R N a))]
    (g : Localization.Away (algebraMap R N a) ≃ₐ[R]
      (∀ i, Localization.Away
        (algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))) a)))
    (x : N) :
    algebraMap (∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i)))
        (∀ i, Localization.Away
          (algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))) a))
        (normalizationEquivStandardCoversOfGenericEquiv u a e he ha g x) =
      g (algebraMap N (Localization.Away (algebraMap R N a)) x) := by
  let C := ∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))
  let TN := Localization.Away (algebraMap R N a)
  let TC := ∀ i, Localization.Away
    (algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))) a)
  letI : Algebra N TC :=
    (g.toAlgHom.toRingHom.comp (algebraMap N TN)).toAlgebra
  letI : IsScalarTower R N TC := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R TC r = g (algebraMap N TN (algebraMap R N r))
    rw [← IsScalarTower.algebraMap_apply R N TN]
    exact (g.commutes r).symm
  let hN : IsIntegralClosure N R TC :=
    IsIntegralClosure.of_algEquiv N g (fun _ => rfl)
  letI : IsIntegralClosure N R TC := hN
  let hC : IsIntegralClosure C R TC :=
    standardCovers_isIntegralClosure_localizationsAway_of_regular u a e he ha
  letI : IsIntegralClosure C R TC := hC
  change algebraMap C TC
    (normalizationEquivStandardCoversOfGenericEquiv u a e he ha g x) = algebraMap N TC x
  rw [normalizationEquivStandardCoversOfGenericEquiv]
  exact IsIntegralClosure.algebraMap_equiv R N TC C x

/-- Localizing a regular quotient at a prime over its defining ideal agrees with
quotienting the corresponding local ring, and is therefore regular local. -/
theorem isRegularLocalRing_quotient_localization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I q : Ideal A) [q.IsPrime] (hIq : I ≤ q)
    [IsRegularRing (A ⧸ I)] :
    IsRegularLocalRing
      (Localization.AtPrime q ⧸ I.map (algebraMap A (Localization.AtPrime q))) := by
  let D := A ⧸ I
  let p : Ideal D := q.map (Ideal.Quotient.mk I)
  letI : p.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIq
  let L := Localization.AtPrime q
  let J : Ideal L := I.map (algebraMap A L)
  let Q := L ⧸ J
  letI : Algebra D Q :=
    (Ideal.quotientMap (I := I) J (algebraMap A L)
      (by exact Ideal.le_comap_map)).toAlgebra
  letI : IsLocalization (Algebra.algebraMapSubmonoid D q.primeCompl) Q := by
    exact IsLocalization.of_surjective q.primeCompl L
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective rfl
      (by rw [Ideal.mk_ker, Ideal.mk_ker])
  letI : p.LiesOver q := ⟨(Ideal.comap_map_mk hIq).symm⟩
  have hM : Algebra.algebraMapSubmonoid D q.primeCompl = p.primeCompl :=
    Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective p q
      Ideal.Quotient.mk_surjective
  letI : IsLocalization p.primeCompl Q := hM ▸ inferInstance
  have hpreg : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
  have hQreg : IsRegularLocalRing Q :=
    @IsRegularLocalRing.of_ringEquiv (Localization.AtPrime p) _ hpreg Q _
      (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) Q).toRingEquiv
  exact hQreg

/-- The localizations of the standard root algebra at primes over the branch divisor are
regular local.  This is the local-regularity verification explicitly suggested, but
omitted, in the proof of Stacks Tag `0EYH`.

Indeed `C/(z) ≅ R/(a)` is regular, `z` is a nonzerodivisor, and the principal regular
quotient criterion (Tag `00NU`) lifts regularity across `z`. -/
theorem standardCover_isRegularLocalRing_atPrime_over_divisor
    [IsNoetherianRing R] (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    (q : Ideal (AdjoinRoot (Pcf.LocalModel.localPoly u a e))) [q.IsPrime]
    (haq : algebraMap R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) a ∈ q) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let C := AdjoinRoot (Pcf.LocalModel.localPoly u a e)
  let z : C := AdjoinRoot.root (Pcf.LocalModel.localPoly u a e)
  let I : Ideal C := Ideal.span {z}
  let D := C ⧸ I
  have hzq : z ∈ q := by
    apply Ideal.IsPrime.mem_of_pow_mem (I := q) inferInstance e
    dsimp only [z, C]
    rw [Pcf.LocalModel.root_pow_eq]
    simpa only [map_mul] using q.mul_mem_left (algebraMap R C (u : R)) haq
  have hIq : I ≤ q := by
    change Ideal.span ({z} : Set C) ≤ q
    rw [Ideal.span_le]
    simpa using hzq
  let L := Localization.AtPrime q
  let J : Ideal L := I.map (algebraMap C L)
  have hDreg : IsRegularRing D := by
    dsimp only [D, I, z, C]
    exact IsRegularRing.of_ringEquiv
      (Pcf.LocalModel.quotientRootEquiv u a he).toRingEquiv.symm
  letI : IsRegularRing D := hDreg
  have hQreg : IsRegularLocalRing (L ⧸ J) :=
    isRegularLocalRing_quotient_localization I q hIq
  let x : L := algebraMap C L z
  have hxmax : x ∈ IsLocalRing.maximalIdeal L := by
    rw [show IsLocalRing.maximalIdeal L = q.map (algebraMap C L) from
      Localization.AtPrime.map_eq_maximalIdeal.symm]
    exact Ideal.mem_map_of_mem _ hzq
  have hxreg : x ∈ nonZeroDivisors L := by
    exact IsLocalization.map_nonZeroDivisors_le q.primeCompl L
      ⟨z, Pcf.LocalModel.root_mem_nonZeroDivisors u a he ha, rfl⟩
  have hJ : J = Ideal.span ({x} : Set L) := by
    change (Ideal.span ({z} : Set C)).map (algebraMap C L) =
      Ideal.span ({x} : Set L)
    rw [Ideal.map_span, Set.image_singleton]
  letI : IsRegularLocalRing (L ⧸ Ideal.span ({x} : Set L)) :=
    IsRegularLocalRing.of_ringEquiv
      (Ideal.quotientEquivAlgOfEq ℤ hJ).toRingEquiv
  exact Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor x hxmax hxreg

#print axioms isIntegrallyClosedIn_away_of_span_isRadical
#print axioms isReduced_of_isRegularRing
#print axioms standardCover_isIntegralClosure_localizationAway
#print axioms standardCover_isIntegralClosure_localizationAway_of_regular
#print axioms isIntegralClosure_pi_of_fintype
#print axioms standardCovers_isIntegralClosure_localizationsAway_of_regular
#print axioms normalizationEquivStandardCoversOfGenericEquiv
#print axioms algebraMap_normalizationEquivStandardCoversOfGenericEquiv
#print axioms standardCover_isRegularLocalRing_atPrime_over_divisor

end Pcf.Stacks
