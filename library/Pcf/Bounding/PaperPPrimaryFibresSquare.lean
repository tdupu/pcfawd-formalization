/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.Divisors
public import Pcf.Bounding.PrimaryHeightOneDVR
public import Pcf.Bounding.PrimaryReducedFiberLocal
public import Pcf.Bounding.SmoothRegularLocal
public import Pcf.Stacks.Abhyankar.StandardCoverNormalization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# The comparison square in the proof of `lem:primary-fibres` (affine form)

`paper-p.tex`, proof of Lemma `lem:primary-fibres`:

> Let `D', F'` be the unique integral effective divisors over `D, F`; then `F'` dominates `D'`,
> and the fibre at `F'` is reduced, so `v_{F'}(q'^* t') = 1` for a local equation `t'` of `D'`.
> Comparing orders of `t` around the square gives
> `e(F'/F) v_F(q^* t) = e(D'/D) v_{F'}(q'^* t') = e(D'/D)`.

Encoding (affine charts). The square is a commutative square of rings
```
A' ---> R'
^       ^
|       |
A  ---> R
```
of Noetherian normal domains (`B = Spec A`, `E ⊇ Spec R`, `B' = Spec A'`, `E' ⊇ Spec R'`).
Divisors are height-one primes; for a height-one prime `F` of `R` over `D` of `A`,
`v_F(q^* t)` is Mathlib's `F.ramificationIdx A` (length of `R_F / D R_F`), and
`e(F'/F) = F'.ramificationIdx R`, `e(D'/D) = D'.ramificationIdx A`,
`v_{F'}(q'^* t') = F'.ramificationIdx A'`.

The theorem `primaryFibres_square_display` takes the square abstractly (finite base and source
alterations, `R'` finitely presented over `A'`, and `R'` smooth over `A'` at its generic point)
and proves, away from a nonzero `c ∈ A`, the display and `v_F(q^* t) ∣ e(D'/D)`.

Divergence from the paper (reduced fibres). The paper obtains reduced fibres of `q'` over a
dense open of `B'` from geometric reducedness of the generic fibre via Stacks `0578`. Here
reducedness of the fibre at `F'` comes from smoothness: the smooth locus of `R'/A'` is open
(Mathlib `Algebra.isOpen_smoothLocus`) and contains the generic point, so it contains a basic
open `D(g)`, `g ≠ 0`; the finitely many height-one primes of `R'` containing `g` (minimal
primes of `(g)`) are removed by a nonzero `c ∈ A`. Over `D(g)` the fibre of the smooth algebra
`R'_g` over a field is regular, hence reduced, which gives `v_{F'}(q'^* t') = 1`. No `0578`
tag is attached.
-/

@[expose] public section

namespace Pcf.Bounding.PaperPPrimaryFibres

open IsLocalRing

set_option linter.style.haveILetI false

/-- Multiplicativity of `v` in a tower whose middle prime has height one (so its local ring is a
DVR and the localized extension is flat). -/
theorem ramificationIdx_tower_of_heightOne {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsNoetherianRing S] [IsDomain S] [IsIntegrallyClosed S] [IsDomain T] [FaithfulSMul S T]
    (q : Ideal S) [q.IsPrime] (hq : q.height = 1) (r : Ideal T) [r.IsPrime] [r.LiesOver q] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S := by
  letI := Localization.AtPrime.algebraOfLiesOver q r
  haveI : IsDiscreteValuationRing (Localization.AtPrime q) :=
    Pcf.isDiscreteValuationRing_localizationAtPrime_of_heightOne q hq
  have hinj :
      Function.Injective (algebraMap (Localization.AtPrime q) (Localization.AtPrime r)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
    change Localization.localRingHom q r (algebraMap S T) (Ideal.over_def r q)
      (IsLocalization.mk' (Localization.AtPrime q) a s) = 0 at hx
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨m, hm⟩, hma⟩ := hx
    have hm0 : m ≠ 0 := fun h => hm (h ▸ r.zero_mem)
    have ha : algebraMap S T a = 0 := (mul_eq_zero.mp hma).resolve_left hm0
    have ha0 : a = 0 := (FaithfulSMul.algebraMap_injective S T) (by rw [ha, map_zero])
    rw [ha0, IsLocalization.mk'_zero]
  haveI : FaithfulSMul (Localization.AtPrime q) (Localization.AtPrime r) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : Module.Flat (Localization.AtPrime q) (Localization.AtPrime r) := inferInstance
  exact Ideal.ramificationIdx_tower' (R := R) q r

/-- **Reduced fibre at `F'` ⇒ `v_{F'}(q'^* t') = 1`.** If `R'_g` is smooth over `A'` and the
height-one prime `F'` of `R'` avoids `g`, then `F'.ramificationIdx A' = 1`: the fibre of `R'_g`
over `D' = F' ∩ A'` is a smooth algebra over a field, hence regular and reduced. -/
theorem ramificationIdx_eq_one_of_smooth_away {A' R' : Type*} [CommRing A'] [CommRing R']
    [Algebra A' R'] [IsNoetherianRing A'] [IsDomain A'] [IsIntegrallyClosed A']
    [IsNoetherianRing R'] [IsDomain R'] [IsIntegrallyClosed R'] [FaithfulSMul A' R']
    (g : R') [Algebra.Smooth A' (Localization.Away g)]
    (𝔭' : Ideal A') [𝔭'.IsPrime] (h𝔭' : 𝔭'.height = 1)
    (Q' : Ideal R') [Q'.IsPrime] (hQ' : Q'.height = 1) [Q'.LiesOver 𝔭'] (hg : g ∉ Q') :
    Q'.ramificationIdx A' = 1 := by
  let S := Localization.Away g
  have hg0 : g ≠ 0 := fun h => hg (h ▸ Q'.zero_mem)
  have hM : Submonoid.powers g ≤ nonZeroDivisors R' :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hg0
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  haveI : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S _ hM
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers g) S inferInstance
  haveI : FaithfulSMul R' S := (faithfulSMul_iff_algebraMap_injective R' S).mpr
    (IsLocalization.injective S hM)
  haveI : FaithfulSMul A' S := FaithfulSMul.trans A' R' S
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid R') : Set R') (Q' : Set R') :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hg
  let Qg : Ideal S := Q'.map (algebraMap R' S)
  haveI hQgp : Qg.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ S Q' inferInstance hdisj
  have hQgc : Qg.comap (algebraMap R' S) = Q' :=
    IsLocalization.under_map_of_isPrime_disjoint _ S inferInstance hdisj
  have hQgh : Qg.height = 1 := by
    rw [IsLocalization.height_map_of_disjoint _ Q' hdisj, hQ']
  haveI : Qg.LiesOver Q' := ⟨hQgc.symm⟩
  haveI : Qg.LiesOver 𝔭' := Ideal.LiesOver.trans Qg Q' 𝔭'
  -- the fibre over `𝔭'` of the smooth algebra `S` is regular, hence reduced
  haveI : IsRegularRing (𝔭'.Fiber S) := Pcf.isRegularRing_of_smooth 𝔭'.ResidueField _
  have hring : _root_.IsReduced (𝔭'.Fiber S) := Pcf.Stacks.isReduced_of_isRegularRing
  let p : Pcf.HeightOnePrime A' := ⟨⟨𝔭', inferInstance⟩, h𝔭'⟩
  let Q : Pcf.HeightOnePrime S := ⟨⟨Qg, hQgp⟩, hQgh⟩
  haveI : Q.1.asIdeal.LiesOver p.1.asIdeal := inferInstanceAs (Qg.LiesOver 𝔭')
  let P : p.1.asIdeal.primesOver S := ⟨Q.1.asIdeal, ⟨inferInstance, inferInstance⟩⟩
  let q : PrimeSpectrum (p.1.asIdeal.Fiber S) :=
    PrimeSpectrum.primesOverOrderIsoFiber A' S p.1.asIdeal P
  have hq : q.asIdeal.comap Algebra.TensorProduct.includeRight = Q.1.asIdeal := by
    change ((PrimeSpectrum.primesOverOrderIsoFiber A' S p.1.asIdeal).symm q).1 = P.1
    exact congrArg Subtype.val
      ((PrimeSpectrum.primesOverOrderIsoFiber A' S p.1.asIdeal).symm_apply_apply P)
  have h1 : Qg.ramificationIdx A' = 1 :=
    Pcf.Bounding.PrimaryFibres.ramificationIdx_eq_one_of_reduced_affineFiber_dominant
      p Q q.asIdeal hq hring
  have h2 : Qg.ramificationIdx R' = 1 := by
    haveI : Algebra.IsUnramifiedAt R' Qg := by
      have hloc : IsLocalization.AtPrime (Localization.AtPrime Qg) Q' := by
        have := IsLocalization.isLocalization_atPrime_localization_atPrime
          (M := Submonoid.powers g) Qg
        have key : ∀ (I : Ideal R') (_ : I.IsPrime), I = Q' →
            ∀ (_ : IsLocalization.AtPrime (Localization.AtPrime Qg) I),
              IsLocalization.AtPrime (Localization.AtPrime Qg) Q' := by
          rintro I _ rfl h; exact h
        exact key _ _ hQgc this
      unfold Algebra.IsUnramifiedAt
      exact Algebra.FormallyUnramified.of_isLocalization Q'.primeCompl
    exact Ideal.ramificationIdx_eq_one Qg R'
  have h3 := ramificationIdx_tower_of_heightOne (R := A') Q' hQ' Qg
  rw [h1, h2, mul_one] at h3
  exact h3.symm

/-- A height-one prime containing a nonzero element `g` is a minimal prime of `(g)`. -/
theorem mem_minimalPrimes_span_of_height_eq_one {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R]
    (g : R) (hg : g ≠ 0) (Q : Ideal R) [Q.IsPrime] (hQ : Q.height = 1) (hgQ : g ∈ Q) :
    Q ∈ (Ideal.span {g}).minimalPrimes := by
  refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem Q).mpr hgQ⟩, ?_⟩
  rintro P ⟨hP, hgP⟩ hPQ
  by_contra hne
  have hlt : P < Q := lt_of_le_of_ne hPQ (fun h => hne (h ▸ le_rfl))
  have hbot := Pcf.Bounding.eq_bot_of_lt_of_height_eq_one Q hQ P hlt
  apply hg
  have : g ∈ P := (Ideal.span_singleton_le_iff_mem P).mp hgP
  rw [hbot] at this
  exact (Submodule.mem_bot R).mp this

/-- **The comparison square of `lem:primary-fibres` (affine form).** Let `A → R`, `A → A'`,
`R → R'`, `A' → R'` be a commutative square of injective maps of Noetherian normal domains, with
`A'` finite over `A`, `R'` finite over `R`, `R'` finitely presented over `A'`, and `R'` smooth
over `A'` at its generic point. Suppose `e(D'/D) ∣ p^a` for every height-one `D` of `A` and every
prime `D'` of `A'` over it. Then there is `c ≠ 0` in `A` such that for every height-one `D ∌ c`
and every height-one `F` of `R` over `D` there are height-one `D'`, `F'` over `D`, `F`, with `F'`
over `D'`, satisfying `v_{F'}(q'^* t') = 1`,
`e(F'/F) · v_F(q^* t) = e(D'/D) · v_{F'}(q'^* t') = e(D'/D)` and `v_F(q^* t) ∣ p^a`. -/
theorem primaryFibres_square_display (p a : ℕ)
    {A R A' R' : Type*} [CommRing A] [CommRing R] [CommRing A'] [CommRing R']
    [IsDomain A] [IsDomain R] [IsDomain A'] [IsDomain R']
    [IsNoetherianRing A] [IsNoetherianRing R] [IsNoetherianRing A'] [IsNoetherianRing R']
    [IsIntegrallyClosed A] [IsIntegrallyClosed R] [IsIntegrallyClosed A'] [IsIntegrallyClosed R']
    [Algebra A R] [Algebra A A'] [Algebra R R'] [Algebra A' R'] [Algebra A R']
    [IsScalarTower A R R'] [IsScalarTower A A' R']
    [FaithfulSMul A R] [FaithfulSMul A A'] [FaithfulSMul R R'] [FaithfulSMul A' R']
    [Module.Finite A A'] [Module.Finite R R'] [Algebra.FinitePresentation A' R']
    (hsm : Algebra.IsSmoothAt A' (⊥ : Ideal R'))
    (hbase : ∀ (D : Ideal A) [D.IsPrime], D.height = 1 →
      ∀ (D' : Ideal A') [D'.IsPrime], D'.LiesOver D → D'.ramificationIdx A ∣ p ^ a) :
    ∃ c : A, c ≠ 0 ∧ ∀ (D : Ideal A) [D.IsPrime], D.height = 1 → c ∉ D →
      ∀ (F : Ideal R) [F.IsPrime], F.height = 1 → F.LiesOver D →
        ∃ (D' : Ideal A') (F' : Ideal R') (_ : D'.IsPrime) (_ : F'.IsPrime),
          D'.height = 1 ∧ F'.height = 1 ∧ D'.LiesOver D ∧ F'.LiesOver F ∧ F'.LiesOver D' ∧
          F'.ramificationIdx A' = 1 ∧
          F'.ramificationIdx R * F.ramificationIdx A =
            D'.ramificationIdx A * F'.ramificationIdx A' ∧
          D'.ramificationIdx A * F'.ramificationIdx A' = D'.ramificationIdx A ∧
          F.ramificationIdx A ∣ p ^ a := by
  classical
  -- (1) a basic open `D(g)` of the generic point inside the smooth locus
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R') ∈ Algebra.smoothLocus A' R' := hsm
  obtain ⟨_, ⟨g, rfl⟩, hbg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hbot
      Algebra.isOpen_smoothLocus
  have hg0 : g ≠ 0 := fun h0 => hbg (by simp [h0])
  haveI : Algebra.Smooth A' (Localization.Away g) :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mp hsub
  -- (2) the finitely many divisors of `R'` containing `g`, removed by `c ∈ A`
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R' (Ideal.span {g})
  have hchoice : ∀ P : Ideal R', ∃ c : A, c ≠ 0 ∧ (P.under A ≠ ⊥ → c ∈ P.under A) := by
    intro P
    by_cases h : P.under A = ⊥
    · exact ⟨1, one_ne_zero, fun h' => absurd h h'⟩
    · obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      exact ⟨c, hc0, fun _ => hc⟩
  choose cP hcP0 hcP using hchoice
  let c : A := ∏ P ∈ hfin.toFinset, cP P
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun P _ => hcP0 P
  refine ⟨c, hc0, ?_⟩
  intro D _ hD hcD F _ hF hFD
  haveI := hFD
  haveI : Algebra.IsIntegral R R' := Algebra.IsIntegral.of_finite R R'
  -- (3) the divisors `F'` over `F` and `D' = F' ∩ A'`
  obtain ⟨F', -, hF'p, hF'F⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := R') F ⊥
      (Ideal.comap_bot_le_of_injective _ (FaithfulSMul.algebraMap_injective R R'))
  haveI := hF'p
  haveI hF'over : F'.LiesOver F := ⟨hF'F.symm⟩
  have hF'h : F'.height = 1 := by
    rw [← Pcf.height_under_eq_of_finite_of_normal (R := R) F', hF'F, hF]
  let D' : Ideal A' := F'.under A'
  haveI hD'p : D'.IsPrime := Ideal.IsPrime.under A' F'
  haveI hF'D' : F'.LiesOver D' := ⟨rfl⟩
  haveI hF'Dover : F'.LiesOver D := Ideal.LiesOver.trans F' F D
  have hD'D : D'.under A = D := by
    change (F'.under A').under A = D
    rw [Ideal.under_under, ← hF'Dover.over]
  haveI hD'over : D'.LiesOver D := ⟨hD'D.symm⟩
  have hD'h : D'.height = 1 := by
    rw [← Pcf.height_under_eq_of_finite_of_normal (R := A) D', hD'D, hD]
  -- (4) `g ∉ F'`, so the fibre at `F'` is reduced and `v_{F'}(q'^* t') = 1`
  have hgF' : g ∉ F' := by
    intro hg
    have hmin := mem_minimalPrimes_span_of_height_eq_one g hg0 F' hF'h hg
    have hmem : F' ∈ hfin.toFinset := hfin.mem_toFinset.mpr hmin
    have hFA : F'.under A = D := hF'Dover.over.symm
    have hDne : D ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hD
    have hcF : cP F' ∈ D := hFA ▸ hcP F' (hFA ▸ hDne)
    apply hcD
    rw [show c = cP F' * ∏ P ∈ hfin.toFinset.erase F', cP P from
      (Finset.mul_prod_erase _ _ hmem).symm]
    exact D.mul_mem_right _ hcF
  have h1 : F'.ramificationIdx A' = 1 :=
    ramificationIdx_eq_one_of_smooth_away g D' hD'h F' hF'h hgF'
  -- (5) the two paths around the square
  have hR := ramificationIdx_tower_of_heightOne (R := A) F hF F'
  have hA' := ramificationIdx_tower_of_heightOne (R := A) D' hD'h F'
  have hdisp : F'.ramificationIdx R * F.ramificationIdx A =
      D'.ramificationIdx A * F'.ramificationIdx A' := by
    rw [mul_comm, ← hR, hA']
  refine ⟨D', F', hD'p, hF'p, hD'h, hF'h, hD'over, hF'over, hF'D', h1, hdisp,
    by rw [h1, mul_one], ?_⟩
  -- (6) `v_F(q^* t) ∣ e(D'/D) ∣ p^a`
  exact (Dvd.intro_left (F'.ramificationIdx R) (by rw [hdisp, h1, mul_one])).trans
    (hbase D hD D' hD'over)

end Pcf.Bounding.PaperPPrimaryFibres

#print axioms Pcf.Bounding.PaperPPrimaryFibres.ramificationIdx_tower_of_heightOne
#print axioms Pcf.Bounding.PaperPPrimaryFibres.ramificationIdx_eq_one_of_smooth_away
#print axioms Pcf.Bounding.PaperPPrimaryFibres.primaryFibres_square_display
