/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedAmbient
public import Pcf.Examples.PaperP.AffineLociBridge
public import Pcf.Stacks.Common.RegularNormal
public import Pcf.Vendor.RegularLocalization.Depth
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Local structure of the pinched plane: `ν` is an isomorphism off `o`, `X` is `R₁`,
not normal at `o`, and has depth one at `o`

For `paper-p.tex`, the unlabelled remark in Example `ex:pinched` ("The ideal
`𝔪_{p₁} ∩ 𝔪_{p₂}` of `k[z,w]` lies in `R`, so `ν` is an isomorphism away from
`o` ... This implies that `X` is regular in codimension one, and it is not normal
at `o`, where it has depth one"), with `R = {h : h(2,1) = h(-2,1)}`, `S = k[z,w]`:

* `mul_mem_of_mem_oIdeal`: the conductor; `h ∈ 𝔪_o` gives `h·S ⊆ R`.
* `isLocalization_away_of_mem_oIdeal`: for `0 ≠ h ∈ 𝔪_o` (e.g. `w - 1`, `z² - 4`)
  `S_h` is the localization `R_h`, i.e. `ν` is an isomorphism over `D(h)`
  (`nu_isIso_away`).
* `basicOpen_cover`: `D(w - 1) ∪ D(z² - 4) = X ∖ {o}`.
* `isRegularLocalRing_of_ne_oIdeal`: `R_P` is regular for every prime `P ≠ 𝔪_o`;
  `oIdeal_height`: `𝔪_o` has height `≥ 2`; hence `regularInCodimOne`: every prime of
  height `≤ 1` has regular local ring.
* `not_isIntegrallyClosed_at_o`, `not_isRegularLocalRing_at_o`: `R_o` is not normal
  (`z = z(w - 1)/(w - 1)` is integral, not in `R_o`), so not regular.
* `depth_at_o`: `depth R_o = 1` (the class of `z(w - 1)` in `R_o/(w - 1)` is killed by
  the maximal ideal).
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedLocalStructure

open AlgebraicGeometry CategoryTheory MvPolynomial Pcf.Examples.Pinched
  Pcf.Examples.PaperP.PinchedNormalization

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k
local notation "S" => PlaneRing k

/-- The ideal `𝔪_o = {h ∈ R : h(2,1) = 0}` of the glued point `o`. -/
noncomputable def oIdeal : Ideal R :=
  RingHom.ker ((evalTwoOne k).toRingHom.comp (algebraMap R S))

omit [CharZero k] in
theorem mem_oIdeal_iff (h : R) : h ∈ oIdeal k ↔ evalTwoOne k (PinchedRing.val k h) = 0 :=
  Iff.rfl

omit [CharZero k] in
theorem evalNegTwoOne_eq (h : R) :
    evalNegTwoOne k (PinchedRing.val k h) = evalTwoOne k (PinchedRing.val k h) :=
  ((mem_pinchedAlg_iff k).mp (PinchedRing.val_mem k h)).symm

instance oIdeal_isMaximal : (oIdeal k).IsMaximal := by
  unfold oIdeal
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  refine ⟨algebraMap k R c, ?_⟩
  change evalTwoOne k (algebraMap k S c) = c
  simp

/-- The glued point `o ∈ X`. -/
noncomputable def oPoint : Spec (.of R) := ⟨oIdeal k, inferInstance⟩

/-- The point `p₁ = (2, 1)` of `𝔸²`. -/
noncomputable def pOne : Spec (.of S) := ⟨RingHom.ker (evalTwoOne k).toRingHom, RingHom.ker_isPrime _⟩

/-- The point `p₂ = (-2, 1)` of `𝔸²`. -/
noncomputable def pTwo : Spec (.of S) :=
  ⟨RingHom.ker (evalNegTwoOne k).toRingHom, RingHom.ker_isPrime _⟩

omit [CharZero k] in
/-- `o = ν(p₁) = ν(p₂)`. -/
theorem nu_pOne : PinchedAmbient.nu k (pOne k) = oPoint k := rfl

omit [CharZero k] in
theorem nu_pTwo : PinchedAmbient.nu k (pTwo k) = oPoint k := by
  apply PrimeSpectrum.ext
  ext h
  change evalNegTwoOne k (PinchedRing.val k h) = 0 ↔ evalTwoOne k (PinchedRing.val k h) = 0
  rw [evalNegTwoOne_eq]

omit [CharZero k] in
/-- **The conductor**: an element of `𝔪_o` multiplies `S` into `R`. -/
theorem mul_mem_of_mem_oIdeal {h : R} (hh : h ∈ oIdeal k) (s : S) :
    PinchedRing.val k h * s ∈ pinchedAlg k := by
  have h1 := (mem_oIdeal_iff k h).mp hh
  have h2 := evalNegTwoOne_eq k h
  rw [h1] at h2
  rw [mem_pinchedAlg_iff, map_mul, map_mul]
  change evalTwoOne k _ * _ = evalNegTwoOne k _ * _
  rw [h1, h2, zero_mul, zero_mul]

/-- The element `w - 1 ∈ R`. -/
noncomputable def wSubOne : R :=
  PinchedRing.mk k (X 1 - 1) (Subalgebra.sub_mem _ (w_mem k) (Subalgebra.one_mem _))

/-- The element `z² - 4 ∈ R`. -/
noncomputable def zSqSubFour : R :=
  PinchedRing.mk k (X 0 ^ 2 - 4) (Subalgebra.sub_mem _ (z_sq_mem k)
    (by rw [mem_pinchedAlg_iff]; simp))

theorem wSubOne_mem_oIdeal : wSubOne k ∈ oIdeal k := by
  rw [mem_oIdeal_iff]; change evalTwoOne k (X 1 - 1) = 0; simp [evalTwoOne]

theorem zSqSubFour_mem_oIdeal : zSqSubFour k ∈ oIdeal k := by
  rw [mem_oIdeal_iff]; change evalTwoOne k (X 0 ^ 2 - 4) = 0; simp [evalTwoOne]; norm_num

theorem wSubOne_ne_zero : wSubOne k ≠ 0 := by
  intro h
  have := congrArg (PinchedRing.val k) h
  change (X 1 - 1 : S) = 0 at this
  have h2 := congrArg (aeval ![(0 : k), 0]) this
  simp at h2

theorem zSqSubFour_ne_zero : zSqSubFour k ≠ 0 := by
  intro h
  have := congrArg (PinchedRing.val k) h
  change (X 0 ^ 2 - 4 : S) = 0 at this
  have h2 := congrArg (aeval ![(0 : k), 0]) this
  simp at h2

#print axioms mul_mem_of_mem_oIdeal
#print axioms nu_pTwo

/-! ### Localizations along the conductor -/

section Generic

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- If `c ∈ M` multiplies `B` into `A`, and the `A`-element `c·u` lies in `M` for every
`u ∈ N`, then a localization `B_N` is the localization `A_M`. -/
theorem isLocalization_of_conductor (hAB : Function.Injective (algebraMap A B))
    (M : Submonoid A) (N : Submonoid B) (T : Type*) [CommRing T] [Algebra B T] [Algebra A T]
    [IsScalarTower A B T] [IsLocalization N T] (hN : N ≤ nonZeroDivisors B)
    (hMN : ∀ m ∈ M, algebraMap A B m ∈ N) (c : A)
    (hcond : ∀ b : B, ∃ a : A, algebraMap A B a = algebraMap A B c * b)
    (hden : ∀ a : A, ∀ u ∈ N, algebraMap A B a = algebraMap A B c * u → a ∈ M) :
    IsLocalization M T := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨m, hm⟩
    rw [IsScalarTower.algebraMap_apply A B T]
    exact IsLocalization.map_units T (⟨_, hMN m hm⟩ : N)
  · intro z
    obtain ⟨⟨b, u⟩, hz⟩ := IsLocalization.surj N z
    obtain ⟨a1, ha1⟩ := hcond b
    obtain ⟨a2, ha2⟩ := hcond u
    refine ⟨(a1, ⟨a2, hden a2 u u.2 ha2⟩), ?_⟩
    simp only [IsScalarTower.algebraMap_apply A B T, ha1, ha2, map_mul]
    rw [← hz]; ring
  · intro x y hxy
    refine ⟨1, ?_⟩
    rw [IsScalarTower.algebraMap_apply A B T, IsScalarTower.algebraMap_apply A B T] at hxy
    rw [hAB (IsLocalization.injective T hN hxy)]

end Generic

theorem conductor (h : R) (hh : h ∈ oIdeal k) (s : S) :
    ∃ a : R, algebraMap R S a = algebraMap R S h * s :=
  ⟨PinchedRing.mk k _ (mul_mem_of_mem_oIdeal k hh s), rfl⟩

omit [CharZero k] in
theorem algebraMap_injective : Function.Injective (algebraMap R S) :=
  FaithfulSMul.algebraMap_injective _ _

/-- **`ν` is an isomorphism over `D(h)`** for `0 ≠ h ∈ 𝔪_o`: `S_h` is the localization `R_h`. -/
theorem isLocalization_away_of_mem_oIdeal (h : R) (hh : h ∈ oIdeal k) (h0 : h ≠ 0) :
    IsLocalization.Away h (Localization.Away (algebraMap R S h)) := by
  refine isLocalization_of_conductor (algebraMap_injective k) _ (Submonoid.powers (algebraMap R S h))
    _ ?_ ?_ h (conductor k h hh) ?_
  · exact powers_le_nonZeroDivisors_of_noZeroDivisors
      ((map_ne_zero_iff _ (algebraMap_injective k)).mpr h0)
  · rintro m ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  · rintro a u ⟨n, rfl⟩ hu
    refine ⟨n + 1, algebraMap_injective k ?_⟩
    rw [hu, map_pow, pow_succ']

/-- The scheme map `Spec S_h → Spec R_h` is an isomorphism (`ν` restricted over `D(h)`).

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem nu_isIso_away (h : R) (hh : h ∈ oIdeal k) (h0 : h ≠ 0) :
    IsIso (Spec.map (CommRingCat.ofHom
      (Localization.awayMap (algebraMap R S) h))) := by
  haveI := isLocalization_away_of_mem_oIdeal k h hh h0
  let e : Localization.Away h ≃ₐ[R] Localization.Away (algebraMap R S h) :=
    IsLocalization.algEquiv (Submonoid.powers h) _ _
  have he : (Localization.awayMap (algebraMap R S) h) = e.toRingEquiv.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers h)
    ext r
    simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    change _ = e (algebraMap R _ r)
    rw [AlgEquiv.commutes]
    exact (IsScalarTower.algebraMap_apply R S _ r)
  rw [he]
  exact inferInstanceAs (IsIso (Spec.map (e.toRingEquiv.toCommRingCatIso.hom)))

#print axioms isLocalization_away_of_mem_oIdeal
#print axioms nu_isIso_away

/-! ### `D(w - 1) ∪ D(z² - 4) = X ∖ {o}` -/

theorem val_mem_glueIdeal {h : R} (hh : h ∈ oIdeal k) : PinchedRing.val k h ∈ glueIdeal k := by
  obtain ⟨a, ha⟩ := sub_C_mem_glueIdeal k (PinchedRing.val_mem k h)
  have e := evalTwoOne_eq_zero_of_mem k ha
  rw [map_sub] at e
  change evalTwoOne k _ - evalTwoOne k _ = 0 at e
  rw [(mem_oIdeal_iff k h).mp hh] at e
  have : a = 0 := by simpa [evalTwoOne] using e
  simpa [this] using ha

theorem oIdeal_le_of_mem {P : Ideal R} [hP : P.IsPrime] (hw : wSubOne k ∈ P)
    (hz : zSqSubFour k ∈ P) : oIdeal k ≤ P := by
  intro h hh
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp (val_mem_glueIdeal k hh)
  apply hP.mem_of_pow_mem 2
  obtain ⟨r1, hr1⟩ := conductor k h hh a
  obtain ⟨r2, hr2⟩ := conductor k h hh b
  have : h ^ 2 = r1 * wSubOne k + r2 * zSqSubFour k := by
    apply algebraMap_injective k
    rw [map_add, map_mul, map_mul, hr1, hr2, map_pow]
    change PinchedRing.val k h ^ 2 = PinchedRing.val k h * a * (X 1 - 1) +
      PinchedRing.val k h * b * (X 0 ^ 2 - 4)
    rw [sq]
    nth_rewrite 2 [← hab]
    ring
  rw [this]
  exact P.add_mem (P.mul_mem_left _ hw) (P.mul_mem_left _ hz)

/-- **`D(w - 1) ∪ D(z² - 4) = X ∖ {o}`**. -/
theorem basicOpen_cover (P : Spec (.of R)) :
    (wSubOne k ∉ P.asIdeal ∨ zSqSubFour k ∉ P.asIdeal) ↔ P ≠ oPoint k := by
  constructor
  · rintro (h | h) rfl
    · exact h (wSubOne_mem_oIdeal k)
    · exact h (zSqSubFour_mem_oIdeal k)
  · intro hne
    by_contra hc
    push_neg at hc
    apply hne
    apply PrimeSpectrum.ext
    exact ((oIdeal_isMaximal k).eq_of_le P.isPrime.ne_top (oIdeal_le_of_mem k hc.1 hc.2)).symm

#print axioms basicOpen_cover

/-! ### `X` is regular away from `o`, hence regular in codimension one -/

/-- For a prime `P ≠ 𝔪_o`, `R_P` is the localization of `S` at a prime over `P`. -/
theorem exists_isLocalization_atPrime (P : Ideal R) [hP : P.IsPrime] (hne : P ≠ oIdeal k) :
    ∃ (Q : Ideal S) (_ : Q.IsPrime), Q.comap (algebraMap R S) = P ∧
      IsLocalization.AtPrime (Localization.AtPrime Q) P := by
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal S)
    (Ideal.comap_bot_le_of_injective _ (algebraMap_injective k))
  refine ⟨Q, hQ, hQP, ?_⟩
  have hc : ∃ c ∈ oIdeal k, c ∉ P := by
    by_contra hcon
    push_neg at hcon
    exact hne ((oIdeal_isMaximal k).eq_of_le hP.ne_top
      (fun x hx => hcon x hx)).symm
  obtain ⟨c, hco, hcP⟩ := hc
  refine isLocalization_of_conductor (algebraMap_injective k) P.primeCompl Q.primeCompl _
    (Q.primeCompl_le_nonZeroDivisors) ?_ c (conductor k c hco) ?_
  · intro m hm hmQ
    exact hm (by rw [← hQP]; exact hmQ)
  · intro a u hu ha haP
    have : algebraMap R S a ∈ Q := by
      have h' : a ∈ Q.under R := hQP ▸ haP
      exact h'
    rw [ha] at this
    rcases hQ.mem_or_mem this with h | h
    · exact hcP (by rw [← hQP]; exact h)
    · exact hu h

/-- **`X` is regular away from `o`**. -/
theorem isRegularLocalRing_of_ne_oIdeal (P : Ideal R) [P.IsPrime] (hne : P ≠ oIdeal k) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  obtain ⟨Q, hQ, -, hloc⟩ := exists_isLocalization_atPrime k P hne
  let e := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) (Localization.AtPrime Q)
  exact IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv

#print axioms isRegularLocalRing_of_ne_oIdeal

/-! ### `X` is not normal at `o` and has depth one there -/

/-- The element `c = z(w - 1) ∈ R`. -/
noncomputable def cElt : R := PinchedRing.mk k (X 0 * (X 1 - 1)) (z_mul_w_sub_one_mem k)

/-- The element `b = z² ∈ R`. -/
noncomputable def bElt : R := PinchedRing.mk k (X 0 ^ 2) (z_sq_mem k)

/-- If `r·(w - 1) = s·z(w - 1)` in `R` (that is, `r = z·s` in `S`), then `s(p₁) = 0`. -/
theorem mem_oIdeal_of_mul_eq (r s : R) (h : r * wSubOne k = s * cElt k) : s ∈ oIdeal k := by
  have hv := congrArg (PinchedRing.val k) h
  change PinchedRing.val k r * (X 1 - 1) = PinchedRing.val k s * (X 0 * (X 1 - 1)) at hv
  have hne : (X 1 - 1 : S) ≠ 0 := by
    intro h0
    have h2 := congrArg (aeval ![(0 : k), 0]) h0
    simp at h2
  have hr : PinchedRing.val k r = X 0 * PinchedRing.val k s :=
    mul_right_cancel₀ hne (by rw [hv]; ring)
  have h1 := evalNegTwoOne_eq k r
  have h2 := evalNegTwoOne_eq k s
  rw [hr, map_mul, map_mul] at h1
  change evalNegTwoOne k (X 0) * _ = evalTwoOne k (X 0) * _ at h1
  rw [h2] at h1
  simp only [evalNegTwoOne, evalTwoOne, aeval_X] at h1
  rw [mem_oIdeal_iff]
  have : (4 : k) * evalTwoOne k (PinchedRing.val k s) = 0 := by
    simp only [Matrix.cons_val_zero] at h1
    change -2 * evalTwoOne k _ = 2 * evalTwoOne k _ at h1
    linear_combination -h1
  simpa using this

local notation "Ao" => Localization.AtPrime (oIdeal k)

theorem algebraMap_Ao_injective : Function.Injective (algebraMap R Ao) :=
  IsLocalization.injective _ (oIdeal k).primeCompl_le_nonZeroDivisors

theorem cElt_sq : cElt k ^ 2 = bElt k * wSubOne k ^ 2 := by
  apply algebraMap_injective k
  change (X 0 * (X 1 - 1) : S) ^ 2 = X 0 ^ 2 * (X 1 - 1) ^ 2
  ring

/-- **`X` is not normal at `o`**: `z = z(w-1)/(w-1)` is integral over `R_o` but not in it.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem not_isIntegrallyClosed_at_o : ¬ IsIntegrallyClosed Ao := by
  intro hA
  let K := FractionRing Ao
  let φ : R →+* K := (algebraMap Ao K).comp (algebraMap R Ao)
  have hφ : Function.Injective φ :=
    (IsFractionRing.injective Ao K).comp (algebraMap_Ao_injective k)
  have hw : φ (wSubOne k) ≠ 0 := (map_ne_zero_iff _ hφ).mpr (wSubOne_ne_zero k)
  let x : K := φ (cElt k) / φ (wSubOne k)
  have hint : IsIntegral Ao x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (algebraMap R Ao (bElt k)),
      Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    change x ^ 2 - φ (bElt k) = 0
    simp only [x, div_pow]
    rw [div_sub' (pow_ne_zero 2 hw), ← map_pow, ← map_pow, ← map_mul, ← map_sub, cElt_sq,
      mul_comm (bElt k), sub_self, map_zero, zero_div]
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp hA hint
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (oIdeal k).primeCompl y
  apply s.2
  apply mem_oIdeal_of_mul_eq k r s
  apply algebraMap_Ao_injective k
  apply IsFractionRing.injective Ao K
  have hs : algebraMap Ao K (IsLocalization.mk' Ao r s) * φ s = φ r := by
    simp only [φ, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
  change φ (r * wSubOne k) = φ (s * cElt k)
  rw [map_mul, map_mul, ← hs, hy]
  show φ (cElt k) / φ (wSubOne k) * φ s * φ (wSubOne k) = φ s * φ (cElt k)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hw]
  ring

/-- A regular local ring is normal, so `R_o` is not regular: `Sing X ∋ o`. -/
theorem not_isRegularLocalRing_at_o : ¬ IsRegularLocalRing Ao := fun h =>
  not_isIntegrallyClosed_at_o k (@Pcf.Stacks.isIntegrallyClosed_of_isRegularLocalRing _ _ h)

#print axioms not_isIntegrallyClosed_at_o
#print axioms not_isRegularLocalRing_at_o

/-! ### Depth one at `o` -/

/-- The image of `w - 1` in `R_o`. -/
noncomputable abbrev xo : Ao := algebraMap R Ao (wSubOne k)

theorem xo_ne_zero : xo k ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap_Ao_injective k)).mpr (wSubOne_ne_zero k)

theorem xo_isSMulRegular : IsSMulRegular Ao (xo k) := fun a b h => by
  simp only [smul_eq_mul] at h
  exact mul_left_cancel₀ (xo_ne_zero k) h

theorem xo_mem_maximalIdeal : xo k ∈ IsLocalRing.maximalIdeal Ao :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff Ao (oIdeal k) _).mpr (wSubOne_mem_oIdeal k)

/-- `z(w - 1) ∉ (w - 1)·R_o`. -/
theorem cElt_not_mem_span : algebraMap R Ao (cElt k) ∉ Ideal.span {xo k} := by
  intro h
  obtain ⟨α, hα⟩ := Ideal.mem_span_singleton'.mp h
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (oIdeal k).primeCompl α
  dsimp only at hα
  apply s.2
  apply mem_oIdeal_of_mul_eq k r s
  apply algebraMap_Ao_injective k
  rw [map_mul, map_mul, ← hα, ← mul_assoc, mul_comm (algebraMap R Ao (s : R)),
    IsLocalization.mk'_spec]

/-- The maximal ideal of `R_o` multiplies `z(w - 1)` into `(w - 1)·R_o`. -/
theorem maximalIdeal_mul_cElt_mem (α : Ao) (hα : α ∈ IsLocalRing.maximalIdeal Ao) :
    α * algebraMap R Ao (cElt k) ∈ Ideal.span {xo k} := by
  obtain ⟨⟨h, s⟩, rfl⟩ := IsLocalization.mk'_surjective (oIdeal k).primeCompl α
  dsimp only at hα ⊢
  have hh : h ∈ oIdeal k := (IsLocalization.AtPrime.mk'_mem_maximal_iff Ao (oIdeal k) h s).mp hα
  obtain ⟨t, ht⟩ := conductor k h hh (X 0)
  rw [Ideal.mem_span_singleton']
  refine ⟨IsLocalization.mk' Ao t s, ?_⟩
  have : h * cElt k = t * wSubOne k := by
    apply algebraMap_injective k
    rw [map_mul, map_mul, ht]
    change PinchedRing.val k h * (X 0 * (X 1 - 1)) = PinchedRing.val k h * X 0 * (X 1 - 1)
    ring
  have h2 := congrArg (algebraMap R Ao) this
  simp only [map_mul] at h2
  rw [IsLocalization.mk'_eq_mul_mk'_one t, IsLocalization.mk'_eq_mul_mk'_one h]
  linear_combination (-(IsLocalization.mk' Ao (1 : R) s)) * h2

/-- The quotient `R_o/(w - 1)`. -/
abbrev QuotO := Ao ⧸ Ideal.span {xo k}

instance : Nontrivial (QuotO k) :=
  Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top
    ((IsLocalRing.mem_maximalIdeal _).mp (xo_mem_maximalIdeal k)))

instance : IsLocalRing (QuotO k) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The nonzero `R_o`-linear map `κ(o) → R_o/(w - 1)`, `1 ↦ z(w - 1)`. -/
noncomputable def socleMap :
    (QuotO k ⧸ IsLocalRing.maximalIdeal (QuotO k)) →ₗ[QuotO k] QuotO k := by
  refine (IsLocalRing.maximalIdeal (QuotO k)).liftQ
    (LinearMap.toSpanSingleton _ _ (Ideal.Quotient.mk _ (algebraMap R Ao (cElt k)))) ?_
  intro a ha
  obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hα : α ∈ IsLocalRing.maximalIdeal Ao := by
    by_contra hn
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hn
    exact (IsLocalRing.mem_maximalIdeal _).mp ha (hn.map _)
  rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact maximalIdeal_mul_cElt_mem k α hα

/-- **Depth one at `o`**: `depth R_o = 1`.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem depth_at_o : IsLocalRing.depth (ModuleCat.of Ao Ao) = 1 := by
  rw [← Pcf.Vendor.IsLocalRing.depth_quotient_span_isSMulRegular_succ_eq_depth (xo k)
    (xo_isSMulRegular k) (xo_mem_maximalIdeal k)]
  have h0 : IsLocalRing.depth (ModuleCat.of (QuotO k) (QuotO k)) = 0 := by
    unfold IsLocalRing.depth Ideal.depth
    rw [ModuleCat.depth_eq_zero_iff_nontrivial_linearMap]
    let A' := QuotO k
    let ψ := (socleMap k).comp (Shrink.linearEquiv A' (A' ⧸ IsLocalRing.maximalIdeal A')).toLinearMap
    refine nontrivial_of_ne ψ 0 ?_
    intro hψ
    have := LinearMap.congr_fun hψ ((Shrink.linearEquiv A' _).symm
      (Submodule.Quotient.mk (p := IsLocalRing.maximalIdeal A') (1 : A')))
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearMap.zero_apply] at this
    erw [LinearEquiv.apply_symm_apply] at this
    unfold socleMap at this
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul,
      Ideal.Quotient.eq_zero_iff_mem] at this
    exact cElt_not_mem_span k this
  rw [h0]
  rfl

#print axioms depth_at_o

end Pcf.Examples.PaperP.PinchedLocalStructure
