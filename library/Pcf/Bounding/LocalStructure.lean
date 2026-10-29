/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Steps 3–4 of Theorem `thm:bounding`: the local structure of the restriction

Step 3 of the proof of Theorem `thm:bounding` in `latex/paper-p.tex` says that the preimage `T`
of `A ∩ V` in the étale-local model `V' = ∐ Spec R'[zᵢ]/(zᵢ^{eᵢ} − uᵢa)` is a union of connected
components of the reduced preimage `∐ V(zᵢ)` of the divisor, each mapping isomorphically to a
component of `D' = V(a)`. Step 4 concludes that the base change of the restriction `A ∩ V → D`
is étale at every point of `T`. This file proves the three general commutative-algebra
lemmas that make up that argument, for arbitrary rings:

* `Pcf.Bounding.mem_minimalPrimes_span_of_mem_minimalPrimes_map` — **the dimension count.**
  If `S → C` is flat and quasi-finite (étale, in the application), `𝔭` is a minimal prime
  over `(a₀)` in `S`, and `𝔮` is a minimal prime over `𝔭C`, then `𝔮` is a minimal prime over
  `(a₀)C`. This is the manuscript's "the étale, hence open, map `T → A ∩ V` sends the generic
  point of each component of `T` to the generic point of the irreducible `A ∩ V`, so `T` is
  equidimensional of dimension `dim D`", rephrased without dimensions: going down for the
  flat map `S → C` (Stacks Tag 00HS) and incomparability of primes in a fibre of a
  quasi-finite map.
* `Pcf.Bounding.exists_mul_mem_ker_of_mem_minimalPrimes_ker` — **a component is locally the
  whole space.** If `f : C → A` is surjective, `𝔮` is a minimal prime over `ker f`, and the
  local ring of `A` at the image of a prime `𝔫 ⊇ 𝔮` is a domain, then `𝔮 ⊆ ker f` locally at
  `𝔫`. This is "a reduced closed subset of full dimension in a scheme whose connected
  components are integral is a union of connected components", at one point.
* `Pcf.Bounding.isLocalization_of_localStructure` — **the conclusion of Step 4 at a point.**
  Given a ring map `θ : C → L` into a local ring that presents `L` as a localization of
  `C/I` (hypotheses `hsurj`, `hker`), where `C/(z) ≅ R/(a)` canonically (Step 3,
  `Pcf.LocalModel.quotientMap_bijective`), `z` is nilpotent modulo `a`, `I ⊆ (z)` locally
  (the two lemmas above) and `L` is reduced, the structure map `R/(a) → L` presents `L` as a
  localization of `R/(a)` at a prime. Hence `L` is formally étale over `R/(a)`:
  `Pcf.Bounding.formallyEtale_of_localStructure`.

None of these lemmas mentions purity, Abhyankar's lemma, or any specific ring; they are the
glue between Step 2's output and Step 4's conclusion.
-/

@[expose] public section

namespace Pcf.Bounding

open IsLocalRing

/-! ### The dimension count, without dimensions -/

/-- **Minimal primes over `𝔭C` are minimal over `aC`.** Let `S → C` be flat (so it has going
down) and quasi-finite (so primes in one fibre are incomparable). If `𝔭` is a minimal prime
over `(a₀)` in `S` and `𝔮` is a minimal prime over `𝔭C`, then `𝔮` is a minimal prime over
`(a₀)C`.

In the application `C` is a standard piece of the étale-local model and `𝔭` cuts out `A ∩ V`,
a component of `f⁻¹(D) = V(a)`; the conclusion says that every component of the preimage `T`
of `A ∩ V` is a component of the preimage of `D`, which is the content of the manuscript's
dimension count in Step 3. -/
theorem mem_minimalPrimes_span_of_mem_minimalPrimes_map
    {S C : Type*} [CommRing S] [CommRing C] [Algebra S C]
    [Algebra.HasGoingDown S C] [Algebra.QuasiFinite S C]
    {a₀ : S} {𝔭 : Ideal S} (h𝔭 : 𝔭 ∈ (Ideal.span {a₀}).minimalPrimes)
    {𝔮 : Ideal C} (h𝔮 : 𝔮 ∈ (𝔭.map (algebraMap S C)).minimalPrimes) :
    𝔮 ∈ (Ideal.span {algebraMap S C a₀}).minimalPrimes := by
  have h𝔭' : Minimal (fun q : Ideal S => q.IsPrime ∧ Ideal.span {a₀} ≤ q) 𝔭 := h𝔭
  have h𝔮' : Minimal (fun q : Ideal C => q.IsPrime ∧ 𝔭.map (algebraMap S C) ≤ q) 𝔮 := h𝔮
  have h𝔭p : 𝔭.IsPrime := h𝔭'.1.1
  have h𝔮p : 𝔮.IsPrime := h𝔮'.1.1
  -- `𝔮` lies over `𝔭`, by going down and minimality.
  have hunder : 𝔮.under S = 𝔭 := by
    have hle : 𝔭 ≤ 𝔮.under S := Ideal.map_le_iff_le_comap.mp h𝔮.1.2
    obtain ⟨P, hPle, hPprime, hPover⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) (q := 𝔮.under S) 𝔮 hle
    have hmapP : 𝔭.map (algebraMap S C) ≤ P :=
      Ideal.map_le_iff_le_comap.mpr (le_of_eq hPover.over)
    have hPQ : P = 𝔮 := h𝔮'.eq_of_le ⟨hPprime, hmapP⟩ hPle
    rw [← hPQ]
    exact hPover.over.symm
  refine ⟨⟨h𝔮p, ?_⟩, ?_⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h𝔮.1.2 (Ideal.mem_map_of_mem _ (h𝔭.1.2 (Ideal.mem_span_singleton_self a₀)))
  · rintro 𝔮' ⟨h𝔮'p, h𝔮'le⟩ hle
    -- `𝔮'` also lies over `𝔭`, by minimality of `𝔭` over `(a₀)`.
    have hunder' : 𝔮'.under S = 𝔭 := by
      refine h𝔭'.eq_of_le ⟨Ideal.comap_isPrime _ _, ?_⟩ ?_
      · rw [Ideal.span_le, Set.singleton_subset_iff, Ideal.under_def, SetLike.mem_coe,
          Ideal.mem_comap]
        exact h𝔮'le (Ideal.mem_span_singleton_self _)
      · rw [← hunder]
        exact Ideal.comap_mono hle
    -- Incomparability in the fibre over `𝔭`.
    have h : 𝔮' = 𝔮 :=
      Algebra.QuasiFiniteAt.eq_of_le_of_under_eq (R := S) hle (hunder'.trans hunder.symm)
    exact h.ge

/-! ### A component of `V(ker f)` is locally all of `V(ker f)` -/

/-- **A minimal prime over `ker f` is locally zero where the local ring of the quotient is a
domain.** Let `f : C → A` be surjective, `𝔮` a minimal prime over `ker f`, and `𝔫'` a prime
of `A` with `𝔮 ≤ f⁻¹(𝔫')`. If `A_{𝔫'}` is a domain, then every `c ∈ 𝔮` is killed modulo
`ker f` by some `t ∉ f⁻¹(𝔫')`.

In the application `f` is `C → C/(z) ≅ R'/(a)`, whose target is regular, hence has local
rings that are domains (Stacks Tag 00NP); `𝔮` is a component of the preimage of `A ∩ V`
through the chosen point, and the conclusion is that the preimage agrees with `V(z)` in a
neighbourhood of that point. -/
theorem exists_mul_mem_ker_of_mem_minimalPrimes_ker
    {C A : Type*} [CommRing C] [CommRing A] (f : C →+* A) (hf : Function.Surjective f)
    {𝔮 : Ideal C} (h𝔮 : 𝔮 ∈ (RingHom.ker f).minimalPrimes)
    (𝔫' : Ideal A) [𝔫'.IsPrime] [IsDomain (Localization.AtPrime 𝔫')]
    (hle : 𝔮 ≤ 𝔫'.comap f) :
    ∀ c ∈ 𝔮, ∃ t ∉ 𝔫'.comap f, t * c ∈ RingHom.ker f := by
  have h𝔮' : Minimal (fun q : Ideal C => q.IsPrime ∧ RingHom.ker f ≤ q) 𝔮 := h𝔮
  have h𝔮p : 𝔮.IsPrime := h𝔮'.1.1
  have hker : RingHom.ker f ≤ 𝔮 := h𝔮'.1.2
  -- The image `P` of `𝔮` is a prime of `A` contained in `𝔫'`.
  set P : Ideal A := 𝔮.map f with hPdef
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have hPle : P ≤ 𝔫' := Ideal.map_le_iff_le_comap.mpr hle
  -- The kernel `p₀` of `A → A_{𝔫'}` is a prime (the target is a domain) contained in `P`.
  set p₀ : Ideal A := (⊥ : Ideal (Localization.AtPrime 𝔫')).comap (algebraMap A _) with hp₀def
  have hp₀ : p₀.IsPrime := Ideal.comap_isPrime _ _
  have hp₀P : p₀ ≤ P := by
    intro x hx
    rw [hp₀def, Ideal.mem_comap, Ideal.mem_bot,
      IsLocalization.map_eq_zero_iff 𝔫'.primeCompl] at hx
    obtain ⟨⟨s, hs⟩, hsx⟩ := hx
    have hsP : s ∉ P := fun h => hs (hPle h)
    rcases hP.mem_or_mem (show s * x ∈ P by rw [hsx]; exact P.zero_mem) with h | h
    · exact absurd h hsP
    · exact h
  -- `P` is a minimal prime of `A`, because `𝔮` is minimal over `ker f`.
  have hPmin : ∀ Q : Ideal A, Q.IsPrime → Q ≤ P → P ≤ Q := by
    intro Q hQ hQP
    have h1 : RingHom.ker f ≤ Q.comap f := Ideal.ker_le_comap f
    have h2 : Q.comap f ≤ 𝔮 := by
      calc Q.comap f ≤ P.comap f := Ideal.comap_mono hQP
        _ = 𝔮 ⊔ (⊥ : Ideal A).comap f := Ideal.comap_map_of_surjective f hf 𝔮
        _ = 𝔮 := by rw [← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
    have h3 : 𝔮 ≤ Q.comap f := h𝔮'.2 ⟨Ideal.comap_isPrime _ _, h1⟩ h2
    calc P = 𝔮.map f := rfl
      _ ≤ (Q.comap f).map f := Ideal.map_mono h3
      _ = Q := Ideal.map_comap_of_surjective f hf Q
  have hPp₀ : P ≤ p₀ := hPmin p₀ hp₀ hp₀P
  -- Now unwind for `c ∈ 𝔮`.
  intro c hc
  have hfc : algebraMap A (Localization.AtPrime 𝔫') (f c) = 0 := by
    have : f c ∈ p₀ := hPp₀ (Ideal.mem_map_of_mem f hc)
    rwa [hp₀def, Ideal.mem_comap, Ideal.mem_bot] at this
  rw [IsLocalization.map_eq_zero_iff 𝔫'.primeCompl] at hfc
  obtain ⟨⟨s, hs⟩, hsfc⟩ := hfc
  obtain ⟨t, rfl⟩ := hf s
  refine ⟨t, fun ht => hs (Ideal.mem_comap.mp ht), ?_⟩
  rw [RingHom.mem_ker, map_mul]
  exact hsfc

/-! ### The conclusion of Step 4 at a point -/

variable {R C L : Type*} [CommRing R] [CommRing C] [CommRing L] [Algebra R C] [IsLocalRing L]

/-- **Step 4 at a point: the local ring of the base-changed restriction is a localization of
the base.**

The data: `R → C` (in the application `R'` and a standard piece `C = R'[z]/(z^e − ua)`), an
element `a ∈ R`, the element `z ∈ C`, an ideal `I ⊆ C` (the ideal of the preimage of `A ∩ V`),
a local ring `L` (the local ring of the base-changed restriction at a point of `T`) with a
ring map `θ : C → L` and an `R/(a)`-algebra structure compatible with it.

The hypotheses are the outputs of Steps 2 and 3:
* `ha`, `hbij`: `R/(a) → C/(z)` is bijective — Step 3, `Pcf.LocalModel.quotientMap_bijective`;
* `hz`: `z` is nilpotent modulo `(a)` — the equation `z^e = ua`;
* `haI`, `hIker`: `a ∈ I` and `θ` kills `I`;
* `hsurj`, `hker`: `L` is a localization of `C/I` through `θ`;
* `hloc`: `I ⊆ (z)` locally at the point — the two lemmas above;
* `IsReduced L` — étale base change of the integral `A ∩ V` is reduced (Stacks Tag 033B).

The conclusion: `L` is the localization of `R/(a)` at the prime `𝔮` under the maximal ideal.
So `T → D'` is, at this point, the identity on `D'`: the manuscript's "each mapping
isomorphically onto a connected component of `D'`". -/
theorem isLocalization_of_localStructure (a : R) (z : C) (θ : C →+* L) (I : Ideal C)
    [Algebra (R ⧸ Ideal.span {a}) L]
    (hcomp : ∀ r : R, θ (algebraMap R C r)
      = algebraMap (R ⧸ Ideal.span {a}) L (Ideal.Quotient.mk _ r))
    (ha : Ideal.span ({a} : Set R) ≤ (Ideal.span {z}).comap (algebraMap R C))
    (hbij : Function.Bijective (Ideal.quotientMap (Ideal.span {z}) (algebraMap R C) ha))
    (hz : ∃ n, z ^ n ∈ Ideal.span {algebraMap R C a})
    (haI : algebraMap R C a ∈ I) (hIker : ∀ c ∈ I, θ c = 0)
    (hsurj : ∀ x : L, ∃ c s : C, IsUnit (θ s) ∧ x * θ s = θ c)
    (hker : ∀ c : C, θ c = 0 → ∃ t : C, IsUnit (θ t) ∧ t * c ∈ I)
    (hloc : ∀ c ∈ I, ∃ t : C, IsUnit (θ t) ∧ t * c ∈ Ideal.span {z})
    [IsReduced L] :
    IsLocalization
      ((maximalIdeal L).comap (algebraMap (R ⧸ Ideal.span {a}) L)).primeCompl L := by
  set A := R ⧸ Ideal.span ({a} : Set R)
  set 𝔮 : Ideal A := (maximalIdeal L).comap (algebraMap A L) with h𝔮
  -- `θ z = 0`: `θ z` is nilpotent because `z^n ∈ (a)` and `θ a = 0`, and `L` is reduced.
  have hθz : θ z = 0 := by
    obtain ⟨n, hn⟩ := hz
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hn
    have : θ z ^ n = 0 := by
      rw [← map_pow, hw, map_mul, hIker _ haI, zero_mul]
    exact IsNilpotent.eq_zero ⟨n, this⟩
  -- Every element of `C` agrees with an element of `R` modulo `(z)`, hence under `θ`.
  have hlift : ∀ c : C, ∃ r : R, θ c = algebraMap A L (Ideal.Quotient.mk _ r) ∧
      c - algebraMap R C r ∈ Ideal.span {z} := by
    intro c
    obtain ⟨x, hx⟩ := hbij.2 (Ideal.Quotient.mk (Ideal.span {z}) c)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
    refine ⟨r, ?_, ?_⟩
    · obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hx
      have : c = algebraMap R C r - z * w := by rw [← hw]; ring
      rw [this, map_sub, map_mul, hθz, zero_mul, sub_zero, hcomp]
    · have := (Ideal.span {z}).neg_mem hx
      rwa [neg_sub] at this
  -- Units of `L` coming from `A` lie outside `𝔮`.
  have hunit : ∀ x : A, IsUnit (algebraMap A L x) → x ∈ 𝔮.primeCompl := by
    intro x hx hx𝔮
    have hx𝔮' : x ∈ 𝔮 := hx𝔮
    rw [h𝔮, Ideal.mem_comap] at hx𝔮'
    exact (IsLocalRing.notMem_maximalIdeal.mpr hx) hx𝔮' 
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    have hy' : y ∉ 𝔮 := hy
    exact IsLocalRing.notMem_maximalIdeal.mp (fun h => hy' (Ideal.mem_comap.mpr h))
  · intro x
    obtain ⟨c, s, hs, hx⟩ := hsurj x
    obtain ⟨rc, hrc, -⟩ := hlift c
    obtain ⟨rs, hrs, -⟩ := hlift s
    refine ⟨⟨Ideal.Quotient.mk _ rc, ⟨Ideal.Quotient.mk _ rs, hunit _ (hrs ▸ hs)⟩⟩, ?_⟩
    change x * algebraMap A L (Ideal.Quotient.mk _ rs) = algebraMap A L (Ideal.Quotient.mk _ rc)
    rw [← hrs, ← hrc]
    exact hx
  · intro x y hxy
    obtain ⟨r₁, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r₂, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h0 : θ (algebraMap R C (r₁ - r₂)) = 0 := by
      rw [hcomp, map_sub, map_sub, hxy, sub_self]
    obtain ⟨t, ht, htI⟩ := hker _ h0
    obtain ⟨t', ht', htz⟩ := hloc _ htI
    set v := t' * t with hv
    have hvu : IsUnit (θ v) := by rw [hv, map_mul]; exact ht'.mul ht
    obtain ⟨rv, hrv, hvz⟩ := hlift v
    -- `algebraMap rv * algebraMap (r₁ - r₂) ∈ (z)`.
    have hmem : algebraMap R C (rv * (r₁ - r₂)) ∈ Ideal.span {z} := by
      have h1 : v * algebraMap R C (r₁ - r₂) ∈ Ideal.span {z} := by
        rwa [hv, mul_assoc]
      have h2 : (v - algebraMap R C rv) * algebraMap R C (r₁ - r₂) ∈ Ideal.span {z} :=
        Ideal.mul_mem_right _ _ hvz
      have := (Ideal.span {z}).sub_mem h1 h2
      have heq : v * algebraMap R C (r₁ - r₂) - (v - algebraMap R C rv) * algebraMap R C (r₁ - r₂)
          = algebraMap R C (rv * (r₁ - r₂)) := by
        rw [map_mul]; ring
      rwa [heq] at this
    -- Hence `mk rv * (mk r₁ - mk r₂) = 0` in `A`, by injectivity of `R/(a) → C/(z)`.
    have hzero : (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) (rv * (r₁ - r₂))) = 0 := by
      apply hbij.1
      rw [Ideal.quotientMap_mk, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    refine ⟨⟨Ideal.Quotient.mk _ rv, hunit _ (hrv ▸ hvu)⟩, ?_⟩
    change Ideal.Quotient.mk _ rv * Ideal.Quotient.mk _ r₁
      = Ideal.Quotient.mk _ rv * Ideal.Quotient.mk _ r₂
    rw [← sub_eq_zero, ← mul_sub, ← map_sub, ← map_mul]
    exact hzero

/-- **Step 4 at a point, concluded.** Under the hypotheses of
`Pcf.Bounding.isLocalization_of_localStructure`, `L` is formally étale over `R/(a)`:
localizations are formally étale. -/
theorem formallyEtale_of_localStructure (a : R) (z : C) (θ : C →+* L) (I : Ideal C)
    [Algebra (R ⧸ Ideal.span {a}) L]
    (hcomp : ∀ r : R, θ (algebraMap R C r)
      = algebraMap (R ⧸ Ideal.span {a}) L (Ideal.Quotient.mk _ r))
    (ha : Ideal.span ({a} : Set R) ≤ (Ideal.span {z}).comap (algebraMap R C))
    (hbij : Function.Bijective (Ideal.quotientMap (Ideal.span {z}) (algebraMap R C) ha))
    (hz : ∃ n, z ^ n ∈ Ideal.span {algebraMap R C a})
    (haI : algebraMap R C a ∈ I) (hIker : ∀ c ∈ I, θ c = 0)
    (hsurj : ∀ x : L, ∃ c s : C, IsUnit (θ s) ∧ x * θ s = θ c)
    (hker : ∀ c : C, θ c = 0 → ∃ t : C, IsUnit (θ t) ∧ t * c ∈ I)
    (hloc : ∀ c ∈ I, ∃ t : C, IsUnit (θ t) ∧ t * c ∈ Ideal.span {z})
    [IsReduced L] :
    Algebra.FormallyEtale (R ⧸ Ideal.span {a}) L :=
  have := isLocalization_of_localStructure a z θ I hcomp ha hbij hz haI hIker hsurj hker hloc
  Algebra.FormallyEtale.of_isLocalization
    ((maximalIdeal L).comap (algebraMap (R ⧸ Ideal.span {a}) L)).primeCompl

end Pcf.Bounding
