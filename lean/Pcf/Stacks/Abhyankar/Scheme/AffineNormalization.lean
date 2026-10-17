/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.Algebra.Module.SpanRankOperations
public import Pcf.Stacks.Abhyankar.Scheme.Defs
public import Pcf.Stacks.Abhyankar.Scheme.IntegralClosureAway
public import Pcf.Stacks.Abhyankar.NormalizationBaseChange
public import Pcf.Stacks.Abhyankar.NormalizationGeometry

/-!
# The normalization in the affine situation of Stacks Tag `0EYH`

Setting: `R` Noetherian, `a ∈ R` a nonzerodivisor, `B` finite étale over `R_a` (the ring of the
cover `Y → X ∖ D` over an affine open `Spec R ⊂ X` with `D = V(a)`), and `N` the integral closure
of `R` in `B` (the ring of the normalization `Y'` over `Spec R`, Mathlib's
`Scheme.Hom.normalizationObjIso`).  The input `hloc` is the affine `0EYG` conclusion at every
point of `V(a)` (`HasLocalizedStandardCoverAt`).  The results are the affine forms of the clauses
of Stacks Lemma 58.31.6 (Tag `0EYH`).

## Stacks proof step → Lean

* "taking the normalization of `X` in `Y` commutes with étale base change (More on Morphisms,
  Lemma 37.19.2)" → `nonempty_baseChange_integralClosure_algEquiv`, through pcf's
  `smoothBaseChange_isIntegralClosure_localizationAway` (Tag `03GV`, affine form);
* "by Lemma 58.31.5 we may assume … `Y` is a finite disjoint union of `Spec(A_f[x]/(x^e - f))`"
  → the hypothesis `hloc` (`HasLocalizedStandardCoverAt`);
* "the integral closure of `A` in `A_f[x]/(x^e - f)` is `A[x]/(x^e - f)`" (omitted in Stacks)
  → pcf's `normalizationEquivStandardCoversOfLocalizedPresentation`, inside
  `nonempty_baseChange_integralClosure_algEquiv`;
* "we may prove the statements … étale locally on `X`":
  finite locally free → `integralClosure_finite`, `integralClosure_flat` (finite and flat over the
  Noetherian `R` is finite locally free, Tag `02KB`);
  `D' = π⁻¹(D)_red` effective Cartier → `exists_radical_eq_span_of_mem`;
  `D'` regular → `isRegularRing_quotient_radical`.

## Route notes (where the proofs are not the Stacks text)

Stacks leaves implicit that each clause descends from an étale cover.  Here each descent is an
explicit lemma: finiteness and flatness by faithfully flat descent over basic opens covered by
the open images of the stages (`finite_flat_away_of_cover`, Chevalley openness Tag `00I1`);
`rad(aN)` invertible by descent of invertible ideals along flat local maps
(`exists_eq_span_nonZeroDivisor_of_map_eq_span`, from the generator count
`spanFinrank_le_spanFinrank_map_of_faithfullyFlat`) and spreading out
(`exists_away_span_nonZeroDivisor_of_atPrime`); regularity by descent along étale local maps
(`isRegularLocalRing_of_flat_of_map_maximalIdeal`, the case of Tag `00OF` with `𝔪₀D₁ = 𝔪₁`).
The identification `rad(aN) ⊗_R A = rad(a (N ⊗_R A))` uses that étale algebras over reduced
Noetherian rings are reduced (`isReduced_of_etale`, case of Tag `033B`, proved via minimal primes
rather than Serre's criterion).  The regularity of `R/(a)` is not needed for these clauses (it
enters only through the stages supplied by `hloc`).
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

namespace Pcf.Stacks.SchemeLevel

set_option linter.style.haveILetI false

/-! ### Commutative-algebra descent lemmas -/

/-- **Étale over reduced is reduced** (Noetherian base; a special case of Stacks Tag `033B`).

Route: a nilpotent `x ∈ E` dies in `D_𝔭 ⊗_D E` for every minimal prime `𝔭` (that ring is étale
over the field `D_𝔭`, hence reduced by Mathlib's `isReduced_of_field`), so its annihilator in `D`
avoids every minimal prime; prime avoidance gives a nonzerodivisor `s` of `D` killing `x`, and `s`
stays regular on the flat `E`.  Stacks deduces `033B` from Serre's criterion instead. -/
@[stacks 033B "étale (hence smooth) over a reduced Noetherian ring; proof via minimal primes"]
theorem isReduced_of_etale (D E : Type*) [CommRing D] [CommRing E] [Algebra D E]
    [IsReduced D] [IsNoetherianRing D] [Algebra.Etale D E] : IsReduced E := by
  classical
  refine ⟨fun x hx => ?_⟩
  have key : ∀ p ∈ minimalPrimes D, ∃ s : D, s ∉ p ∧ algebraMap D E s * x = 0 := by
    intro p hp
    have : p.IsPrime := hp.1.1
    let Dp := Localization.AtPrime p
    have hfield : IsField Dp := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq,
        ← IsLocalization.AtPrime.map_eq_maximalIdeal p Dp,
        ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Dp) p ⊥ hp,
        Ideal.map_bot]
      have := nilradical_eq_zero Dp
      exact this
    letI : Field Dp := hfield.toField
    let E' := Dp ⊗[D] E
    letI : Algebra E E' := Algebra.TensorProduct.rightAlgebra
    have hloc : IsLocalization (Algebra.algebraMapSubmonoid E p.primeCompl) E' := inferInstance
    have hred : IsReduced E' := Algebra.FormallyUnramified.isReduced_of_field Dp E'
    have hx' : algebraMap E E' x = 0 := (hx.map (algebraMap E E')).eq_zero
    obtain ⟨⟨m, hm⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff
      (Algebra.algebraMapSubmonoid E p.primeCompl) E' x).mp hx'
    obtain ⟨s, hs, rfl⟩ := hm
    exact ⟨s, hs, hm'⟩
  let J : Ideal D := LinearMap.ker (LinearMap.toSpanSingleton D E x)
  have hJ : ∀ s, s ∈ J ↔ algebraMap D E s * x = 0 := fun s => by
    simp [J, Algebra.smul_def]
  have hfin := minimalPrimes.finite_of_isNoetherianRing D
  obtain ⟨s, hsJ, hsu⟩ : ∃ s ∈ J, s ∉ ⋃ p ∈ minimalPrimes D, (p : Set D) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite (f := id) hfin ⊥ ⊥
      (fun i hi _ _ => hi.1.1)).mp hcon
    obtain ⟨t, ht, ht'⟩ := key p hp
    exact ht (hle ((hJ t).mpr ht'))
  have hreg : IsSMulRegular D s := by
    intro y z hyz
    by_contra hne
    apply hsu
    have : s ∈ ⋃ p ∈ (⊥ : Ideal D).minimalPrimes, (p : Set D) := by
      rw [Ideal.iUnion_minimalPrimes]
      refine ⟨y - z, ?_, ?_⟩
      · intro h
        have h0 : y - z = 0 := by
          have := (nilradical_eq_zero D)
          change y - z ∈ nilradical D at h
          rw [this] at h
          exact h
        exact hne (sub_eq_zero.mp h0)
      · have : s * (y - z) = 0 := by
          simp only [smul_eq_mul] at hyz
          rw [mul_sub, hyz, sub_self]
        rw [this]
        exact Ideal.zero_mem _
    exact this
  have hregE : IsSMulRegular E (algebraMap D E s) := hreg.of_flat
  apply hregE
  simp only [smul_eq_mul, mul_zero]
  exact (hJ s).mp hsJ

/-- Along a faithfully flat map into a Noetherian local ring, an ideal needs no more generators
than its extension: a minimal generating set of `I D₁` can be extracted (Nakayama, over the
residue field of `D₁`) from the images of generators of `I`, and faithful flatness gives back `I`
from its extension. -/
theorem spanFinrank_le_spanFinrank_map_of_faithfullyFlat {D0 D1 : Type*} [CommRing D0]
    [CommRing D1] [Algebra D0 D1] [IsNoetherianRing D0] [IsLocalRing D1] [IsNoetherianRing D1]
    [Module.FaithfullyFlat D0 D1] (I : Ideal D0) :
    I.spanFinrank ≤ (I.map (algebraMap D0 D1)).spanFinrank := by
  classical
  letI : Field (D1 ⧸ maximalIdeal D1) := Ideal.Quotient.field _
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian I : I.FG)
  set φ := algebraMap D0 D1
  set J := I.map φ with hJdef
  have hJ : J = Ideal.span (φ '' (G : Set D0)) := by rw [hJdef, ← hG, Ideal.map_span]
  have hmemJ : ∀ g ∈ (G : Set D0), φ g ∈ J := fun g hg => hJ ▸ Ideal.subset_span ⟨g, hg, rfl⟩
  have hn : J.spanFinrank = Module.finrank (D1 ⧸ maximalIdeal D1)
      (J ⧸ (maximalIdeal D1 • (⊤ : Submodule D1 J))) :=
    IsLocalRing.spanFinrank_eq_finrank_quotient J (IsNoetherian.noetherian J)
  let w : G → J := fun g => ⟨φ g, hmemJ g g.2⟩
  let v : G → J ⧸ (maximalIdeal D1 • (⊤ : Submodule D1 J)) := fun g => Submodule.mkQ _ (w g)
  have hspanw : ∀ G' : Set G, Ideal.span (φ '' (Subtype.val '' G')) = J →
      Submodule.span D1 (w '' G') = ⊤ := by
    intro G' hG'
    apply Submodule.map_injective_of_injective (Submodule.injective_subtype J)
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.image_comp]
    have : (⇑J.subtype ∘ w) '' G' = φ '' (Subtype.val '' G') := by
      rw [← Set.image_comp]; rfl
    rw [this]; exact hG'
  have hspank : ∀ S : Set (J ⧸ (maximalIdeal D1 • (⊤ : Submodule D1 J))),
      (Submodule.span (D1 ⧸ maximalIdeal D1) S).restrictScalars D1 = Submodule.span D1 S :=
    fun S => Submodule.restrictScalars_span D1 _ Ideal.Quotient.mk_surjective S
  have hkey : ∀ G' : Set G, Submodule.span (D1 ⧸ maximalIdeal D1) (v '' G') = ⊤ →
      Ideal.span (φ '' (Subtype.val '' G')) = J := by
    intro G' hG'
    have h2 : Submodule.span D1 (v '' G') = ⊤ := by
      rw [← hspank, hG']; rfl
    have h3 : (Submodule.span D1 (w '' G')).map
        (Submodule.mkQ (maximalIdeal D1 • (⊤ : Submodule D1 J))) = ⊤ := by
      rw [Submodule.map_span, ← Set.image_comp]; exact h2
    rw [IsLocalRing.map_mkQ_eq_top] at h3
    have h4 := congrArg (Submodule.map J.subtype) h3
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.image_comp] at h4
    have : (⇑J.subtype ∘ w) '' G' = φ '' (Subtype.val '' G') := by
      rw [← Set.image_comp]; rfl
    rw [this] at h4; exact h4
  have htop : Submodule.span (D1 ⧸ maximalIdeal D1) (Set.range v) = ⊤ := by
    have h1 : Submodule.span D1 (w '' Set.univ) = ⊤ :=
      hspanw Set.univ (by rw [hJ]; congr 1; ext; simp)
    have h2 : Submodule.span D1 (Set.range v) = ⊤ := by
      rw [show Set.range v = (Submodule.mkQ _) '' (w '' Set.univ) by
        rw [Set.image_univ, ← Set.range_comp]; rfl, ← Submodule.map_span, h1, Submodule.map_top,
        Submodule.range_mkQ]
    apply Submodule.restrictScalars_injective D1
    rw [hspank, h2]
    rfl
  obtain ⟨t, ht_sub, ht_span, ht_li⟩ := exists_linearIndependent (D1 ⧸ maximalIdeal D1)
    (Set.range v)
  rw [htop] at ht_span
  have htfin : t.Finite := (Set.finite_range v).subset ht_sub
  haveI : Fintype t := htfin.fintype
  have hcard : Module.finrank (D1 ⧸ maximalIdeal D1)
      (J ⧸ (maximalIdeal D1 • (⊤ : Submodule D1 J))) = t.ncard := by
    rw [← finrank_top, ← ht_span, finrank_span_set_eq_card ht_li, Set.ncard_eq_toFinset_card']
  choose f hf using fun x : t => ht_sub x.2
  let G' : Set G := Set.range f
  have hvG' : t ⊆ v '' G' := fun x hx => ⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, hf ⟨x, hx⟩⟩
  have hspanG' : Submodule.span (D1 ⧸ maximalIdeal D1) (v '' G') = ⊤ :=
    eq_top_iff.mpr (ht_span ▸ Submodule.span_mono hvG')
  have hJ' := hkey G' hspanG'
  have hI' : Ideal.span (Subtype.val '' G') = I := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := D1) (Ideal.span _), Ideal.map_span,
      hJ', hJdef]
    exact Ideal.comap_map_eq_self_of_faithfullyFlat I
  have hfinG' : (Subtype.val '' G').Finite := (Set.finite_range f).image _
  calc I.spanFinrank = (Submodule.span D0 (Subtype.val '' G')).spanFinrank := by rw [← hI']
    _ ≤ (Subtype.val '' G').ncard := Submodule.spanFinrank_span_le_ncard_of_finite hfinG'
    _ ≤ G'.ncard := Set.ncard_image_le (Set.finite_range f)
    _ ≤ t.ncard := by
        change (Set.range f).ncard ≤ t.ncard
        rw [← Set.image_univ]
        refine (Set.ncard_image_le Set.finite_univ).trans ?_
        rw [Set.ncard_univ, Nat.card_coe_set_eq]
    _ = J.spanFinrank := by rw [hn, hcard]

/-- **Regularity descends along flat local maps with `𝔪₀ D₁ = 𝔪₁`** (the case of Stacks Tag
`00OF` used here: étale local maps).  `μ(𝔪₀) ≤ μ(𝔪₁) = dim D₁ ≤ dim D₀`, the last by the height
inequality `ht 𝔪₁ ≤ ht 𝔪₀ + ht(𝔪₁ / 𝔪₀D₁)` with the fibre a field. -/
@[stacks 00OF "case 𝔪₀D₁ = 𝔪₁ (e.g. étale local maps)"]
theorem isRegularLocalRing_of_flat_of_map_maximalIdeal (D0 D1 : Type*) [CommRing D0]
    [CommRing D1] [Algebra D0 D1] [IsLocalRing D0] [IsNoetherianRing D0]
    [IsRegularLocalRing D1] [IsLocalHom (algebraMap D0 D1)]
    [Module.Flat D0 D1]
    (hmax : (maximalIdeal D0).map (algebraMap D0 D1) = maximalIdeal D1) :
    IsRegularLocalRing D0 := by
  haveI : Module.FaithfullyFlat D0 D1 := Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h1 := spanFinrank_le_spanFinrank_map_of_faithfullyFlat (D1 := D1) (maximalIdeal D0)
  rw [hmax] at h1
  haveI hlo : (maximalIdeal D1).LiesOver (maximalIdeal D0) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap D0 D1)).symm⟩
  have hdim : ringKrullDim D1 ≤ ringKrullDim D0 := by
    rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]
    have h := Ideal.height_le_height_add_of_liesOver (maximalIdeal D0) (maximalIdeal D1)
    rw [hmax, Ideal.map_quotient_self] at h
    rw [Ideal.height_bot, add_zero] at h
    exact WithBot.coe_le_coe.mpr h
  calc ((maximalIdeal D0).spanFinrank : WithBot ℕ∞) ≤ (maximalIdeal D1).spanFinrank := by
        exact_mod_cast h1
    _ = ringKrullDim D1 := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ ringKrullDim D0 := hdim

/-- An ideal whose extension along a flat local map of Noetherian local rings is generated by one
nonzerodivisor is itself generated by one nonzerodivisor (faithfully flat descent of invertible
ideals, local form). -/
theorem exists_eq_span_nonZeroDivisor_of_map_eq_span {D0 D1 : Type*} [CommRing D0]
    [CommRing D1] [Algebra D0 D1] [IsLocalRing D0] [IsNoetherianRing D0] [IsLocalRing D1]
    [IsNoetherianRing D1] [IsLocalHom (algebraMap D0 D1)] [Module.Flat D0 D1]
    (I : Ideal D0) {t : D1} (ht : t ∈ nonZeroDivisors D1)
    (hI : I.map (algebraMap D0 D1) = Ideal.span {t}) :
    ∃ s ∈ nonZeroDivisors D0, I = Ideal.span {s} := by
  classical
  haveI : Module.FaithfullyFlat D0 D1 := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
  have hle := spanFinrank_le_spanFinrank_map_of_faithfullyFlat (D1 := D1) I
  rw [hI, Submodule.spanFinrank_singleton ht0] at hle
  obtain ⟨S, hScard, hS⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian I)
  rw [← hScard] at hle
  obtain ⟨x, rfl⟩ : ∃ x, S = {x} := by
    rcases Finset.card_le_one_iff_subset_singleton.mp hle with ⟨x, hx⟩
    rcases Finset.subset_singleton_iff.mp hx with h | h
    · exfalso
      subst h
      rw [Finset.coe_empty, Submodule.span_empty] at hS
      rw [← hS, Ideal.map_bot] at hI
      exact ht0 (Ideal.span_singleton_eq_bot.mp hI.symm)
    · exact ⟨x, h⟩
  rw [Finset.coe_singleton] at hS
  change Ideal.span {x} = I at hS
  refine ⟨x, ?_, hS.symm⟩
  rw [← hS, Ideal.map_span, Set.image_singleton] at hI
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hI ▸ Ideal.mem_span_singleton_self _ :
    algebraMap D0 D1 x ∈ Ideal.span {t})
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (hI.symm ▸ Ideal.mem_span_singleton_self _ :
    t ∈ Ideal.span {algebraMap D0 D1 x})
  have hdc : d * c = 1 := by
    have : (d * c - 1) * t = 0 := by rw [sub_mul, mul_assoc, hc, hd, one_mul, sub_self]
    have := (mem_nonZeroDivisors_iff_right.mp ht) _ this
    exact sub_eq_zero.mp this
  have hxnzd : algebraMap D0 D1 x ∈ nonZeroDivisors D1 := by
    rw [← hc]
    exact Submonoid.mul_mem _ ((isUnit_iff_exists_inv'.mpr ⟨d, hdc⟩).mem_nonZeroDivisors) ht
  have hinj := FaithfulSMul.algebraMap_injective D0 D1
  refine mem_nonZeroDivisors_iff_right.mpr fun r hr => hinj ?_
  rw [map_zero]
  exact (mem_nonZeroDivisors_iff_right.mp hxnzd) _ (by rw [← map_mul, hr, map_zero])

section EtaleAtPrime
variable {S T : Type*} [CommRing S] [CommRing T] [Algebra S T] [Algebra.Etale S T]
  [IsNoetherianRing S] (P : Ideal S) [P.IsPrime] (P' : Ideal T) [P'.IsPrime] [P'.LiesOver P]

include P' in
/-- Regularity descends from `T_{P'}` to `S_P` along an étale map. -/
theorem isRegularLocalRing_atPrime_of_etale
    (h : IsRegularLocalRing (Localization.AtPrime P')) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime P') :=
    Localization.AtPrime.algebraOfLiesOver P P'
  have : IsScalarTower S (Localization.AtPrime P) (Localization.AtPrime P') := inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime P')) := by
    rw [Localization.AtPrime.algebraMap_eq]; infer_instance
  have : Algebra.EssFiniteType (Localization.AtPrime P) (Localization.AtPrime P') :=
    Algebra.EssFiniteType.of_comp S _ _
  have : Algebra.FormallyUnramified S (Localization.AtPrime P') :=
    Algebra.FormallyUnramified.comp S T _
  have : Algebra.FormallyUnramified (Localization.AtPrime P) (Localization.AtPrime P') :=
    Algebra.FormallyUnramified.of_restrictScalars S _ _
  exact isRegularLocalRing_of_flat_of_map_maximalIdeal _ (Localization.AtPrime P')
    (Algebra.FormallyUnramified.map_maximalIdeal)

include P' in
/-- An ideal that becomes principal, generated by a nonzerodivisor, after an étale base change is
principal, generated by a nonzerodivisor, at every prime under a prime of the base change. -/
theorem exists_span_nonZeroDivisor_atPrime_of_etale (I : Ideal S) {t : T}
    (ht : t ∈ nonZeroDivisors T) (hI : I.map (algebraMap S T) = Ideal.span {t}) :
    ∃ s ∈ nonZeroDivisors (Localization.AtPrime P),
      I.map (algebraMap S (Localization.AtPrime P)) = Ideal.span {s} := by
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime P') :=
    Localization.AtPrime.algebraOfLiesOver P P'
  have : IsScalarTower S (Localization.AtPrime P) (Localization.AtPrime P') := inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime P')) := by
    rw [Localization.AtPrime.algebraMap_eq]; infer_instance
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing S T
  have ht' : algebraMap T (Localization.AtPrime P') t ∈
      nonZeroDivisors (Localization.AtPrime P') := by
    have hreg : IsSMulRegular T t := fun a b h => by
      have h' : (a - b) * t = 0 := by
        simp only [smul_eq_mul] at h
        rw [sub_mul, mul_comm a, mul_comm b, h, sub_self]
      exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp ht) _ h')
    have := hreg.of_isLocalization (Localization.AtPrime P') P'.primeCompl
    refine mem_nonZeroDivisors_iff_right.mpr fun y hy => this ?_
    simp only [smul_eq_mul, mul_zero]
    rw [mul_comm]; exact hy
  apply exists_eq_span_nonZeroDivisor_of_map_eq_span _ ht'
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    IsScalarTower.algebraMap_eq S T (Localization.AtPrime P'), ← Ideal.map_map, hI,
    Ideal.map_span, Set.image_singleton]

end EtaleAtPrime

/-- Faithfully flat descent of finiteness and flatness over a basic open: if `C` is flat over `R`,
every prime of `D(g)` lies under a prime of `C`, and `C ⊗_R M` is finite and flat over `C`, then
`R_g ⊗_R M` is finite and flat over `R_g` (descend along `R_g → R_g ⊗_R C`). -/
theorem finite_flat_away_of_cover {R M C : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing C] [Algebra R C] [Module.Flat R C] (g : R)
    (hsurj : ∀ p : Ideal R, p.IsPrime → g ∉ p →
      ∃ q : Ideal C, q.IsPrime ∧ q.comap (algebraMap R C) = p)
    (hfin : Module.Finite C (C ⊗[R] M)) (hflat : Module.Flat C (C ⊗[R] M)) :
    Module.Finite (Localization.Away g) (Localization.Away g ⊗[R] M) ∧
      Module.Flat (Localization.Away g) (Localization.Away g ⊗[R] M) := by
  let Rg := Localization.Away g
  let T := Rg ⊗[R] C
  letI : Algebra C T := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers g)) T :=
    inferInstance
  have htow : ∀ r : R, algebraMap C T (algebraMap R C r) = algebraMap R T r := fun r =>
    (IsScalarTower.algebraMap_apply R C T r).symm
  -- faithful flatness of `Rg → T`
  have hff : Module.FaithfullyFlat Rg T := by
    refine Module.FaithfullyFlat.of_comap_surjective ?_
    intro P
    let p := P.asIdeal.comap (algebraMap R Rg)
    have hgp : g ∉ p := fun h =>
      P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit g))
    obtain ⟨q, hq, hqp⟩ := hsurj p inferInstance hgp
    have hdisj : Disjoint (Algebra.algebraMapSubmonoid C (Submonoid.powers g) : Set C) q := by
      rw [Set.disjoint_left]
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩ hmem
      apply hgp
      have : algebraMap R C (g ^ n) ∈ q := hmem
      rw [← Ideal.mem_comap, hqp] at this
      exact (inferInstance : p.IsPrime).mem_of_pow_mem n this
    let Q : Ideal T := q.map (algebraMap C T)
    have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ T q hq hdisj
    refine ⟨⟨Q, hQ⟩, ?_⟩
    ext1
    change Q.comap (algebraMap Rg T) = P.asIdeal
    have hR : (Q.comap (algebraMap Rg T)).under R = p := by
      change (Q.comap (algebraMap Rg T)).comap (algebraMap R Rg) = p
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R C T,
        ← Ideal.comap_comap]
      change (Q.under C).comap (algebraMap R C) = p
      rw [IsLocalization.under_map_of_isPrime_disjoint _ T hq hdisj, hqp]
    rw [← IsLocalization.map_under (Submonoid.powers g) Rg (Q.comap (algebraMap Rg T)), hR]
    exact IsLocalization.map_under (Submonoid.powers g) Rg P.asIdeal
  -- the base change of `Rg ⊗ M` to `T`
  let e1 : T ⊗[Rg] (Rg ⊗[R] M) ≃ₗ[T] T ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R Rg T T M
  let e2 : T ⊗[C] (C ⊗[R] M) ≃ₗ[T] T ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R C T T M
  have hfinT : Module.Finite T (T ⊗[Rg] (Rg ⊗[R] M)) :=
    Module.Finite.equiv (e2.trans e1.symm)
  have hflatT : Module.Flat T (T ⊗[Rg] (Rg ⊗[R] M)) :=
    Module.Flat.of_linearEquiv (e2.trans e1.symm).symm
  exact ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat T,
    Module.Flat.of_flat_tensorProduct Rg (Rg ⊗[R] M) T⟩

/-- A prime of `S` and a prime of `A` over the same prime of `R` are both under a prime of
`S ⊗[R] A` (surjectivity of `Spec(S ⊗_R A) → Spec S ×_{Spec R} Spec A` onto points). -/
theorem exists_isPrime_tensorProduct_comap_eq {R S A : Type*} [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra R A] (Q : Ideal S) [Q.IsPrime] (y' : Ideal A)
    [y'.IsPrime] (h : Q.comap (algebraMap R S) = y'.comap (algebraMap R A)) :
    ∃ Q' : Ideal (S ⊗[R] A), Q'.IsPrime ∧ Q'.comap (algebraMap S (S ⊗[R] A)) = Q := by
  let p := Q.comap (algebraMap R S)
  let k := p.ResidueField
  let K := Q.ResidueField
  let L := y'.ResidueField
  letI : Algebra k K := (Ideal.ResidueField.map p Q (algebraMap R S) rfl).toAlgebra
  letI : Algebra k L := (Ideal.ResidueField.map p y' (algebraMap R A) h).toAlgebra
  let F := K ⊗[k] L
  letI : Algebra R F := ((algebraMap k F).comp (algebraMap R k)).toAlgebra
  let f : S →ₐ[R] F :=
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom).comp (algebraMap S K)
      commutes' := fun r => by
        change (algebraMap S K (algebraMap R S r)) ⊗ₜ[k] (1 : L) =
          algebraMap k F (algebraMap R k r)
        rw [Algebra.TensorProduct.algebraMap_apply]
        congr 1
        exact (Ideal.ResidueField.map_algebraMap p Q (algebraMap R S) rfl r).symm }
  let g : A →ₐ[R] F :=
    { toRingHom := (Algebra.TensorProduct.includeRight : L →ₐ[k] F).toRingHom.comp
        (algebraMap A L)
      commutes' := fun r => by
        change (1 : K) ⊗ₜ[k] (algebraMap A L (algebraMap R A r)) =
          algebraMap k F (algebraMap R k r)
        rw [← Ideal.ResidueField.map_algebraMap p y' (algebraMap R A) h r]
        exact (Algebra.TensorProduct.algebraMap_apply' _).symm }
  let ψ := Algebra.TensorProduct.productMap f g
  obtain ⟨M, hM⟩ := Ideal.exists_maximal F
  refine ⟨M.comap ψ.toRingHom, Ideal.comap_isPrime _ _, ?_⟩
  have hcomp : (ψ.toRingHom).comp (algebraMap S (S ⊗[R] A)) =
      (Algebra.TensorProduct.includeLeftRingHom).comp (algebraMap S K) := by
    ext s
    simp [ψ, f, Algebra.TensorProduct.algebraMap_apply]
  rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap]
  have hbot : M.comap (Algebra.TensorProduct.includeLeftRingHom : K →+* F) = ⊥ :=
    ((Ideal.eq_bot_or_top _).resolve_right (Ideal.comap_ne_top _ hM.ne_top))
  rw [hbot, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

/-- Spreading out: if an ideal becomes principal, generated by a nonzerodivisor, at a prime `Q` of
a Noetherian ring, then it is so on a basic open neighbourhood `D(h)` of `Q`. -/
theorem exists_away_span_nonZeroDivisor_of_atPrime {N : Type*} [CommRing N] [IsNoetherianRing N]
    (Q : Ideal N) [Q.IsPrime] (I : Ideal N) {s : Localization.AtPrime Q}
    (hs : s ∈ nonZeroDivisors (Localization.AtPrime Q))
    (hIs : I.map (algebraMap N (Localization.AtPrime Q)) = Ideal.span {s}) :
    ∃ h : N, h ∉ Q ∧ ∃ n ∈ I, ∀ (Nh : Type*) [CommRing Nh] [Algebra N Nh]
      [IsLocalization.Away h Nh],
        algebraMap N Nh n ∈ nonZeroDivisors Nh ∧
          I.map (algebraMap N Nh) = Ideal.span {algebraMap N Nh n} := by
  classical
  let NQ := Localization.AtPrime Q
  have hsI : s ∈ I.map (algebraMap N NQ) := by rw [hIs]; exact Ideal.mem_span_singleton_self s
  -- a generator coming from `I`
  obtain ⟨⟨⟨n, hnI⟩, d⟩, hnd⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl NQ).mp hsI
  simp only at hnd
  have hdu : IsUnit (algebraMap N NQ d) := IsLocalization.map_units NQ d
  have hn_span : I.map (algebraMap N NQ) = Ideal.span {algebraMap N NQ n} := by
    rw [hIs, ← hnd, Ideal.span_singleton_mul_right_unit hdu]
  have hn_nzd : algebraMap N NQ n ∈ nonZeroDivisors NQ := by
    rw [← hnd]; exact Submonoid.mul_mem _ hs hdu.mem_nonZeroDivisors
  -- generators of `I` are multiples of `n` up to elements outside `Q`
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian I : I.FG)
  have hgen : ∀ g ∈ G, ∃ w : N, w ∉ Q ∧ ∃ c : N, w * g = c * n := by
    intro g hg
    have hgI : algebraMap N NQ g ∈ Ideal.span {algebraMap N NQ n} := by
      rw [← hn_span]; exact Ideal.mem_map_of_mem _ (hG ▸ Submodule.subset_span hg)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hgI
    obtain ⟨⟨x, dd⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl c
    simp only at hc
    have : algebraMap N NQ (x * n) = algebraMap N NQ (dd * g) := by
      rw [map_mul, map_mul, ← hc, ← mul_assoc, mul_comm (algebraMap N NQ dd),
        IsLocalization.mk'_spec]
    obtain ⟨e, he⟩ := (IsLocalization.eq_iff_exists Q.primeCompl NQ).mp this
    refine ⟨e * dd, ?_, e * x, ?_⟩
    · exact Q.primeCompl.mul_mem e.2 dd.2
    · linear_combination he.symm
  choose! w hwQ c hwc using hgen
  -- the annihilator of `n` dies outside `Q`
  let K : Ideal N := LinearMap.ker (LinearMap.toSpanSingleton N N n)
  obtain ⟨H, hH⟩ := (IsNoetherian.noetherian K : K.FG)
  have hann : ∀ z ∈ H, ∃ f : N, f ∉ Q ∧ f * z = 0 := by
    intro z hz
    have hzK : z ∈ K := hH ▸ Submodule.subset_span hz
    have hzn : z * n = 0 := by simpa [K] using hzK
    have : algebraMap N NQ z = 0 :=
      (mem_nonZeroDivisors_iff_right.mp hn_nzd) _ (by rw [← map_mul, hzn, map_zero])
    obtain ⟨⟨f, hf⟩, hfz⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl NQ z).mp this
    exact ⟨f, hf, hfz⟩
  choose! f hfQ hfz using hann
  let W := ∏ g ∈ G, w g
  let F := ∏ z ∈ H, f z
  have hWQ : W ∉ Q := fun h => by
    obtain ⟨g, hg, hgQ⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hwQ g hg hgQ
  have hFQ : F ∉ Q := fun h => by
    obtain ⟨z, hz, hzQ⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hfQ z hz hzQ
  have hFK : ∀ k ∈ K, F * k = 0 := by
    intro k hk
    rw [← hH] at hk
    induction hk using Submodule.span_induction with
    | mem x hx =>
      rw [show F = (∏ z ∈ H.erase x, f z) * f x from (Finset.prod_erase_mul _ _ hx).symm,
        mul_assoc, hfz x hx, mul_zero]
    | zero => exact mul_zero _
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  refine ⟨W * F, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hWQ hFQ, n, hnI, ?_⟩
  intro Nh _ _ _
  have hu : IsUnit (algebraMap N Nh (W * F)) := IsLocalization.Away.algebraMap_isUnit _
  have hWu : IsUnit (algebraMap N Nh W) := by
    rw [map_mul] at hu; exact isUnit_of_mul_isUnit_left hu
  have hFu : IsUnit (algebraMap N Nh F) := by
    rw [map_mul] at hu; exact isUnit_of_mul_isUnit_right hu
  have hwu : ∀ g ∈ G, IsUnit (algebraMap N Nh (w g)) := by
    intro g hg
    have : W = (∏ x ∈ G.erase g, w x) * w g := (Finset.prod_erase_mul _ _ hg).symm
    rw [this, map_mul] at hWu
    exact isUnit_of_mul_isUnit_right hWu
  constructor
  · refine mem_nonZeroDivisors_iff_right.mpr fun y hy => ?_
    obtain ⟨⟨z, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (W * F)) y
    simp only at hy ⊢
    have hz : algebraMap N Nh (z * n) = 0 := by
      have := congrArg (· * algebraMap N Nh ((W * F) ^ k)) hy
      simp only [zero_mul] at this
      rw [mul_right_comm, IsLocalization.mk'_spec] at this
      rw [map_mul]; exact this
    obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (W * F)) Nh _).mp hz
    have hmK : (W * F) ^ m * z ∈ K := by
      change ((W * F) ^ m * z) • n = 0
      rw [smul_eq_mul, mul_assoc]; exact hm
    have h0 := hFK _ hmK
    have hz0 : algebraMap N Nh z = 0 := by
      have h1 := congrArg (algebraMap N Nh) h0
      rw [map_zero, map_mul, map_mul, map_pow, ← mul_assoc] at h1
      exact (hFu.mul (hu.pow m)).mul_right_eq_zero.mp h1
    obtain ⟨m', hm'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (W * F)) Nh z).mp hz0
    exact (IsLocalization.mk'_eq_zero_iff z _).mpr ⟨m', hm'⟩
  · apply le_antisymm
    · rw [← hG, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨v, hv⟩ := hwu g hg
      refine Ideal.mem_span_singleton'.mpr ⟨(↑v⁻¹ : Nh) * algebraMap N Nh (c g), ?_⟩
      have := congrArg (algebraMap N Nh) (hwc g hg)
      rw [map_mul, map_mul, ← hv] at this
      rw [mul_assoc, ← this, ← mul_assoc, Units.inv_mul, one_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hnI

/-- In a finite product, the product of principal ideals is principal. -/
theorem pi_span_singleton_eq {ι : Type} [Finite ι] {A : ι → Type u} [∀ i, CommRing (A i)]
    (x : ∀ i, A i) : Ideal.pi (fun i => Ideal.span {x i}) = Ideal.span {x} := by
  classical
  apply le_antisymm
  · intro f hf
    have : ∀ i, ∃ c, c * x i = f i := fun i => Ideal.mem_span_singleton'.mp (hf i)
    choose c hc using this
    exact Ideal.mem_span_singleton'.mpr ⟨c, funext fun i => hc i⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    intro i
    exact Ideal.mem_span_singleton_self _

/-- A family of nonzerodivisors is a nonzerodivisor of the product. -/
theorem pi_mem_nonZeroDivisors {ι : Type} {A : ι → Type u} [∀ i, CommRing (A i)]
    (x : ∀ i, A i) (hx : ∀ i, x i ∈ nonZeroDivisors (A i)) :
    x ∈ nonZeroDivisors (∀ i, A i) :=
  mem_nonZeroDivisors_iff_right.mpr fun _ hy =>
    funext fun i => (mem_nonZeroDivisors_iff_right.mp (hx i)) _ (congrFun hy i)

/-! ### The affine `0EYH` setting -/

section Normalization

variable {R : Type u} [CommRing R] (a : R)
    (Ra : Type u) [CommRing Ra] [Algebra R Ra] [IsLocalization.Away a Ra]
    (B : Type u) [CommRing B] [Algebra Ra B] [Algebra R B] [IsScalarTower R Ra B]
    [Module.Finite Ra B]

include Ra in
/-- **Normalization commutes with étale base change, and the normalization of a standard tame
cover is `∏ A[x]/(x^{e_i} - u_i a)`** (the two steps of the proof of Stacks Tag `0EYH`: More on
Morphisms, Lemma 37.19.2, and the omitted computation "the integral closure of `A` in
`A_f[x]/(x^e - f)` is `A[x]/(x^e - f)`").  Given a stage `A` of the local structure of `B`, the
base change `A ⊗_R N` of the normalization `N` is the product of standard root covers.  Uses pcf's
`smoothBaseChange_isIntegralClosure_localizationAway` (Tag `03GV`, affine) and
`normalizationEquivStandardCoversOfLocalizedPresentation`. -/
theorem nonempty_baseChange_integralClosure_algEquiv {A : Type u} [CommRing A] [Algebra R A]
    [Algebra.Etale R A]
    [IsNoetherianRing A] (hA : algebraMap R A a ∈ nonZeroDivisors A)
    [IsRegularRing (A ⧸ Ideal.span {algebraMap R A a})] {n : ℕ} (e : Fin n → ℕ) (u : Fin n → Aˣ)
    (he : ∀ i, 1 ≤ e i)
    (g : A ⊗[R] B ≃ₐ[A] ∀ i, AdjoinRoot (localizedStandardPoly (u i) (algebraMap R A a) (e i))) :
    Nonempty (A ⊗[R] integralClosure R B ≃ₐ[A]
      ∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (u i) (algebraMap R A a) (e i))) := by
  let N := integralClosure R B
  have : IsLocalization.Away (algebraMap R N a) B := isLocalization_away_integralClosure a Ra B
  have : IsIntegralClosure N R (Localization.Away (algebraMap R N a)) :=
    isIntegralClosure_localizationAway_integralClosure a Ra B
  have hIC : IsIntegralClosure (A ⊗[R] N) A
      (Localization.Away (algebraMap A (A ⊗[R] N) (algebraMap R A a))) :=
    smoothBaseChange_isIntegralClosure_localizationAway (R := R) (R' := A) (S := N) a
  let F : A ⊗[R] B ≃ₐ[A] Localization.Away ((1 : A) ⊗ₜ[R] algebraMap R N a) :=
    IsLocalization.Away.tensorProductEquivTMulRight R A (algebraMap R N a) B
  have hbase : (1 : A) ⊗ₜ[R] algebraMap R N a =
      algebraMap A (A ⊗[R] N) (algebraMap R A a) :=
    (Algebra.TensorProduct.tmul_one_eq_one_tmul a).symm
  let G : Localization.Away (algebraMap A (A ⊗[R] N) (algebraMap R A a)) ≃ₐ[A]
      ∀ i, AdjoinRoot (localizedStandardPoly (u i) (algebraMap R A a) (e i)) := by
    rw [← hbase]
    exact F.symm.trans g
  exact ⟨normalizationEquivStandardCoversOfLocalizedPresentation u (algebraMap R A a) e he hA G⟩

/-- On `D(a)` the normalization is `B`: `R_a ⊗_R N ≅ B` as `R_a`-modules. -/
noncomputable def awayTensorIntegralClosureEquiv [Algebra.IsIntegral Ra B] :
    Ra ⊗[R] integralClosure R B ≃ₗ[Ra] B := by
  let N := integralClosure R B
  have hloc : IsLocalization.Away (algebraMap R N a) B := isLocalization_away_integralClosure a Ra B
  have hlm : IsLocalizedModule (Submonoid.powers a)
      (IsScalarTower.toAlgHom R N B).toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid_powers]
    exact hloc
  exact ((isLocalizedModule_iff_isBaseChange (Submonoid.powers a) Ra _).mp hlm).equiv

variable [Algebra.Etale Ra B]

include Ra in
/-- Every point of `Spec R` has a basic open neighbourhood `D(g)` over which the normalization
`N` becomes finite and flat after localization. -/
theorem exists_away_finite_flat_integralClosure (_ha : a ∈ nonZeroDivisors R)
    (hloc : ∀ y : PrimeSpectrum R, a ∈ y.asIdeal → HasLocalizedStandardCoverAt a B y)
    (p : PrimeSpectrum R) :
    ∃ g : R, g ∉ p.asIdeal ∧
      Module.Finite (Localization.Away g) (Localization.Away g ⊗[R] integralClosure R B) ∧
      Module.Flat (Localization.Away g) (Localization.Away g ⊗[R] integralClosure R B) := by
  by_cases hap : a ∈ p.asIdeal
  · obtain ⟨A, _, _, hAet, ⟨y', hy'⟩, hAN, hAa, hAreg, n, e, u, he, heu, ⟨g⟩⟩ := hloc p hap
    obtain ⟨E⟩ := nonempty_baseChange_integralClosure_algEquiv a Ra B hAa e u he g
    have hfinC := standardCovers_finite u (algebraMap R A a) e he
    have hfreeC := standardCovers_free u (algebraMap R A a) e he
    have hfin : Module.Finite A (A ⊗[R] integralClosure R B) :=
      Module.Finite.equiv E.symm.toLinearEquiv
    have hfree : Module.Free A (A ⊗[R] integralClosure R B) :=
      Module.Free.of_equiv E.symm.toLinearEquiv
    have hopen : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap R A))) := by
      rw [← Set.image_univ]
      exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation _ isOpen_univ
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R A)) :=
      ⟨y', PrimeSpectrum.ext hy'⟩
    obtain ⟨_, ⟨g0, rfl⟩, hpg, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hopen
    refine ⟨g0, hpg, finite_flat_away_of_cover (C := A) g0 ?_ hfin inferInstance⟩
    intro q hq hgq
    obtain ⟨q', hq'⟩ := hsub (show (⟨q, hq⟩ : PrimeSpectrum R) ∈
      (PrimeSpectrum.basicOpen g0 : Set (PrimeSpectrum R)) from hgq)
    exact ⟨q'.asIdeal, q'.isPrime, congrArg PrimeSpectrum.asIdeal hq'⟩
  · have : Module.Flat R Ra := IsLocalization.flat Ra (Submonoid.powers a)
    refine ⟨a, hap, finite_flat_away_of_cover (C := Ra) a ?_ ?_ ?_⟩
    · intro q hq haq
      have hdisj : Disjoint (Submonoid.powers a : Set R) q := by
        rw [Set.disjoint_left]
        rintro _ ⟨n, rfl⟩ hmem
        exact haq (hq.mem_of_pow_mem n hmem)
      exact ⟨q.map (algebraMap R Ra), IsLocalization.isPrime_of_isPrime_disjoint _ Ra q hq hdisj,
        IsLocalization.under_map_of_isPrime_disjoint _ Ra hq hdisj⟩
    · exact Module.Finite.equiv (awayTensorIntegralClosureEquiv a Ra B).symm
    · exact Module.Flat.of_linearEquiv (awayTensorIntegralClosureEquiv a Ra B)

include Ra in
/-- The normalization `N` of `R` in `B` is finite and flat over `R`.

Route (differs from Stacks, which proves this étale locally and invokes descent of finite locally
free morphisms): over `D(a)` the normalization is `B`; near a point of `V(a)` a stage `A` of the
local structure has `A ⊗_R N` finite free; the image of `Spec A` is open (Chevalley, Tag `00I1`),
so finitely many basic opens `D(g)` carry finite flat localizations `N_g` by faithfully flat
descent (`finite_flat_away_of_cover`), and finiteness and flatness are local on `Spec R`. -/
theorem integralClosure_finite_and_flat (ha : a ∈ nonZeroDivisors R)
    (hloc : ∀ y : PrimeSpectrum R, a ∈ y.asIdeal → HasLocalizedStandardCoverAt a B y) :
    Module.Finite R (integralClosure R B) ∧ Module.Flat R (integralClosure R B) := by
  classical
  choose g hg hfin hflat using exists_away_finite_flat_integralClosure a Ra B ha hloc
  let t : Set R := Set.range g
  have ht : Ideal.span t = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hg ⟨M, hM.isPrime⟩ (hle (Ideal.subset_span ⟨⟨M, hM.isPrime⟩, rfl⟩))
  let N := integralClosure R B
  have hbc : ∀ x : t, IsLocalizedModule (Submonoid.powers x.1)
      (TensorProduct.mk R (Localization.Away x.1) N 1) := fun x =>
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers x.1) (Localization.Away x.1) _).mpr
      (TensorProduct.isBaseChange R N (Localization.Away x.1))
  have hfin' : ∀ x : t, Module.Finite (Localization.Away x.1) (Localization.Away x.1 ⊗[R] N) := by
    rintro ⟨_, p, rfl⟩; exact hfin p
  have hflat' : ∀ x : t, Module.Flat R (Localization.Away x.1 ⊗[R] N) := by
    rintro ⟨_, p, rfl⟩
    have := hflat p
    exact Module.Flat.trans R (Localization.Away (g p)) _
  constructor
  · exact Module.Finite.of_localizationSpan' t ht
      (Rₚ := fun x : t => Localization.Away x.1)
      (fun x => TensorProduct.mk R (Localization.Away x.1) N 1) hfin'
  · exact Module.flat_of_isLocalized_span R N t ht
      (fun x : t => Localization.Away x.1 ⊗[R] N)
      (fun x => TensorProduct.mk R (Localization.Away x.1) N 1) hflat'

include Ra in
/-- **The normalization is finite** (finiteness part of the first assertion of Stacks Tag `0EYH`,
affine form). -/
@[stacks 0EYH "finiteness part of the first assertion, affine form, from the étale-local standard \
  structure"]
theorem integralClosure_finite (ha : a ∈ nonZeroDivisors R)
    (hloc : ∀ y : PrimeSpectrum R, a ∈ y.asIdeal → HasLocalizedStandardCoverAt a B y) :
    Module.Finite R (integralClosure R B) :=
  (integralClosure_finite_and_flat a Ra B ha hloc).1

include Ra in
/-- **The normalization is flat**; with finiteness over the Noetherian `R`, finite locally free
(Stacks Tag `02KB`), the first assertion of Tag `0EYH` in affine form. -/
@[stacks 0EYH "first assertion (flat; finite locally free with 02KB), affine form, from the \
  étale-local standard structure"]
theorem integralClosure_flat (ha : a ∈ nonZeroDivisors R)
    (hloc : ∀ y : PrimeSpectrum R, a ∈ y.asIdeal → HasLocalizedStandardCoverAt a B y) :
    Module.Flat R (integralClosure R B) :=
  (integralClosure_finite_and_flat a Ra B ha hloc).2

omit [Algebra.Etale Ra B] in
include Ra in
/-- At a stage of the étale-local structure, the radical `rad(aN)` of the divisor on the
normalization becomes principal, generated by a nonzerodivisor, and the reduced divisor
becomes regular. -/
theorem isRegularRing_reducedDivisor_of_standardCoverEquiv [IsNoetherianRing (integralClosure R B)]
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.Etale R A]
    [IsNoetherianRing A] (hA : algebraMap R A a ∈ nonZeroDivisors A)
    [IsRegularRing (A ⧸ Ideal.span {algebraMap R A a})] {n : ℕ} (e : Fin n → ℕ) (u : Fin n → Aˣ)
    (he : ∀ i, 1 ≤ e i)
    (g : A ⊗[R] B ≃ₐ[A] ∀ i, AdjoinRoot (localizedStandardPoly (u i) (algebraMap R A a) (e i))) :
    ∃ t : integralClosure R B ⊗[R] A, t ∈ nonZeroDivisors _ ∧
      ((Ideal.span {algebraMap R (integralClosure R B) a}).radical).map
          (algebraMap (integralClosure R B) (integralClosure R B ⊗[R] A)) = Ideal.span {t} ∧
      IsRegularRing ((integralClosure R B ⧸
        (Ideal.span {algebraMap R (integralClosure R B) a}).radical) ⊗[R] A) := by
  let N := integralClosure R B
  let I : Ideal N := (Ideal.span {algebraMap R N a}).radical
  let N' := N ⊗[R] A
  let C := ∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (u i) (algebraMap R A a) (e i))
  obtain ⟨E⟩ := nonempty_baseChange_integralClosure_algEquiv a Ra B hA e u he g
  let φ : N' ≃+* C := (Algebra.TensorProduct.comm R N A).toRingEquiv.trans E.toRingEquiv
  have hφa : φ (algebraMap R N' a) = algebraMap A C (algebraMap R A a) := by
    change E (Algebra.TensorProduct.comm R N A (algebraMap R N' a)) = _
    rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply R A (A ⊗[R] N), E.commutes]
  -- `I N'` is radical, hence equal to `rad(a N')`
  have hIred : IsReduced (N ⧸ I) :=
    (Ideal.isRadical_iff_quotient_reduced I).mp (Ideal.radical_isRadical _)
  have : Algebra.Etale (N ⧸ I) ((N ⧸ I) ⊗[R] A) := inferInstance
  have hTred : IsReduced ((N ⧸ I) ⊗[R] A) := isReduced_of_etale (N ⧸ I) ((N ⧸ I) ⊗[R] A)
  let qe := Algebra.TensorProduct.quotientTensorEquiv (R := R) R A N I
  have hrad : (I.map (algebraMap N N')).IsRadical := by
    rw [Ideal.isRadical_iff_quotient_reduced]
    exact isReduced_of_injective qe.symm.toRingEquiv.toRingHom qe.symm.injective
  have hspanN' : (Ideal.span {algebraMap R N a}).map (algebraMap N N') =
      Ideal.span {algebraMap R N' a} := by
    rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply]
  have hK : I.map (algebraMap N N') = (Ideal.span {algebraMap R N' a}).radical := by
    apply le_antisymm
    · rw [← hspanN']; exact Ideal.map_radical_le (algebraMap N N')
    · rw [← hrad.radical]
      apply Ideal.radical_mono
      rw [← hspanN']
      exact Ideal.map_mono Ideal.le_radical
  -- transport to the standard covers
  have hred : IsReduced (A ⧸ Ideal.span ({algebraMap R A a} : Set A)) :=
    isReduced_of_isRegularRing
  have hC : (Ideal.span {algebraMap R N' a}).radical.map φ.toRingHom =
      Ideal.span {fun i =>
        AdjoinRoot.root (Pcf.LocalModel.localPoly (u i) (algebraMap R A a) (e i))} := by
    have hk : RingHom.ker φ.toRingHom = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp φ.injective
    rw [Ideal.map_radical_of_surjective φ.surjective (by rw [hk]; exact bot_le),
      Ideal.map_span, Set.image_singleton]
    change (Ideal.span {φ (algebraMap R N' a)}).radical = _
    rw [hφa, standardCovers_radical_span_algebraMap_eq_reducedDivisorIdeal u _ e he,
      standardCoversReducedDivisorIdeal, pi_span_singleton_eq]
  let r : C := fun i => AdjoinRoot.root (Pcf.LocalModel.localPoly (u i) (algebraMap R A a) (e i))
  have hr : r ∈ nonZeroDivisors C := pi_mem_nonZeroDivisors r fun i =>
    Pcf.LocalModel.root_mem_nonZeroDivisors (u i) (algebraMap R A a) (he i) hA
  refine ⟨φ.symm r, ?_, ?_, ?_⟩
  · refine mem_nonZeroDivisors_iff_right.mpr fun y hy => φ.injective ?_
    rw [map_zero]
    have := congrArg φ hy
    rw [map_mul, RingEquiv.apply_symm_apply, map_zero] at this
    exact (mem_nonZeroDivisors_iff_right.mp hr) _ this
  · rw [hK]
    have := congrArg (Ideal.map φ.symm.toRingHom) hC
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton] at this
    simpa using this
  · let qe2 : (N' ⧸ I.map (algebraMap N N')) ≃+* (C ⧸ standardCoversReducedDivisorIdeal u
        (algebraMap R A a) e) :=
      Ideal.quotientEquiv _ _ φ (by
        rw [standardCoversReducedDivisorIdeal, pi_span_singleton_eq, ← hC, hK]; rfl)
    have : IsRegularRing (C ⧸ standardCoversReducedDivisorIdeal u (algebraMap R A a) e) :=
      standardCoversReducedDivisor_isRegularRing u _ e he
    exact IsRegularRing.of_ringEquiv (qe.toRingEquiv.trans qe2).symm

end Normalization

section Divisor

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (a : R)
    (Ra : Type u) [CommRing Ra] [Algebra R Ra] [IsLocalization.Away a Ra]
    (B : Type u) [CommRing B] [Algebra Ra B] [Algebra R B] [IsScalarTower R Ra B]
    [Module.Finite Ra B] [Algebra.Etale Ra B]

include Ra in
/-- **The reduced inverse image of the divisor on the normalization is regular** (third
assertion of Stacks Tag `0EYH`, affine form). -/
@[stacks 0EYH "third assertion (D' regular), affine form"]
theorem isRegularRing_quotient_radical (ha : a ∈ nonZeroDivisors R)
    (hloc : ∀ y : PrimeSpectrum R, a ∈ y.asIdeal → HasLocalizedStandardCoverAt a B y) :
    IsRegularRing (integralClosure R B ⧸
      (Ideal.span {algebraMap R (integralClosure R B) a}).radical) := by
  let N := integralClosure R B
  let I : Ideal N := (Ideal.span {algebraMap R N a}).radical
  have : Module.Finite R N := integralClosure_finite a Ra B ha hloc
  have : IsNoetherianRing N := Algebra.FiniteType.isNoetherianRing R N
  apply isRegularRing_iff.mpr
  intro P hP
  let Q : Ideal N := P.comap (Ideal.Quotient.mk I)
  have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
  have haQ : algebraMap R N a ∈ Q := by
    change Ideal.Quotient.mk I (algebraMap R N a) ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.le_radical (Ideal.mem_span_singleton_self _))]
    exact P.zero_mem
  let y : PrimeSpectrum R := ⟨Q.comap (algebraMap R N), Ideal.comap_isPrime _ _⟩
  obtain ⟨A, _, _, _, ⟨y', hy'⟩, _, hAa, _, n, e, u, he, _, ⟨g⟩⟩ := hloc y haQ
  obtain ⟨_, _, _, hTreg⟩ := isRegularRing_reducedDivisor_of_standardCoverEquiv a Ra B hAa e u he g
  have hPR : P.comap (algebraMap R (N ⧸ I)) = y'.asIdeal.comap (algebraMap R A) := by
    rw [IsScalarTower.algebraMap_eq R N (N ⧸ I), ← Ideal.comap_comap]
    exact hy'.symm
  obtain ⟨P', hP', hP'P⟩ := exists_isPrime_tensorProduct_comap_eq (S := N ⧸ I) P y'.asIdeal hPR
  have : P'.LiesOver P := ⟨hP'P.symm⟩
  have : IsRegularLocalRing (Localization.AtPrime P') := isRegularRing_iff.mp hTreg P'
  exact isRegularLocalRing_atPrime_of_etale P P' this

include Ra in
/-- **The reduced inverse image of the divisor is an effective Cartier divisor** (second
assertion of Stacks Tag `0EYH`, affine form): near every prime `Q ∋ a` of the normalization `N`,
`rad(aN)` is generated by one nonzerodivisor. -/
@[stacks 0EYH "second assertion (D' effective Cartier), affine local form"]
theorem exists_radical_eq_span_of_mem (ha : a ∈ nonZeroDivisors R)
    (hloc : ∀ y : PrimeSpectrum R, a ∈ y.asIdeal → HasLocalizedStandardCoverAt a B y)
    (Q : PrimeSpectrum (integralClosure R B))
    (hQ : algebraMap R (integralClosure R B) a ∈ Q.asIdeal) :
    ∃ h : integralClosure R B, h ∉ Q.asIdeal ∧
      ∀ (Nh : Type u) [CommRing Nh] [Algebra (integralClosure R B) Nh]
        [IsLocalization.Away h Nh],
        ∃ t : Nh, t ∈ nonZeroDivisors Nh ∧
          (Ideal.span {algebraMap (integralClosure R B) Nh (algebraMap R _ a)}).radical =
            Ideal.span {t} := by
  let N := integralClosure R B
  let I : Ideal N := (Ideal.span {algebraMap R N a}).radical
  have : Module.Finite R N := integralClosure_finite a Ra B ha hloc
  have : IsNoetherianRing N := Algebra.FiniteType.isNoetherianRing R N
  let y : PrimeSpectrum R := ⟨Q.asIdeal.comap (algebraMap R N), Ideal.comap_isPrime _ _⟩
  obtain ⟨A, _, _, _, ⟨y', hy'⟩, _, hAa, _, n, e, u, he, _, ⟨g⟩⟩ := hloc y hQ
  obtain ⟨t, ht, hIt, _⟩ := isRegularRing_reducedDivisor_of_standardCoverEquiv a Ra B hAa e u he g
  obtain ⟨Q', hQ', hQ'Q⟩ := exists_isPrime_tensorProduct_comap_eq (S := N) Q.asIdeal y'.asIdeal
    hy'.symm
  have : Q'.LiesOver Q.asIdeal := ⟨hQ'Q.symm⟩
  obtain ⟨s, hs, hIs⟩ := exists_span_nonZeroDivisor_atPrime_of_etale Q.asIdeal Q' I ht hIt
  obtain ⟨h, hhQ, m, hmI, hspread⟩ := exists_away_span_nonZeroDivisor_of_atPrime Q.asIdeal I hs hIs
  refine ⟨h, hhQ, fun Nh _ _ _ => ⟨algebraMap N Nh m, (hspread Nh).1, ?_⟩⟩
  rw [← (hspread Nh).2, ← Set.image_singleton, ← Ideal.map_span,
    IsLocalization.map_radical (Submonoid.powers h) Nh]
end Divisor

end Pcf.Stacks.SchemeLevel
