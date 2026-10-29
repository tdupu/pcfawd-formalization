/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedPushoutGlobal
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Affine Ferrand pinching: `Spec(B ×_A A')` is a pushout of schemes

For `paper-p.tex`, Example `ex:monodromy-loss`: "Pinch `E × {0}` along `y : E → ℙ¹` ... using the
finite pushout construction of [Fer03, §5.4]". Locally on affine charts the pinching is
`Spec(B ×_A A')`, where `A' → A` is the surjection onto the coordinate ring of the pinched
divisor and `B → A` is the finite map to be pinched along. This file proves, in general, that this
affine pinching is the pushout in the category of **all** schemes.

Setting: `π : A' →+* A` surjective, `β : B →+* A` integral, and `B' = B ×_A A'` (`Fib π β`, the
subring `{(b, a') | β b = π a'}` of `B × A'`, with projections `pr₁`, `pr₂`).

* `existsUnique_desc`: for every scheme `T`, every `a : Spec A' → T` and `b : Spec B → T` with
  `a ∘ Spec π = b ∘ Spec β`, there is a unique `φ : Spec B' → T` with `φ ∘ Spec pr₂ = a` and
  `φ ∘ Spec pr₁ = b`;
* `isPushout`: the corresponding `IsPushout` square in `Scheme`.

The proof generalizes `PinchedPushoutGlobal` (the instance `A' = k[z,w]`, `A = k × k`, `B = k`).
`ν : Spec(B × A') → Spec B'` is integral (`incl_isIntegral`) and injective on rings, so it is
surjective, closed and an epimorphism. All points of `Spec(B × A')` over one point of `Spec B'`
have the same image in `T` (`fibre_const`). Around every point there is a basic open `D(h)` with
`ν⁻¹ D(h)` mapping into an affine open of `T`; on it `B'_h → (B × A')_h` is injective with image
the elements whose two images in `A_h` agree (`mem_range_locIncl`), so the affine argument
applies, and the local maps glue (`PinchedPushoutGlobal.exists_desc_of_cover`).

Stacks 0ET0 proves the statement without the integrality hypothesis on `β`, via the topological
pushout. The integrality hypothesis is the one of Ferrand's situation (Stacks 0E25 / 37.67.1,
`Z → Y` integral) and is what the local proof here uses (`ν` closed).
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FerrandPushout

open AlgebraicGeometry CategoryTheory Limits Polynomial
open Pcf.Examples.PaperP.PinchedPushoutGlobal (exists_desc_of_cover
  epi_of_surjective_of_isSchemeTheoreticallyDominant)

set_option linter.unusedSectionVars false

universe u

variable {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B] (π : A' →+* A) (β : B →+* A)

/-! ### The fibre product ring -/

/-- The fibre product `B ×_A A'` as a subring of `B × A'`. -/
def fib : Subring (B × A') :=
  RingHom.eqLocus (β.comp (RingHom.fst B A')) (π.comp (RingHom.snd B A'))

/-- The ring `B' = B ×_A A'`. -/
abbrev Fib := ↥(fib π β)

theorem mem_fib (z : B × A') : z ∈ fib π β ↔ β z.1 = π z.2 := Iff.rfl

/-- The inclusion `B' → B × A'`. -/
def incl : Fib π β →+* B × A' := (fib π β).subtype

/-- The projection `B' → B`. -/
def pr₁ : Fib π β →+* B := (RingHom.fst B A').comp (incl π β)

/-- The projection `B' → A'`. -/
def pr₂ : Fib π β →+* A' := (RingHom.snd B A').comp (incl π β)

theorem incl_injective : Function.Injective (incl π β) := Subtype.val_injective

theorem pr_comm : β.comp (pr₁ π β) = π.comp (pr₂ π β) := RingHom.ext fun z => z.2

theorem pr_comm_apply (z : Fib π β) : β (pr₁ π β z) = π (pr₂ π β z) := z.2

variable {π β}

theorem pr₁_surjective (hπ : Function.Surjective π) : Function.Surjective (pr₁ π β) := by
  intro b
  obtain ⟨a', ha'⟩ := hπ (β b)
  exact ⟨⟨(b, a'), ha'.symm⟩, rfl⟩

/-- `(0, d) ∈ B'` for `d ∈ ker π`. -/
def kerElt (d : A') (hd : π d = 0) : Fib π β := ⟨(0, d), by simp [mem_fib, hd]⟩

/-- `A'` is integral over `B'` when `A` is integral over `B`. -/
theorem pr₂_isIntegralElem (hπ : Function.Surjective π) (hβ : β.IsIntegral) (c : A') :
    (pr₂ π β).IsIntegralElem c := by
  obtain ⟨q, hqm, hq⟩ := hβ (π c)
  have hlift : q ∈ Polynomial.lifts (pr₁ π β) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun n => pr₁_surjective hπ (q.coeff n)
  obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hqm
  set d := Q.eval₂ (pr₂ π β) c
  have hd : π (c * d) = 0 := by
    have : π d = 0 := by
      simp only [d]
      rw [Polynomial.hom_eval₂, ← pr_comm, ← Polynomial.eval₂_map, hQmap, hq]
    rw [map_mul, this, mul_zero]
  rcases subsingleton_or_nontrivial (Fib π β) with hs | hs
  · refine ⟨0, ?_, ?_⟩
    · exact Polynomial.monic_zero_iff_subsingleton.mpr hs
    · simp
  refine ⟨Polynomial.X * Q - Polynomial.C (kerElt (c * d) hd),
    (Polynomial.monic_X.mul hQm).sub_of_left ?_, ?_⟩
  · refine (Polynomial.degree_C_le).trans_lt ?_
    refine Polynomial.natDegree_pos_iff_degree_pos.mp ?_
    rw [Polynomial.monic_X.natDegree_mul hQm, Polynomial.natDegree_X]
    omega
  · simp [d, kerElt, pr₂, incl]

/-- `B × A'` is integral over `B'`. -/
theorem incl_isIntegral (hπ : Function.Surjective π) (hβ : β.IsIntegral) :
    (incl π β).IsIntegral := by
  intro z
  obtain ⟨a'', ha''⟩ := hπ (β z.1)
  set e : Fib π β := ⟨(z.1, a''), ha''.symm⟩
  have hz : z = incl π β e + (0, z.2 - a'') := by
    ext <;> simp [e, incl]
  rw [hz]
  refine RingHom.IsIntegralElem.add _ (RingHom.isIntegralElem_map _) ?_
  obtain ⟨Q, hQm, hQ⟩ := pr₂_isIntegralElem hπ hβ (z.2 - a'')
  refine ⟨Polynomial.X * Q, Polynomial.monic_X.mul hQm, ?_⟩
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_X]
  ext
  · simp
  · have := Polynomial.hom_eval₂ Q (incl π β) (RingHom.snd B A') (0, z.2 - a'')
    simp only [Prod.snd_mul, Prod.snd_zero]
    rw [show (Polynomial.eval₂ (incl π β) ((0 : B), z.2 - a'') Q).2 = _ from this]
    exact mul_eq_zero_of_right _ hQ

theorem ker_pr₁_le {x : Ideal (Fib π β)} (hx : ∀ d (hd : π d = 0), kerElt (β := β) d hd ∈ x) :
    RingHom.ker (pr₁ π β) ≤ x := by
  intro z hz
  have h1 : z.1.1 = 0 := hz
  have h2 : π z.1.2 = 0 := by
    change π (pr₂ π β z) = 0
    rw [← pr_comm_apply]; exact (congrArg β h1).trans (map_zero β)
  convert hx _ h2 using 1
  exact Subtype.ext (Prod.ext h1 rfl)

/-! ### Points -/

section Points

/-- A prime of `B × A'` comes from `B` or from `A'`. -/
theorem prime_prod_cases (y : PrimeSpectrum (B × A')) :
    (∃ u : PrimeSpectrum B, y = PrimeSpectrum.comap (RingHom.fst B A') u) ∨
      ∃ v : PrimeSpectrum A', y = PrimeSpectrum.comap (RingHom.snd B A') v := by
  rcases (Ideal.ideal_prod_prime y.asIdeal).mp y.isPrime with ⟨p, hp, hy⟩ | ⟨p, hp, hy⟩
  · refine Or.inl ⟨⟨p, hp⟩, PrimeSpectrum.ext ?_⟩
    rw [hy]; ext z; simp [Ideal.mem_prod]
  · refine Or.inr ⟨⟨p, hp⟩, PrimeSpectrum.ext ?_⟩
    rw [hy]; ext z; simp [Ideal.mem_prod]

variable (hπ : Function.Surjective π)
include hπ

theorem comap_pr₁_injective : Function.Injective (PrimeSpectrum.comap (pr₁ π β)) :=
  PrimeSpectrum.comap_injective_of_surjective _ (pr₁_surjective hπ)

/-- A point of `Spec A'` and a point of `Spec B` over the same point of `Spec B'` come from one
point of `Spec A`. -/
theorem exists_of_comap_eq (v : PrimeSpectrum A') (u : PrimeSpectrum B)
    (h : PrimeSpectrum.comap (pr₂ π β) v = PrimeSpectrum.comap (pr₁ π β) u) :
    ∃ w : PrimeSpectrum A, v = PrimeSpectrum.comap π w ∧ u = PrimeSpectrum.comap β w := by
  have hker : RingHom.ker π ≤ v.asIdeal := by
    intro d hd
    have : kerElt (β := β) d hd ∈ (PrimeSpectrum.comap (pr₁ π β) u).asIdeal := by
      change pr₁ π β (kerElt d hd) ∈ u.asIdeal
      simp [kerElt, pr₁, incl]
    rw [← h] at this
    exact this
  have hv : v ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    exact hker
  obtain ⟨w, rfl⟩ := hv
  refine ⟨w, rfl, comap_pr₁_injective (β := β) hπ ?_⟩
  rw [← h, ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, pr_comm]

/-- Two points of `Spec A'` over the same point of `Spec B'` either coincide or both come from
`Spec A` over one point of `Spec B`. -/
theorem snd_cases (v v' : PrimeSpectrum A')
    (h : PrimeSpectrum.comap (pr₂ π β) v = PrimeSpectrum.comap (pr₂ π β) v') :
    v = v' ∨ ∃ u : PrimeSpectrum B,
      PrimeSpectrum.comap (pr₂ π β) v = PrimeSpectrum.comap (pr₁ π β) u := by
  by_cases hall : ∀ d (hd : π d = 0), d ∈ v.asIdeal
  · right
    have hle : RingHom.ker (pr₁ π β) ≤ (PrimeSpectrum.comap (pr₂ π β) v).asIdeal :=
      ker_pr₁_le fun d hd => by
        change pr₂ π β (kerElt d hd) ∈ v.asIdeal
        exact hall d hd
    have : PrimeSpectrum.comap (pr₂ π β) v ∈ Set.range (PrimeSpectrum.comap (pr₁ π β)) := by
      rw [range_comap_of_surjective _ _ (pr₁_surjective hπ)]
      exact hle
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu.symm⟩
  · left
    push Not at hall
    obtain ⟨d, hd, hdv⟩ := hall
    have hdv' : d ∉ v'.asIdeal := by
      intro hm
      have : kerElt (β := β) d hd ∈ (PrimeSpectrum.comap (pr₂ π β) v').asIdeal := hm
      rw [← h] at this
      exact hdv this
    ext t
    have htd : π (t * d) = 0 := by rw [map_mul, hd, mul_zero]
    have key : ∀ w : PrimeSpectrum A', d ∉ w.asIdeal → (t ∈ w.asIdeal ↔
        kerElt (β := β) (t * d) htd ∈ (PrimeSpectrum.comap (pr₂ π β) w).asIdeal) := by
      intro w hw
      change t ∈ w.asIdeal ↔ t * d ∈ w.asIdeal
      refine ⟨fun ht => w.asIdeal.mul_mem_right d ht, fun h' => ?_⟩
      rcases w.isPrime.mem_or_mem h' with ht | ht
      · exact ht
      · exact absurd ht hw
    rw [key v hdv, key v' hdv', h]

end Points

/-! ### The morphism `ν` -/

section Nu

variable (π β)

/-- `ν : Spec(B × A') → Spec B'`. -/
noncomputable abbrev nu : Spec (CommRingCat.of (B × A')) ⟶ Spec (CommRingCat.of (Fib π β)) :=
  Spec.map (CommRingCat.ofHom (incl π β))

variable {π β}

/-- `Spec` of an injective ring map is scheme-theoretically dominant. -/
theorem isSchemeTheoreticallyDominant_Spec_map {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : Function.Injective f) : IsSchemeTheoreticallyDominant (Spec.map f) := by
  constructor
  rw [Scheme.ker_of_isAffine]
  have : RingHom.ker (Spec.map f).appTop.hom = ⊥ := by
    rw [← RingHom.injective_iff_ker_eq_bot]
    have e : (Spec.map f).appTop = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv := by
      rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
    rw [e]
    exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).1.comp hf).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1
  rw [this, ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply]
  exact map_bot _

variable (hπ : Function.Surjective π) (hβ : β.IsIntegral)
include hπ hβ

theorem nu_surjective : Surjective (nu π β) :=
  ⟨(incl_isIntegral hπ hβ).comap_surjective (incl_injective π β)⟩

/-- **`ν` is an epimorphism of schemes.** -/
theorem nu_epi : Epi (nu π β) := by
  have := nu_surjective hπ hβ
  have := isSchemeTheoreticallyDominant_Spec_map (CommRingCat.ofHom (incl π β))
    (incl_injective π β)
  exact epi_of_surjective_of_isSchemeTheoreticallyDominant _

end Nu

/-! ### The map `Spec(B × A') → T` -/

section CMap

variable {T : Scheme.{u}} (a : Spec (CommRingCat.of A') ⟶ T) (b : Spec (CommRingCat.of B) ⟶ T)

/-- The morphism `Spec(B × A') = Spec B ⨿ Spec A' → T` given by `b` and `a`. -/
noncomputable def cmap : Spec (CommRingCat.of (B × A')) ⟶ T :=
  inv (coprodSpec B A') ≫ coprod.desc b a

theorem fst_cmap : Spec.map (CommRingCat.ofHom (RingHom.fst B A')) ≫ cmap a b = b := by
  rw [cmap, ← coprodSpec_inl, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inl_desc]

theorem snd_cmap : Spec.map (CommRingCat.ofHom (RingHom.snd B A')) ≫ cmap a b = a := by
  rw [cmap, ← coprodSpec_inr, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inr_desc]

theorem cmap_fst_apply (u : PrimeSpectrum B) :
    cmap a b (PrimeSpectrum.comap (RingHom.fst B A') u) = b u := by
  exact congrArg (fun g : Spec (CommRingCat.of B) ⟶ T => g u) (fst_cmap a b)

theorem cmap_snd_apply (v : PrimeSpectrum A') :
    cmap a b (PrimeSpectrum.comap (RingHom.snd B A') v) = a v := by
  exact congrArg (fun g : Spec (CommRingCat.of A') ⟶ T => g v) (snd_cmap a b)

variable (hπ : Function.Surjective π)
include hπ

/-- **All points of `Spec(B × A')` over one point of `Spec B'` have the same image in `T`.** -/
theorem fibre_const (h : Spec.map (CommRingCat.ofHom π) ≫ a = Spec.map (CommRingCat.ofHom β) ≫ b)
    (y y' : PrimeSpectrum (B × A'))
    (hy : PrimeSpectrum.comap (incl π β) y = PrimeSpectrum.comap (incl π β) y') :
    cmap a b y = cmap a b y' := by
  have hab : ∀ w : PrimeSpectrum A, a (PrimeSpectrum.comap π w) = b (PrimeSpectrum.comap β w) :=
    fun w => by
      exact congrArg (fun g : Spec (CommRingCat.of A) ⟶ T => g w) h
  -- the mixed case
  have mixed : ∀ (v : PrimeSpectrum A') (u : PrimeSpectrum B),
      PrimeSpectrum.comap (pr₂ π β) v = PrimeSpectrum.comap (pr₁ π β) u → a v = b u := by
    intro v u hvu
    obtain ⟨w, rfl, rfl⟩ := exists_of_comap_eq hπ v u hvu
    exact hab w
  have c₁ : ∀ u : PrimeSpectrum B, PrimeSpectrum.comap (incl π β)
      (PrimeSpectrum.comap (RingHom.fst B A') u) = PrimeSpectrum.comap (pr₁ π β) u := fun _ => rfl
  have c₂ : ∀ v : PrimeSpectrum A', PrimeSpectrum.comap (incl π β)
      (PrimeSpectrum.comap (RingHom.snd B A') v) = PrimeSpectrum.comap (pr₂ π β) v := fun _ => rfl
  rcases prime_prod_cases y with ⟨u, rfl⟩ | ⟨v, rfl⟩ <;>
    rcases prime_prod_cases y' with ⟨u', rfl⟩ | ⟨v', rfl⟩
  · rw [c₁, c₁] at hy
    rw [comap_pr₁_injective (β := β) hπ hy]
  · rw [c₁, c₂] at hy
    rw [cmap_fst_apply, cmap_snd_apply]
    exact (mixed v' u hy.symm).symm
  · rw [c₂, c₁] at hy
    rw [cmap_fst_apply, cmap_snd_apply]
    exact mixed v u' hy
  · rw [c₂, c₂] at hy
    rw [cmap_snd_apply, cmap_snd_apply]
    rcases snd_cases hπ v v' hy with rfl | ⟨u, hu⟩
    · rfl
    · exact (mixed v u hu).trans (mixed v' u (hy.symm.trans hu)).symm

end CMap

/-! ### Localizations -/

section Loc

variable (π β)

/-- `ν` over `D(h)`: the ring map `B'_h → (B × A')_h`. -/
noncomputable def locIncl (h : Fib π β) :
    Localization.Away h →+* Localization.Away (incl π β h) :=
  Localization.awayMap (incl π β) h

theorem locIncl_algebraMap (h : Fib π β) (r : Fib π β) :
    locIncl π β h (algebraMap _ (Localization.Away h) r) =
      algebraMap (B × A') (Localization.Away (incl π β h)) (incl π β r) := by
  simp only [locIncl, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]

theorem locIncl_comp (h : Fib π β) :
    (locIncl π β h).comp (algebraMap _ (Localization.Away h)) =
      (algebraMap (B × A') (Localization.Away (incl π β h))).comp (incl π β) :=
  RingHom.ext (locIncl_algebraMap π β h)

instance isLocalization_map_powers (h : Fib π β) :
    IsLocalization ((Submonoid.powers h).map (incl π β))
      (Localization.Away (incl π β h)) := by
  rw [Submonoid.map_powers]
  infer_instance

/-- The square `B' → B × A'`, `B' → B'_h`, `(B × A') → (B × A')_h` gives a pullback of schemes. -/
theorem isPullback_loc (h : Fib π β) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (B × A') (Localization.Away (incl π β h)))))
      (Spec.map (CommRingCat.ofHom (locIncl π β h))) (nu π β)
      (Spec.map (CommRingCat.ofHom (algebraMap (Fib π β) (Localization.Away h)))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (incl π β) (locIncl π β h) (locIncl_comp π β h)
      (Submonoid.powers h))

theorem locIncl_injective (h : Fib π β) : Function.Injective (locIncl π β h) :=
  IsLocalization.map_injective_of_injective (Submonoid.powers h) (Localization.Away h)
    (Localization.Away (incl π β h)) (incl_injective π β)

/-- The image `β(h₁) = π(h₂)` of `h` in `A`. -/
def hbar (h : Fib π β) : A := β (pr₁ π β h)

theorem hbar_eq (h : Fib π β) : π (pr₂ π β h) = hbar π β h := (pr_comm_apply π β h).symm

/-- `(B × A')_h → A_h` through `B`. -/
noncomputable def L₁ (h : Fib π β) :
    Localization.Away (incl π β h) →+* Localization.Away (hbar π β h) :=
  IsLocalization.Away.lift (incl π β h)
    (g := (algebraMap A (Localization.Away (hbar π β h))).comp (β.comp (RingHom.fst B A')))
    (IsLocalization.Away.algebraMap_isUnit (hbar π β h))

/-- `(B × A')_h → A_h` through `A'`. -/
noncomputable def L₂ (h : Fib π β) :
    Localization.Away (incl π β h) →+* Localization.Away (hbar π β h) :=
  IsLocalization.Away.lift (incl π β h)
    (g := (algebraMap A (Localization.Away (hbar π β h))).comp (π.comp (RingHom.snd B A')))
    (by
      change IsUnit (algebraMap A _ (π (pr₂ π β h)))
      rw [hbar_eq]
      exact IsLocalization.Away.algebraMap_isUnit (hbar π β h))

theorem L₁_algebraMap (h : Fib π β) (z : B × A') :
    L₁ π β h (algebraMap _ _ z) = algebraMap A (Localization.Away (hbar π β h)) (β z.1) :=
  IsLocalization.Away.lift_eq _ _ z

theorem L₂_algebraMap (h : Fib π β) (z : B × A') :
    L₂ π β h (algebraMap _ _ z) = algebraMap A (Localization.Away (hbar π β h)) (π z.2) :=
  IsLocalization.Away.lift_eq _ _ z

/-- **`B'_h = B_h ×_{A_h} A'_h`**: an element of `(B × A')_h` whose two images in `A_h` agree
comes from `B'_h`. -/
theorem mem_range_locIncl (h : Fib π β) (z : Localization.Away (incl π β h))
    (hz : L₁ π β h z = L₂ π β h z) : z ∈ (locIncl π β h).range := by
  obtain ⟨s, ⟨_, n, rfl⟩, rfl⟩ :=
    IsLocalization.exists_mk'_eq (Submonoid.powers (incl π β h)) z
  have spec := IsLocalization.mk'_spec (Localization.Away (incl π β h)) s
    (⟨incl π β h ^ n, n, rfl⟩ : Submonoid.powers (incl π β h))
  have e₁ := congrArg (L₁ π β h) spec
  have e₂ := congrArg (L₂ π β h) spec
  simp only [map_mul, L₁_algebraMap, L₂_algebraMap] at e₁ e₂
  rw [hz] at e₁
  have hh : π (incl π β h ^ n).2 = β (incl π β h ^ n).1 := by
    simp only [Prod.pow_fst, Prod.pow_snd, map_pow]
    exact congrArg (· ^ n) (pr_comm_apply π β h).symm
  rw [hh] at e₂
  have heq : algebraMap A (Localization.Away (hbar π β h)) (β s.1) =
      algebraMap A (Localization.Away (hbar π β h)) (π s.2) := e₁.symm.trans e₂
  obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers (hbar π β h)) _).mp heq
  simp only at hm
  have hmem : ((pr₁ π β h) ^ m * s.1, (pr₂ π β h) ^ m * s.2) ∈ fib π β := by
    rw [mem_fib]
    simp only [map_mul, map_pow]
    rw [hbar_eq]
    exact hm
  refine ⟨IsLocalization.mk' (Localization.Away h) (⟨_, hmem⟩ : Fib π β)
    (⟨h ^ (m + n), m + n, rfl⟩ : Submonoid.powers h), ?_⟩
  simp only [locIncl, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk']
  rw [IsLocalization.mk'_eq_iff_eq]
  congr 1
  ext <;> simp [incl, pr₁, pr₂] <;> ring

/-- The ring-level factorization through `B'_h`. -/
theorem exists_factor (h : Fib π β) {C : CommRingCat.{u}}
    (α : C ⟶ CommRingCat.of (Localization.Away (incl π β h)))
    (hα : α ≫ CommRingCat.ofHom (L₁ π β h) = α ≫ CommRingCat.ofHom (L₂ π β h)) :
    ∃ γ : C ⟶ CommRingCat.of (Localization.Away h),
      γ ≫ CommRingCat.ofHom (locIncl π β h) = α := by
  let E := RingEquiv.ofBijective (locIncl π β h).rangeRestrict
    ⟨fun x y e => locIncl_injective π β h (congrArg Subtype.val e),
      (locIncl π β h).rangeRestrict_surjective⟩
  have hmem : ∀ x, α x ∈ (locIncl π β h).range := fun x =>
    mem_range_locIncl π β h _ (congrArg (fun f => f.hom x) hα)
  refine ⟨CommRingCat.ofHom (E.symm.toRingHom.comp (α.hom.codRestrict _ hmem)), ?_⟩
  ext x
  change locIncl π β h (E.symm ⟨α x, hmem x⟩) = α x
  have := E.apply_symm_apply ⟨α x, hmem x⟩
  exact congrArg Subtype.val this

end Loc

/-! ### Local solutions and the universal property -/

section Universal

variable {T : Scheme.{u}} (a : Spec (CommRingCat.of A') ⟶ T) (b : Spec (CommRingCat.of B) ⟶ T)

theorem ring_L₁ (h : Fib π β) :
    CommRingCat.ofHom (algebraMap (B × A') (Localization.Away (incl π β h))) ≫
        CommRingCat.ofHom (L₁ π β h) =
      CommRingCat.ofHom (RingHom.fst B A') ≫ CommRingCat.ofHom β ≫
        CommRingCat.ofHom (algebraMap A (Localization.Away (hbar π β h))) := by
  ext z
  exact L₁_algebraMap π β h z

theorem ring_L₂ (h : Fib π β) :
    CommRingCat.ofHom (algebraMap (B × A') (Localization.Away (incl π β h))) ≫
        CommRingCat.ofHom (L₂ π β h) =
      CommRingCat.ofHom (RingHom.snd B A') ≫ CommRingCat.ofHom π ≫
        CommRingCat.ofHom (algebraMap A (Localization.Away (hbar π β h))) := by
  ext z
  exact L₂_algebraMap π β h z

/-- Over `D(h)`: if `ν⁻¹ D(h)` maps into an affine open `V` of `T`, the map descends over
`D(h)`. -/
theorem local_desc
    (hab : Spec.map (CommRingCat.ofHom π) ≫ a = Spec.map (CommRingCat.ofHom β) ≫ b)
    (h : Fib π β) (V : T.Opens) (hV : IsAffineOpen V)
    (hrange : ∀ x, (Spec.map (CommRingCat.ofHom
      (algebraMap (B × A') (Localization.Away (incl π β h)))) ≫ cmap a b) x ∈ V) :
    ∃ g : Spec (CommRingCat.of (Localization.Away h)) ⟶ T,
      Spec.map (CommRingCat.ofHom (algebraMap (B × A') (Localization.Away (incl π β h)))) ≫
          cmap a b = Spec.map (CommRingCat.ofHom (locIncl π β h)) ≫ g := by
  set ι := Spec.map (CommRingCat.ofHom (algebraMap (B × A') (Localization.Away (incl π β h))))
  let a'' : Spec (CommRingCat.of (Localization.Away (incl π β h))) ⟶ V :=
    IsOpenImmersion.lift V.ι (ι ≫ cmap a b) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hrange x)
  have ha'' : a'' ≫ V.ι = ι ≫ cmap a b := IsOpenImmersion.lift_fac _ _ _
  let α := Spec.preimage (a'' ≫ hV.isoSpec.hom)
  have hα : Spec.map α = a'' ≫ hV.isoSpec.hom := Spec.map_preimage _
  have hev₁ : Spec.map (CommRingCat.ofHom (L₁ π β h)) ≫ ι ≫ cmap a b =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (hbar π β h)))) ≫
        Spec.map (CommRingCat.ofHom β) ≫ b := by
    rw [← Category.assoc, ← Spec.map_comp, ring_L₁]
    simp only [Spec.map_comp, Category.assoc, fst_cmap]
  have hev₂ : Spec.map (CommRingCat.ofHom (L₂ π β h)) ≫ ι ≫ cmap a b =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (hbar π β h)))) ≫
        Spec.map (CommRingCat.ofHom π) ≫ a := by
    rw [← Category.assoc, ← Spec.map_comp, ring_L₂]
    simp only [Spec.map_comp, Category.assoc, snd_cmap]
  have hcond : α ≫ CommRingCat.ofHom (L₁ π β h) = α ≫ CommRingCat.ofHom (L₂ π β h) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hα]
    rw [← cancel_mono hV.isoSpec.inv, ← cancel_mono V.ι]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, ha'']
    rw [hev₁, hev₂, hab]
  obtain ⟨γ, hγ⟩ := exists_factor π β h α hcond
  refine ⟨Spec.map γ ≫ hV.isoSpec.inv ≫ V.ι, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hγ, hα, Category.assoc, Iso.hom_inv_id_assoc, ha'']

variable (hπ : Function.Surjective π) (hβ : β.IsIntegral)
include hπ hβ

/-- **Choice of `D(h) ∋ x`** with `ν⁻¹ D(h)` mapping into an affine open of `T`. Uses that `ν` is
closed (integral) and that `T`-images are constant on fibres of `ν` (`fibre_const`). -/
theorem exists_basicOpen
    (hab : Spec.map (CommRingCat.ofHom π) ≫ a = Spec.map (CommRingCat.ofHom β) ≫ b)
    (x : PrimeSpectrum (Fib π β)) :
    ∃ h : Fib π β, h ∉ x.asIdeal ∧ ∃ V : T.Opens, IsAffineOpen V ∧
      ∀ y, (Spec.map (CommRingCat.ofHom
        (algebraMap (B × A') (Localization.Away (incl π β h)))) ≫ cmap a b) y ∈ V := by
  obtain ⟨y₀, hy₀⟩ := (incl_isIntegral hπ hβ).comap_surjective (incl_injective π β) x
  obtain ⟨V, hV, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (x := cmap a b y₀)
    (U := ⊤) trivial
  let U : Set (PrimeSpectrum (B × A')) := {Q | cmap a b Q ∈ V}
  have hU : IsOpen U := (cmap a b ⁻¹ᵁ V).isOpen
  let F := PrimeSpectrum.comap (incl π β) '' Uᶜ
  have hF : IsClosed F := PrimeSpectrum.isClosedMap_comap_of_isIntegral (incl π β)
    (incl_isIntegral hπ hβ) _ hU.isClosed_compl
  have hxF : x ∉ F := by
    rintro ⟨Q, hQ, hQx⟩
    apply hQ
    change cmap a b Q ∈ V
    rw [fibre_const a b hπ hab Q y₀ (hQx.trans hy₀.symm)]
    exact hpV
  obtain ⟨_, ⟨h, rfl⟩, hxh, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxF hF.isOpen_compl
  refine ⟨h, (PrimeSpectrum.mem_basicOpen _ _).mp hxh, V, hV, fun y => ?_⟩
  let y' : PrimeSpectrum (B × A') := PrimeSpectrum.comap
    (algebraMap (B × A') (Localization.Away (incl π β h))) y
  have hy : PrimeSpectrum.comap (incl π β) y' ∈ PrimeSpectrum.basicOpen h := by
    rw [PrimeSpectrum.mem_basicOpen]
    intro hmem
    have hunit : IsUnit (algebraMap (B × A') (Localization.Away (incl π β h)) (incl π β h)) :=
      IsLocalization.Away.algebraMap_isUnit _
    exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)
  by_contra hy'
  exact hsub hy ⟨y', hy', rfl⟩

/-- **Existence**: `cmap a b` factors through `ν`. -/
theorem exists_desc_nu
    (hab : Spec.map (CommRingCat.ofHom π) ≫ a = Spec.map (CommRingCat.ofHom β) ≫ b) :
    ∃ φ : Spec (CommRingCat.of (Fib π β)) ⟶ T, nu π β ≫ φ = cmap a b := by
  choose s hs V hV hrange using exists_basicOpen a b hπ hβ hab
  have hspan : Ideal.span (Set.range s) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hs ⟨M, hM.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop
    (R := CommRingCat.of (Fib π β)) s hspan).openCover
  have := nu_surjective hπ hβ
  have := isSchemeTheoreticallyDominant_Spec_map (CommRingCat.ofHom (incl π β))
    (incl_injective π β)
  refine exists_desc_of_cover (nu π β) (cmap a b) 𝒰 fun i => ?_
  obtain ⟨g, hg⟩ := local_desc a b hab (s i) (V i) (hV i) (hrange i)
  exact ⟨_, _, _, g, isPullback_loc π β (s i), hg⟩

/-- **Affine Ferrand pinching, universal property for every scheme `T`.** Let `π : A' → A` be
surjective and `β : B → A` integral. Given `a : Spec A' → T` and `b : Spec B → T` with
`a ∘ Spec π = b ∘ Spec β`, there is a unique `φ : Spec(B ×_A A') → T` with `φ ∘ Spec pr₂ = a`
and `φ ∘ Spec pr₁ = b`. -/
@[stacks 0ET0 "with `B → A` integral; local proof, not via the topological pushout"]
theorem existsUnique_desc
    (hab : Spec.map (CommRingCat.ofHom π) ≫ a = Spec.map (CommRingCat.ofHom β) ≫ b) :
    ∃! φ : Spec (CommRingCat.of (Fib π β)) ⟶ T,
      Spec.map (CommRingCat.ofHom (pr₂ π β)) ≫ φ = a ∧
        Spec.map (CommRingCat.ofHom (pr₁ π β)) ≫ φ = b := by
  have e₂ : Spec.map (CommRingCat.ofHom (pr₂ π β)) =
      Spec.map (CommRingCat.ofHom (RingHom.snd B A')) ≫ nu π β := by
    rw [← Spec.map_comp]; rfl
  have e₁ : Spec.map (CommRingCat.ofHom (pr₁ π β)) =
      Spec.map (CommRingCat.ofHom (RingHom.fst B A')) ≫ nu π β := by
    rw [← Spec.map_comp]; rfl
  obtain ⟨φ, hφ⟩ := exists_desc_nu a b hπ hβ hab
  refine ⟨φ, ⟨?_, ?_⟩, fun ψ ⟨hψ₂, hψ₁⟩ => ?_⟩
  · rw [e₂, Category.assoc, hφ, snd_cmap]
  · rw [e₁, Category.assoc, hφ, fst_cmap]
  · have := nu_epi hπ hβ
    rw [← cancel_epi (nu π β), hφ, ← cancel_epi (coprodSpec B A')]
    refine coprod.hom_ext ?_ ?_
    · rw [coprodSpec_inl_assoc, coprodSpec_inl_assoc, ← Category.assoc, ← e₁, hψ₁, fst_cmap]
    · rw [coprodSpec_inr_assoc, coprodSpec_inr_assoc, ← Category.assoc, ← e₂, hψ₂, snd_cmap]

/-- **`Spec(B ×_A A')` is the pushout of `Spec B ← Spec A → Spec A'` in `Scheme`.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
@[stacks 0ET0 "with `B → A` integral"]
theorem isPushout :
    IsPushout (Spec.map (CommRingCat.ofHom π)) (Spec.map (CommRingCat.ofHom β))
      (Spec.map (CommRingCat.ofHom (pr₂ π β))) (Spec.map (CommRingCat.ofHom (pr₁ π β))) := by
  have w : Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom (pr₂ π β)) =
      Spec.map (CommRingCat.ofHom β) ≫ Spec.map (CommRingCat.ofHom (pr₁ π β)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    exact (pr_comm π β).symm
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk w
    (fun s => (existsUnique_desc s.inl s.inr hπ hβ s.condition).choose)
    (fun s => (existsUnique_desc s.inl s.inr hπ hβ s.condition).choose_spec.1.1)
    (fun s => (existsUnique_desc s.inl s.inr hπ hβ s.condition).choose_spec.1.2)
    (fun s m h1 h2 =>
      (existsUnique_desc s.inl s.inr hπ hβ s.condition).choose_spec.2 m ⟨h1, h2⟩))

end Universal

#print axioms incl_isIntegral
#print axioms fibre_const
#print axioms mem_range_locIncl
#print axioms exists_desc_nu
#print axioms existsUnique_desc
#print axioms isPushout

end Pcf.Examples.PaperP.FerrandPushout
