/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FerrandPushoutAffine

/-!
# Affine Ferrand pinching commutes with localization

For `paper-p.tex`, Example `ex:monodromy-loss` (gluing the affine pinchings of
`FerrandPushoutAffine` into the global pinched variety `X`).

Let `B' = B ×_A A'` (`Fib π β`) and `h ∈ B'` with components `h₁ ∈ B`, `h₂ ∈ A'` and common image
`h̄ = β h₁ = π h₂ ∈ A`. Put
`π_h : A'_{h₂} → A_{h̄}` (`piLoc`) and `β_h : B_{h₁} → A_{h̄}` (`betaLoc`).

* `isLocalization_away`: `B_{h₁} ×_{A_{h̄}} A'_{h₂}` (`Fib (piLoc h) (betaLoc h)`) is a localization
  of `B'` away from `h`, through `toFibLoc h : z ↦ (z₁, z₂)`.
* `piLoc_surjective`, `betaLoc_isIntegral`: the localized data again satisfy the hypotheses of
  `FerrandPushout.isPushout`.
* `fibLocEquiv`: hence `B'_h ≃ B_{h₁} ×_{A_{h̄}} A'_{h₂}` as `B'`-algebras.

So the basic open `D(h) ⊂ Spec B'` is again an affine Ferrand pinching, of the localized data.
The statement is phrased with `IsLocalization.Away` to avoid comparing the types
`Localization.Away (π h₂)` and `Localization.Away (β h₁)`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FerrandPushout

open AlgebraicGeometry CategoryTheory Limits

set_option linter.unusedSectionVars false

universe u

variable {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B] (π : A' →+* A) (β : B →+* A)
  (h : Fib π β)

local notation "Bh" => Localization.Away (pr₁ π β h)
local notation "A'h" => Localization.Away (pr₂ π β h)
local notation "Ah" => Localization.Away (hbar π β h)

/-- `π_h : A'_{h₂} → A_{h̄}`. -/
noncomputable def piLoc : A'h →+* Ah :=
  IsLocalization.Away.lift (pr₂ π β h) (g := (algebraMap A Ah).comp π) (by
    change IsUnit (algebraMap A _ (π (pr₂ π β h)))
    rw [hbar_eq]
    exact IsLocalization.Away.algebraMap_isUnit (hbar π β h))

/-- `β_h : B_{h₁} → A_{h̄}`. -/
noncomputable def betaLoc : Bh →+* Ah :=
  IsLocalization.Away.lift (pr₁ π β h) (g := (algebraMap A Ah).comp β)
    (IsLocalization.Away.algebraMap_isUnit (hbar π β h))

theorem piLoc_algebraMap (a : A') :
    piLoc π β h (algebraMap A' A'h a) = algebraMap A Ah (π a) :=
  IsLocalization.Away.lift_eq _ _ a

theorem betaLoc_algebraMap (b : B) :
    betaLoc π β h (algebraMap B Bh b) = algebraMap A Ah (β b) :=
  IsLocalization.Away.lift_eq _ _ b

/-- `B' → B_{h₁} ×_{A_{h̄}} A'_{h₂}`. -/
noncomputable def toFibLoc : Fib π β →+* Fib (piLoc π β h) (betaLoc π β h) :=
  RingHom.codRestrict ((RingHom.prodMap (algebraMap B Bh) (algebraMap A' A'h)).comp (incl π β))
    (fib (piLoc π β h) (betaLoc π β h)) fun z => by
      rw [mem_fib]
      change betaLoc π β h (algebraMap B Bh (pr₁ π β z)) =
        piLoc π β h (algebraMap A' A'h (pr₂ π β z))
      rw [betaLoc_algebraMap, piLoc_algebraMap, pr_comm_apply]

theorem toFibLoc_fst (z : Fib π β) : (toFibLoc π β h z).1.1 = algebraMap B Bh (pr₁ π β z) := rfl

theorem toFibLoc_snd (z : Fib π β) : (toFibLoc π β h z).1.2 = algebraMap A' A'h (pr₂ π β z) := rfl

theorem betaLoc_h : betaLoc π β h (algebraMap B Bh (pr₁ π β h)) = algebraMap A Ah (hbar π β h) :=
  betaLoc_algebraMap π β h _

theorem piLoc_h : piLoc π β h (algebraMap A' A'h (pr₂ π β h)) = algebraMap A Ah (hbar π β h) :=
  (piLoc_algebraMap π β h _).trans (congrArg _ (hbar_eq π β h))

theorem toFibLoc_isUnit : IsUnit (toFibLoc π β h h) := by
  have hmem : (IsLocalization.Away.invSelf (S := Bh) (pr₁ π β h),
      IsLocalization.Away.invSelf (S := A'h) (pr₂ π β h)) ∈ fib (piLoc π β h) (betaLoc π β h) := by
    rw [mem_fib]
    have u₁ : algebraMap A Ah (hbar π β h) * betaLoc π β h
        (IsLocalization.Away.invSelf (pr₁ π β h)) = 1 := by
      rw [← betaLoc_h, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    have u₂ : algebraMap A Ah (hbar π β h) * piLoc π β h
        (IsLocalization.Away.invSelf (pr₂ π β h)) = 1 := by
      rw [← piLoc_h, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    have hu : IsUnit (algebraMap A Ah (hbar π β h)) :=
      IsLocalization.Away.algebraMap_isUnit _
    exact hu.mul_left_cancel (u₁.trans u₂.symm)
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
  · exact IsLocalization.Away.mul_invSelf (pr₁ π β h)
  · exact IsLocalization.Away.mul_invSelf (pr₂ π β h)

theorem coe_pow_fst (z : Fib (piLoc π β h) (betaLoc π β h)) (n : ℕ) :
    (z ^ n).1.1 = z.1.1 ^ n := by
  rw [SubmonoidClass.coe_pow, Prod.pow_fst]

theorem coe_pow_snd (z : Fib (piLoc π β h) (betaLoc π β h)) (n : ℕ) :
    (z ^ n).1.2 = z.1.2 ^ n := by
  rw [SubmonoidClass.coe_pow, Prod.pow_snd]

/-- **The pinching commutes with localization**: `B_{h₁} ×_{A_{h̄}} A'_{h₂}` is `B'_h`. -/
theorem isLocalization_away :
    letI := (toFibLoc π β h).toAlgebra
    IsLocalization.Away h (Fib (piLoc π β h) (betaLoc π β h)) := by
  let := (toFibLoc π β h).toAlgebra
  refine IsLocalization.Away.mk h (toFibLoc_isUnit π β h) ?_ ?_
  · rintro ⟨⟨u, v⟩, huv⟩
    rw [mem_fib] at huv
    obtain ⟨n₁, b, hb⟩ := IsLocalization.Away.surj (pr₁ π β h) u
    obtain ⟨n₂, a, ha⟩ := IsLocalization.Away.surj (pr₂ π β h) v
    set N := n₁ + n₂
    set b' := b * pr₁ π β h ^ n₂
    set a' := a * pr₂ π β h ^ n₁
    have hb' : u * algebraMap B Bh (pr₁ π β h) ^ N = algebraMap B Bh b' := by
      simp only [b', N, map_mul, ← hb, map_pow, pow_add]; ring
    have ha' : v * algebraMap A' A'h (pr₂ π β h) ^ N = algebraMap A' A'h a' := by
      simp only [a', N, map_mul, ← ha, map_pow, pow_add]; ring
    have e₁ := congrArg (betaLoc π β h) hb'
    have e₂ := congrArg (piLoc π β h) ha'
    rw [map_mul, map_pow, betaLoc_h, betaLoc_algebraMap] at e₁
    rw [map_mul, map_pow, piLoc_h, piLoc_algebraMap] at e₂
    rw [huv, e₂] at e₁
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (hbar π β h) e₁
    have hmem : (pr₁ π β h ^ m * b', pr₂ π β h ^ m * a') ∈ fib π β := by
      rw [mem_fib]
      simp only [map_mul, map_pow]
      rw [hbar_eq]
      exact hm.symm
    refine ⟨m + N, ⟨_, hmem⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change u * ((toFibLoc π β h h) ^ (m + N)).1.1 = algebraMap B Bh (pr₁ π β h ^ m * b')
      rw [coe_pow_fst, toFibLoc_fst, map_mul, ← hb', map_pow]; ring
    · change v * ((toFibLoc π β h h) ^ (m + N)).1.2 = algebraMap A' A'h (pr₂ π β h ^ m * a')
      rw [coe_pow_snd, toFibLoc_snd, map_mul, ← ha', map_pow]; ring
  · intro a b hab
    have h1 := congrArg (fun z : Fib (piLoc π β h) (betaLoc π β h) => z.1.1) hab
    have h2 := congrArg (fun z : Fib (piLoc π β h) (betaLoc π β h) => z.1.2) hab
    obtain ⟨n₁, hn₁⟩ := IsLocalization.Away.exists_of_eq (S := Bh) (pr₁ π β h)
      (show algebraMap B Bh (pr₁ π β a) = algebraMap B Bh (pr₁ π β b) from h1)
    obtain ⟨n₂, hn₂⟩ := IsLocalization.Away.exists_of_eq (S := A'h) (pr₂ π β h)
      (show algebraMap A' A'h (pr₂ π β a) = algebraMap A' A'h (pr₂ π β b) from h2)
    refine ⟨n₁ + n₂, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change pr₁ π β (h ^ (n₁ + n₂) * a) = pr₁ π β (h ^ (n₁ + n₂) * b)
      simp only [map_mul, map_pow, pow_add]
      rw [mul_comm (pr₁ π β h ^ n₁), mul_assoc, hn₁, ← mul_assoc]
    · change pr₂ π β (h ^ (n₁ + n₂) * a) = pr₂ π β (h ^ (n₁ + n₂) * b)
      simp only [map_mul, map_pow, pow_add]
      rw [mul_assoc, hn₂, ← mul_assoc]

theorem algebraMap_hbar_mul_piLoc_inv :
    algebraMap A Ah (hbar π β h) * piLoc π β h (IsLocalization.Away.invSelf (pr₂ π β h)) = 1 := by
  rw [← piLoc_h, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

theorem algebraMap_hbar_mul_betaLoc_inv :
    algebraMap A Ah (hbar π β h) * betaLoc π β h (IsLocalization.Away.invSelf (pr₁ π β h)) = 1 := by
  rw [← betaLoc_h, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

variable {π β}

/-- The localized `π_h` is surjective. -/
theorem piLoc_surjective (hπ : Function.Surjective π) : Function.Surjective (piLoc π β h) := by
  intro w
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (hbar π β h) w
  obtain ⟨a, rfl⟩ := hπ c
  refine ⟨algebraMap A' A'h a * IsLocalization.Away.invSelf (pr₂ π β h) ^ n, ?_⟩
  rw [map_mul, map_pow, piLoc_algebraMap, ← hc]
  calc w * algebraMap A Ah (hbar π β h) ^ n * piLoc π β h (IsLocalization.Away.invSelf _) ^ n
      = w * (algebraMap A Ah (hbar π β h) * piLoc π β h (IsLocalization.Away.invSelf _)) ^ n := by
        ring
    _ = w := by rw [algebraMap_hbar_mul_piLoc_inv, one_pow, mul_one]

/-- The localized `β_h` is integral. -/
theorem betaLoc_isIntegral (hβ : β.IsIntegral) : (betaLoc π β h).IsIntegral := by
  have hcomp : (betaLoc π β h).comp (algebraMap B Bh) = (algebraMap A Ah).comp β :=
    RingHom.ext (betaLoc_algebraMap π β h)
  have halg : ∀ a : A, (betaLoc π β h).IsIntegralElem (algebraMap A Ah a) := by
    intro a
    obtain ⟨p, hpm, hp⟩ := hβ a
    refine ⟨p.map (algebraMap B Bh), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
  intro w
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (hbar π β h) w
  have hw : w = algebraMap A Ah c * betaLoc π β h (IsLocalization.Away.invSelf (pr₁ π β h)) ^ n := by
    rw [← hc]
    calc w = w * (algebraMap A Ah (hbar π β h) *
          betaLoc π β h (IsLocalization.Away.invSelf _)) ^ n := by
          rw [algebraMap_hbar_mul_betaLoc_inv, one_pow, mul_one]
      _ = _ := by ring
  rw [hw, ← map_pow]
  exact RingHom.IsIntegralElem.mul _ (halg c) (betaLoc π β h).isIntegralElem_map

variable (π β)

/-- `B'_h ≃ B_{h₁} ×_{A_{h̄}} A'_{h₂}` as rings, compatibly with `B'`. -/
noncomputable def fibLocEquiv : Localization.Away h ≃+* Fib (piLoc π β h) (betaLoc π β h) :=
  letI := (toFibLoc π β h).toAlgebra
  haveI := isLocalization_away π β h
  (IsLocalization.algEquiv (Submonoid.powers h) (Localization.Away h)
    (Fib (piLoc π β h) (betaLoc π β h))).toRingEquiv

theorem fibLocEquiv_algebraMap (z : Fib π β) :
    fibLocEquiv π β h (algebraMap _ (Localization.Away h) z) = toFibLoc π β h z := by
  let := (toFibLoc π β h).toAlgebra
  have := isLocalization_away π β h
  exact (IsLocalization.algEquiv (Submonoid.powers h) (Localization.Away h)
    (Fib (piLoc π β h) (betaLoc π β h))).commutes z

variable {π β}

/-- **The basic open `D(h)` of an affine Ferrand pinching is the affine Ferrand pinching of the
localized data**: `Spec(B_{h₁} ×_{A_{h̄}} A'_{h₂})` is the pushout of
`Spec B_{h₁} ← Spec A_{h̄} → Spec A'_{h₂}`. -/
theorem isPushout_loc (hπ : Function.Surjective π) (hβ : β.IsIntegral) :
    IsPushout (Spec.map (CommRingCat.ofHom (piLoc π β h)))
      (Spec.map (CommRingCat.ofHom (betaLoc π β h)))
      (Spec.map (CommRingCat.ofHom (pr₂ (piLoc π β h) (betaLoc π β h))))
      (Spec.map (CommRingCat.ofHom (pr₁ (piLoc π β h) (betaLoc π β h)))) :=
  isPushout (piLoc_surjective h hπ) (betaLoc_isIntegral h hβ)

#print axioms isLocalization_away
#print axioms fibLocEquiv_algebraMap
#print axioms isPushout_loc

end Pcf.Examples.PaperP.FerrandPushout
