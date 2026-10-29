/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FerrandPushoutLocalization

/-!
# Functoriality of the affine Ferrand pinching, and localization along any model

For `paper-p.tex`, Example `ex:monodromy-loss`: to glue the pinched charts of `X` one needs the
overlaps of two charts to be the *same* ring. This file provides:

* `fibMap`: a compatible triple of ring maps `A'₁ → A'₂`, `A₁ → A₂`, `B₁ → B₂` induces
  `B₁ ×_{A₁} A'₁ → B₂ ×_{A₂} A'₂` (with `pr₁_fibMap`, `pr₂_fibMap`);
* **`isLocalization_fibMap`**: if `A'₂`, `A₂`, `B₂` are localizations of `A'₁`, `A₁`, `B₁` away
  from the components `h₂`, `h̄`, `h₁` of some `h ∈ B₁ ×_{A₁} A'₁` (any models of the
  localizations, with any algebra structures compatible with `π`, `β`), then
  `B₂ ×_{A₂} A'₂` is the localization of `B₁ ×_{A₁} A'₁` away from `h`.

This generalizes `FerrandPushout.isLocalization_away` (the case of the canonical models).
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FerrandPushout

open AlgebraicGeometry CategoryTheory Limits

set_option linter.unusedSectionVars false

universe u

section Map

variable {A'₁ A₁ B₁ A'₂ A₂ B₂ : Type u} [CommRing A'₁] [CommRing A₁] [CommRing B₁]
  [CommRing A'₂] [CommRing A₂] [CommRing B₂]
  (π₁ : A'₁ →+* A₁) (β₁ : B₁ →+* A₁) (π₂ : A'₂ →+* A₂) (β₂ : B₂ →+* A₂)

/-- The map of fibre products induced by a compatible triple. -/
def fibMap (f' : A'₁ →+* A'₂) (f : A₁ →+* A₂) (g : B₁ →+* B₂) (hπ : π₂.comp f' = f.comp π₁)
    (hβ : β₂.comp g = f.comp β₁) : Fib π₁ β₁ →+* Fib π₂ β₂ :=
  RingHom.codRestrict ((RingHom.prodMap g f').comp (incl π₁ β₁)) (fib π₂ β₂) fun z => by
    rw [mem_fib]
    change β₂ (g (pr₁ π₁ β₁ z)) = π₂ (f' (pr₂ π₁ β₁ z))
    rw [← RingHom.comp_apply, hβ, ← RingHom.comp_apply π₂, hπ, RingHom.comp_apply,
      RingHom.comp_apply, pr_comm_apply]

variable {π₁ β₁ π₂ β₂}
variable {f' : A'₁ →+* A'₂} {f : A₁ →+* A₂} {g : B₁ →+* B₂} {hπ : π₂.comp f' = f.comp π₁}
  {hβ : β₂.comp g = f.comp β₁}

@[simp] theorem pr₁_fibMap (z : Fib π₁ β₁) :
    pr₁ π₂ β₂ (fibMap π₁ β₁ π₂ β₂ f' f g hπ hβ z) = g (pr₁ π₁ β₁ z) := rfl

@[simp] theorem pr₂_fibMap (z : Fib π₁ β₁) :
    pr₂ π₂ β₂ (fibMap π₁ β₁ π₂ β₂ f' f g hπ hβ z) = f' (pr₂ π₁ β₁ z) := rfl

theorem pr₁_comp_fibMap :
    (pr₁ π₂ β₂).comp (fibMap π₁ β₁ π₂ β₂ f' f g hπ hβ) = g.comp (pr₁ π₁ β₁) := rfl

theorem pr₂_comp_fibMap :
    (pr₂ π₂ β₂).comp (fibMap π₁ β₁ π₂ β₂ f' f g hπ hβ) = f'.comp (pr₂ π₁ β₁) := rfl

theorem fib_ext {z z' : Fib π₁ β₁} (h₁ : pr₁ π₁ β₁ z = pr₁ π₁ β₁ z')
    (h₂ : pr₂ π₁ β₁ z = pr₂ π₁ β₁ z') : z = z' :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- Ring homs into a fibre product are determined by the two projections. -/
theorem fib_ringHom_ext {R : Type*} [CommRing R] {φ ψ : R →+* Fib π₁ β₁}
    (h₁ : (pr₁ π₁ β₁).comp φ = (pr₁ π₁ β₁).comp ψ) (h₂ : (pr₂ π₁ β₁).comp φ = (pr₂ π₁ β₁).comp ψ) :
    φ = ψ :=
  RingHom.ext fun r => fib_ext (RingHom.congr_fun h₁ r) (RingHom.congr_fun h₂ r)

end Map

section Loc

variable {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B] {π : A' →+* A} {β : B →+* A}
  (h : Fib π β)
  {A'₂ A₂ B₂ : Type u} [CommRing A'₂] [CommRing A₂] [CommRing B₂] (π₂ : A'₂ →+* A₂)
  (β₂ : B₂ →+* A₂) [Algebra A' A'₂] [Algebra A A₂] [Algebra B B₂]
  [IsLocalization.Away (pr₂ π β h) A'₂] [IsLocalization.Away (hbar π β h) A₂]
  [IsLocalization.Away (pr₁ π β h) B₂]
  (hπ : π₂.comp (algebraMap A' A'₂) = (algebraMap A A₂).comp π)
  (hβ : β₂.comp (algebraMap B B₂) = (algebraMap A A₂).comp β)

include hπ in
theorem π₂_h : π₂ (algebraMap A' A'₂ (pr₂ π β h)) = algebraMap A A₂ (hbar π β h) := by
  rw [← RingHom.comp_apply, hπ, RingHom.comp_apply, hbar_eq]

include hβ in
theorem β₂_h : β₂ (algebraMap B B₂ (pr₁ π β h)) = algebraMap A A₂ (hbar π β h) := by
  rw [← RingHom.comp_apply, hβ, RingHom.comp_apply, hbar]

include hπ hβ in
/-- **Localization of the pinching along any models.** -/
theorem isLocalization_fibMap :
    letI := (fibMap π β π₂ β₂ (algebraMap A' A'₂) (algebraMap A A₂) (algebraMap B B₂) hπ
      hβ).toAlgebra
    IsLocalization.Away h (Fib π₂ β₂) := by
  set F := fibMap π β π₂ β₂ (algebraMap A' A'₂) (algebraMap A A₂) (algebraMap B B₂) hπ hβ
  let := F.toAlgebra
  have hu : IsUnit (algebraMap A A₂ (hbar π β h)) := IsLocalization.Away.algebraMap_isUnit _
  have hunit : IsUnit (F h) := by
    have hmem : (IsLocalization.Away.invSelf (S := B₂) (pr₁ π β h),
        IsLocalization.Away.invSelf (S := A'₂) (pr₂ π β h)) ∈ fib π₂ β₂ := by
      rw [mem_fib]
      have u₁ : algebraMap A A₂ (hbar π β h) * β₂
          (IsLocalization.Away.invSelf (pr₁ π β h)) = 1 := by
        rw [← β₂_h h β₂ hβ, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      have u₂ : algebraMap A A₂ (hbar π β h) * π₂
          (IsLocalization.Away.invSelf (pr₂ π β h)) = 1 := by
        rw [← π₂_h h π₂ hπ, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      exact hu.mul_left_cancel (u₁.trans u₂.symm)
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · exact IsLocalization.Away.mul_invSelf (pr₁ π β h)
    · exact IsLocalization.Away.mul_invSelf (pr₂ π β h)
  have cpow₁ : ∀ (z : Fib π₂ β₂) (n : ℕ), (z ^ n).1.1 = z.1.1 ^ n := fun z n => by
    rw [SubmonoidClass.coe_pow, Prod.pow_fst]
  have cpow₂ : ∀ (z : Fib π₂ β₂) (n : ℕ), (z ^ n).1.2 = z.1.2 ^ n := fun z n => by
    rw [SubmonoidClass.coe_pow, Prod.pow_snd]
  refine IsLocalization.Away.mk h hunit ?_ ?_
  · rintro ⟨⟨u, v⟩, huv⟩
    rw [mem_fib] at huv
    obtain ⟨n₁, b, hb⟩ := IsLocalization.Away.surj (pr₁ π β h) u
    obtain ⟨n₂, a, ha⟩ := IsLocalization.Away.surj (pr₂ π β h) v
    set N := n₁ + n₂
    set b' := b * pr₁ π β h ^ n₂
    set a' := a * pr₂ π β h ^ n₁
    have hb' : u * algebraMap B B₂ (pr₁ π β h) ^ N = algebraMap B B₂ b' := by
      simp only [b', N, map_mul, ← hb, map_pow, pow_add]; ring
    have ha' : v * algebraMap A' A'₂ (pr₂ π β h) ^ N = algebraMap A' A'₂ a' := by
      simp only [a', N, map_mul, ← ha, map_pow, pow_add]; ring
    have e₁ := congrArg β₂ hb'
    have e₂ := congrArg π₂ ha'
    rw [map_mul, map_pow, β₂_h h β₂ hβ, ← RingHom.comp_apply β₂, hβ, RingHom.comp_apply] at e₁
    rw [map_mul, map_pow, π₂_h h π₂ hπ, ← RingHom.comp_apply π₂, hπ, RingHom.comp_apply] at e₂
    rw [huv, e₂] at e₁
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (hbar π β h) e₁
    have hmem : (pr₁ π β h ^ m * b', pr₂ π β h ^ m * a') ∈ fib π β := by
      rw [mem_fib]
      simp only [map_mul, map_pow]
      rw [hbar_eq]
      exact hm.symm
    refine ⟨m + N, ⟨_, hmem⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change u * ((F h) ^ (m + N)).1.1 = algebraMap B B₂ (pr₁ π β h ^ m * b')
      rw [cpow₁]
      change u * (algebraMap B B₂ (pr₁ π β h)) ^ (m + N) = _
      rw [map_mul, ← hb', map_pow]; ring
    · change v * ((F h) ^ (m + N)).1.2 = algebraMap A' A'₂ (pr₂ π β h ^ m * a')
      rw [cpow₂]
      change v * (algebraMap A' A'₂ (pr₂ π β h)) ^ (m + N) = _
      rw [map_mul, ← ha', map_pow]; ring
  · intro a b hab
    have h1 := congrArg (fun z : Fib π₂ β₂ => z.1.1) hab
    have h2 := congrArg (fun z : Fib π₂ β₂ => z.1.2) hab
    obtain ⟨n₁, hn₁⟩ := IsLocalization.Away.exists_of_eq (S := B₂) (pr₁ π β h)
      (show algebraMap B B₂ (pr₁ π β a) = algebraMap B B₂ (pr₁ π β b) from h1)
    obtain ⟨n₂, hn₂⟩ := IsLocalization.Away.exists_of_eq (S := A'₂) (pr₂ π β h)
      (show algebraMap A' A'₂ (pr₂ π β a) = algebraMap A' A'₂ (pr₂ π β b) from h2)
    refine ⟨n₁ + n₂, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change pr₁ π β (h ^ (n₁ + n₂) * a) = pr₁ π β (h ^ (n₁ + n₂) * b)
      simp only [map_mul, map_pow, pow_add]
      rw [mul_comm (pr₁ π β h ^ n₁), mul_assoc, hn₁, ← mul_assoc]
    · change pr₂ π β (h ^ (n₁ + n₂) * a) = pr₂ π β (h ^ (n₁ + n₂) * b)
      simp only [map_mul, map_pow, pow_add]
      rw [mul_assoc, hn₂, ← mul_assoc]

include h hπ hβ in
/-- The spectrum of the localized pinching is an open immersion into the pinching. -/
theorem isOpenImmersion_fibMap :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (fibMap π β π₂ β₂ (algebraMap A' A'₂) (algebraMap A A₂) (algebraMap B B₂) hπ hβ))) := by
  let := (fibMap π β π₂ β₂ (algebraMap A' A'₂) (algebraMap A A₂) (algebraMap B B₂) hπ
    hβ).toAlgebra
  have := isLocalization_fibMap h π₂ β₂ hπ hβ
  exact IsOpenImmersion.of_isLocalization (R := Fib π β) (S := Fib π₂ β₂) h

end Loc

#print axioms isLocalization_fibMap
#print axioms isOpenImmersion_fibMap

end Pcf.Examples.PaperP.FerrandPushout
