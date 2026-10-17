/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.Defs

/-!
# Regular schemes: basic API

API for `Pcf.Stacks.SchemeLevel.IsRegularScheme` (Stacks Definition 28.9.1, Tag `02IS`).  Mathlib
at the pin has no notion of a regular scheme.

* `isRegularLocalRing_stalk_of_isRegularRing`, `isRegularRing_of_isRegularLocalRing_stalk`: for
  an affine open `U` with `Γ(X, U)` Noetherian, `Γ(X, U)` is regular iff all stalks at points of
  `U` are regular local rings.
* `isRegularScheme_iff`: Stacks Lemma 28.9.2 (Tag `02IT`), (1) ⇔ (2): `X` is regular iff it is
  locally Noetherian and all its local rings are regular.
* `IsRegularScheme.isRegularRing`: on a regular scheme every affine open has a regular ring of
  sections.
* `IsRegularScheme.of_isOpenImmersion`: an open subscheme of a regular scheme is regular.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Stacks.SchemeLevel

variable {X : Scheme.{u}}

/-- `primeIdealOf` inverts `fromSpec`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.primeIdealOf_fromSpec {U : X.Opens}
    (hU : IsAffineOpen U)
    (p : PrimeSpectrum Γ(X, U)) :
    hU.primeIdealOf ⟨hU.fromSpec p,
      by rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact Set.mem_range_self p⟩ = p :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

/-- On an affine open with regular ring of sections, the local rings are regular. -/
theorem isRegularLocalRing_stalk_of_isRegularRing {U : X.Opens} (hU : IsAffineOpen U)
    [IsRegularRing Γ(X, U)] {x : X} (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  let _ := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
    (X.presheaf.stalk x)).toRingEquiv

/-- On an affine open with Noetherian ring of sections, regularity of all local rings at points
of the open implies regularity of the ring of sections. -/
theorem isRegularRing_of_isRegularLocalRing_stalk {U : X.Opens} (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] (h : ∀ x ∈ U, IsRegularLocalRing (X.presheaf.stalk x)) :
    IsRegularRing Γ(X, U) := by
  rw [isRegularRing_iff]
  intro p hp
  let x : U := ⟨hU.fromSpec ⟨p, hp⟩, by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact Set.mem_range_self _⟩
  have hx : hU.primeIdealOf x = ⟨p, hp⟩ := AlgebraicGeometry.IsAffineOpen.primeIdealOf_fromSpec hU _
  let _ := X.presheaf.algebra_section_stalk x
  have := hU.isLocalization_stalk x
  rw [hx] at this
  have := h x.1 x.2
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (X.presheaf.stalk x.1) (Localization.AtPrime p)).toRingEquiv

/-- The local rings of a regular scheme are regular. -/
theorem IsRegularScheme.isRegularLocalRing_stalk (hX : IsRegularScheme X) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hxU, hreg⟩ := hX x
  exact isRegularLocalRing_stalk_of_isRegularRing U.2 hxU

/-- A regular scheme is locally Noetherian. -/
theorem IsRegularScheme.isLocallyNoetherian (hX : IsRegularScheme X) : IsLocallyNoetherian X := by
  choose U hxU hreg using hX
  refine isLocallyNoetherian_of_affine_cover (S := U) ?_ fun x ↦ by have := hreg x; infer_instance
  exact eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩

/-- **Stacks Lemma 28.9.2 (Tag `02IT`), (1) ⇔ (2).**  A scheme is regular iff it is locally
Noetherian and all its local rings are regular. -/
@[stacks 02IT "(1) ⇔ (2)"]
theorem isRegularScheme_iff :
    IsRegularScheme X ↔
      IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := by
  refine ⟨fun hX ↦ ⟨hX.isLocallyNoetherian, hX.isRegularLocalRing_stalk⟩, ?_⟩
  rintro ⟨hN, hstalk⟩ x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact ⟨⟨U, hU⟩, hxU, isRegularRing_of_isRegularLocalRing_stalk hU fun y _ ↦ hstalk y⟩

/-- On a regular scheme, the ring of sections of every affine open is regular. -/
theorem IsRegularScheme.isRegularRing (hX : IsRegularScheme X) (U : X.affineOpens) :
    IsRegularRing Γ(X, U) := by
  have := hX.isLocallyNoetherian
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  exact isRegularRing_of_isRegularLocalRing_stalk U.2 fun y _ ↦ hX.isRegularLocalRing_stalk y

/-- An open subscheme (more generally, the source of an open immersion) of a regular scheme is
regular. -/
theorem IsRegularScheme.of_isOpenImmersion {Z : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f]
    (hX : IsRegularScheme X) : IsRegularScheme Z := by
  have := hX.isLocallyNoetherian
  refine isRegularScheme_iff.mpr ⟨isLocallyNoetherian_of_isOpenImmersion f, fun z ↦ ?_⟩
  have := hX.isRegularLocalRing_stalk (f z)
  exact IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap z)).commRingCatIsoToRingEquiv

end Pcf.Stacks.SchemeLevel
