/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.Tag0BMBScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# API for the pointwise Stacks morphism properties

`Purity/Tag0BMBScheme.lean` states the Stacks pointwise notions literally:
`IsStacksQuasiFiniteAt` (Definition 29.21.1, `01TD`), `IsStacksUnramifiedAt` (29.36.1, `02G4`) and
`IsStacksEtaleAt` (29.37.1, `02GI`), each as "there are affine opens `x ∈ U`, `V ⊇ f(U)` such that
`𝒪_Y(V) → 𝒪_X(U)` has the ring-map property". This file connects them to Mathlib so that they
can be used, or avoided, by other developments.

## Bridges to Mathlib (the intended entry points)

* `isStacksEtaleAt_iff_exists_etale`: étale at `x` iff `Etale (U.ι ≫ f)` for an open `U ∋ x`.
* `isStacksUnramifiedAt_iff_exists`, `isStacksUnramifiedAt_iff_stalkMap`: unramified at `x` iff
  `LocallyOfFiniteType` and `FormallyUnramified` near `x`, iff locally of finite type near `x`
  with formally unramified stalk map.
* `isStacksQuasiFiniteAt_iff`: quasi-finite at `x` iff locally of finite type near `x` and
  `Scheme.Hom.QuasiFiniteAt f x`; `quasiFiniteAt_iff_appLE` is the converse of Mathlib's
  `Scheme.Hom.QuasiFiniteAt.quasiFiniteAt`.
* Global forms (the remaining clauses of the three tags): `forall_isStacksEtaleAt_iff`
  (`Etale f`), `forall_isStacksUnramifiedAt_iff` (`LocallyOfFiniteType f ∧ FormallyUnramified f`),
  `forall_isStacksQuasiFiniteAt_iff` (`LocallyOfFiniteType f ∧ LocallyQuasiFinite f`).
* `exists_etale_of_zariskiNagataPurity`: Tag `0BMB` with hypotheses and conclusion in Mathlib
  vocabulary, derived from the Stacks-literal `isStacksEtaleAt_of_zariskiNagataPurity`.

## Chart independence and stability

* `HasRingHomProperty.appLE_of_comp_ι`, `HasRingHomProperty.appLE_of_appLE_of_le`,
  `IsStacksEtaleAt.etale_appLE`: once the ring-map property holds on one chart around `x`, it holds
  on every smaller affine chart.
* `isOpen_setOf_isStacksEtaleAt`, `isOpen_setOf_isStacksUnramifiedAt`,
  `isOpen_setOf_isStacksQuasiFiniteAt`: the three loci are open.
* `stacks*At_comp_iff_of_isOpenImmersion`: insensitivity to restriction to opens.
* `IsStacksEtaleAt.isStacksUnramifiedAt`, `IsStacksUnramifiedAt.isStacksQuasiFiniteAt`,
  `IsStacksEtaleAt.isStacksQuasiFiniteAt`.

The generic lemmas in `Pcf.Stacks.HasRingHomProperty` and `Pcf.Stacks.IsZariskiLocalAtSource`
hold for any property of morphisms defined by a local property of ring maps; they are stated so
that they could be upstreamed to Mathlib.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace Pcf.Stacks

section Generic

namespace HasRingHomProperty

variable {P : MorphismProperty Scheme.{u}}
  {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
  [HasRingHomProperty P Q] {X Y : Scheme.{u}} {f : X ⟶ Y}

include Q in
/-- For a property `P` of scheme morphisms defined by the ring-map property `Q`
(`HasRingHomProperty P Q`) and affine opens `W ⊆ X`, `V ⊆ Y` with `f(W) ⊆ V`, the restriction
`f.resLE V W e : W ⟶ V` has `P` iff `𝒪_Y(V) → 𝒪_X(W)` has `Q`. -/
theorem resLE_iff_appLE {V : Y.Opens} (hV : IsAffineOpen V) {W : X.Opens} (hW : IsAffineOpen W)
    (e : W ≤ f ⁻¹ᵁ V) : P (f.resLE V W e) ↔ Q (f.appLE V W e).hom := by
  have : IsAffine V := hV
  have : IsAffine W := hW
  rw [HasRingHomProperty.iff_of_isAffine (P := P)]
  exact (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f V W e)

include Q in
/-- If `P` (local on the target) holds for `f` restricted to an open `W ⊆ X`, it holds for
the corestriction `f.resLE V W e : W ⟶ V` to any open `V ⊇ f(W)`. -/
theorem resLE_of_comp_ι {V : Y.Opens} {W : X.Opens} (e : W ≤ f ⁻¹ᵁ V) (h : P (W.ι ≫ f)) :
    P (f.resLE V W e) := by
  rw [← Scheme.Hom.resLE_comp_ι f e] at h
  have := hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict P
    (fun f U h ↦ IsZariskiLocalAtTarget.restrict h U)
  exact P.of_postcomp (W' := @IsOpenImmersion) _ _ (show IsOpenImmersion V.ι from inferInstance) h

include Q in
/-- For multiplicative `P` with a ring-map description, `P` holds for `W.ι ≫ f` iff it holds
for the corestriction `f.resLE V W e` to an open `V ⊇ f(W)`. -/
theorem comp_ι_iff_resLE [P.IsMultiplicative] {V : Y.Opens} {W : X.Opens}
    (e : W ≤ f ⁻¹ᵁ V) : P (W.ι ≫ f) ↔ P (f.resLE V W e) := by
  refine ⟨resLE_of_comp_ι (P := P) e, fun h ↦ ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact P.comp_mem _ _ h (IsZariskiLocalAtSource.of_isOpenImmersion _)

include Q in
/-- **Independence of chart.** If `P` holds for `f` restricted to an open `U ⊆ X`, then `Q`
holds for `𝒪_Y(V) → 𝒪_X(W)` for *every* pair of affine opens `W ⊆ U`, `V ⊆ Y` with
`f(W) ⊆ V`. -/
theorem appLE_of_comp_ι {U : X.Opens} (hP : P (U.ι ≫ f)) {V : Y.Opens} (hV : IsAffineOpen V)
    {W : X.Opens} (hW : IsAffineOpen W) (hWU : W ≤ U) (e : W ≤ f ⁻¹ᵁ V) :
    Q (f.appLE V W e).hom := by
  rw [← resLE_iff_appLE (P := P) hV hW]
  refine resLE_of_comp_ι (P := P) e ?_
  rw [← X.homOfLE_ι hWU, Category.assoc]
  exact IsZariskiLocalAtSource.comp hP _

include Q in
/-- **The Stacks pointwise definition, in Mathlib vocabulary.** For multiplicative `P`
defined by the ring-map property `Q`, "there are affine opens `x ∈ U`, `V ⊇ f(U)` with
`𝒪_Y(V) → 𝒪_X(U)` satisfying `Q`" (the shape of Stacks Definitions 29.21.1, 29.36.1,
29.37.1) is equivalent to "`f` restricted to some open neighbourhood of `x` has `P`". -/
theorem exists_appLE_iff_exists_comp_ι [P.IsMultiplicative] (x : X) :
    (∃ (U : X.Opens) (_ : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V), x ∈ U ∧ Q (f.appLE V U e).hom) ↔
      ∃ U : X.Opens, x ∈ U ∧ P (U.ι ≫ f) := by
  constructor
  · rintro ⟨U, hU, V, hV, e, hx, h⟩
    exact ⟨U, hx, (comp_ι_iff_resLE (P := P) e).2 ((resLE_iff_appLE (P := P) hV hU e).2 h)⟩
  · rintro ⟨U, hx, h⟩
    obtain ⟨V, hV, hfx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (f x))
    obtain ⟨W, hW, hxW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U ⊓ f ⁻¹ᵁ V from ⟨hx, hfx⟩)
    exact ⟨W, hW, V, hV, hWle.trans inf_le_right, hxW,
      appLE_of_comp_ι (P := P) h hV hW (hWle.trans inf_le_left) _⟩

include Q in
/-- **Independence of chart.** If `𝒪_Y(V) → 𝒪_X(U)` has `Q` for one pair of affine opens
`U ⊆ f⁻¹(V)`, then `𝒪_Y(V') → 𝒪_X(W)` has `Q` for every smaller affine open `W ⊆ U` and every
affine open `V'` with `f(W) ⊆ V'`. -/
theorem appLE_of_appLE_of_le [P.IsMultiplicative] {U : X.Opens} (hU : IsAffineOpen U)
    {V : Y.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) (h : Q (f.appLE V U e).hom)
    {V' : Y.Opens} (hV' : IsAffineOpen V') {W : X.Opens} (hW : IsAffineOpen W) (hWU : W ≤ U)
    (e' : W ≤ f ⁻¹ᵁ V') : Q (f.appLE V' W e').hom :=
  appLE_of_comp_ι (P := P)
    ((comp_ι_iff_resLE (P := P) e).2 ((resLE_iff_appLE (P := P) hV hU e).2 h)) hV' hW hWU e'

end HasRingHomProperty

namespace IsZariskiLocalAtSource

variable {P : MorphismProperty Scheme.{u}} {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A property local on the source holds for `f` iff it holds for `f` restricted to some open
neighbourhood of every point. -/
theorem iff_forall_exists_comp_ι [IsZariskiLocalAtSource P] :
    P f ↔ ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ P (U.ι ≫ f) := by
  refine ⟨fun h x ↦ ⟨⊤, trivial, IsZariskiLocalAtSource.comp h _⟩, fun h ↦ ?_⟩
  choose U hx hU using h
  exact IsZariskiLocalAtSource.of_iSup_eq_top U
    (eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩) hU

/-- The set of points near which `f` has `P` is open. -/
theorem isOpen_setOf_exists_comp_ι :
    IsOpen {x : X | ∃ U : X.Opens, x ∈ U ∧ P (U.ι ≫ f)} :=
  isOpen_iff_forall_mem_open.2 fun _ ⟨U, hx, h⟩ ↦ ⟨U, fun _ hy ↦ ⟨U, hy, h⟩, U.2, hx⟩

/-- For an open immersion `i : Z ⟶ X`, `i ≫ f` has `P` near `z` iff `f` has `P` near
`i z`. -/
theorem exists_comp_ι_comp_iff [IsZariskiLocalAtSource P] {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsOpenImmersion i] (z : Z) :
    (∃ U : Z.Opens, z ∈ U ∧ P (U.ι ≫ i ≫ f)) ↔ ∃ U : X.Opens, i z ∈ U ∧ P (U.ι ≫ f) := by
  constructor
  · rintro ⟨U, hz, h⟩
    refine ⟨i ''ᵁ U, i.apply_mem_image_iff.2 hz, ?_⟩
    have : (i ''ᵁ U).ι = (i.isoImage U).inv ≫ U.ι ≫ i := by
      rw [← Scheme.Hom.isoImage_hom_ι, Iso.inv_hom_id_assoc]
    rw [this, Category.assoc, Category.assoc, P.cancel_left_of_respectsIso]
    simpa using h
  · rintro ⟨U, hz, h⟩
    refine ⟨i ⁻¹ᵁ U, hz, ?_⟩
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι i (le_refl (i ⁻¹ᵁ U)), Category.assoc,
      Scheme.Hom.resLE_eq_morphismRestrict]
    exact IsZariskiLocalAtSource.comp h _

end IsZariskiLocalAtSource

end Generic

section Charts

variable {X Y : Scheme.{u}}

/-- A point `x` of an affine open `U` lies in the basic open `D(r)` when `r` is not in
the prime ideal of `x`. -/
theorem mem_basicOpen_of_notMem_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) {r : Γ(X, U)} (hr : r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    x ∈ X.basicOpen r :=
  (SchemeLevel.mem_basicOpen_iff_notMem_primeIdealOf hU r ⟨x, hx⟩).2 hr

end Charts

section Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- `f` is étale at `x` in the sense of Stacks iff `f` is étale (Mathlib's `Etale`) on
some open neighbourhood of `x`. This is the main bridge for reusers. -/
theorem isStacksEtaleAt_iff_exists_etale (x : X) :
    IsStacksEtaleAt f x ↔ ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) :=
  HasRingHomProperty.exists_appLE_iff_exists_comp_ι (P := @Etale) x

/-- **Independence of chart.** If `f` is étale at `x`, there is an open `U ∋ x` such that
`𝒪_Y(V) → 𝒪_X(W)` is étale for *every* pair of affine opens `W ⊆ U`, `V` with `f(W) ⊆ V`. -/
theorem IsStacksEtaleAt.etale_appLE {x : X} (h : IsStacksEtaleAt f x) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ (V : Y.Opens) (_ : IsAffineOpen V) (W : X.Opens)
      (_ : IsAffineOpen W) (_ : W ≤ U) (e : W ≤ f ⁻¹ᵁ V), (f.appLE V W e).hom.Etale := by
  obtain ⟨U, hx, hU⟩ := (isStacksEtaleAt_iff_exists_etale x).1 h
  exact ⟨U, hx, fun V hV W hW hWU e ↦
    HasRingHomProperty.appLE_of_comp_ι (P := @Etale) hU hV hW hWU e⟩

/-- **Independence of chart.** If `𝒪_Y(V) → 𝒪_X(U)` is étale for one pair of affine opens,
then `𝒪_Y(V') → 𝒪_X(W)` is étale for every smaller affine `W ⊆ U` and any affine `V'` with
`f(W) ⊆ V'`. -/
theorem etale_appLE_of_le {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) (h : (f.appLE V U e).hom.Etale)
    {V' : Y.Opens} (hV' : IsAffineOpen V') {W : X.Opens} (hW : IsAffineOpen W) (hWU : W ≤ U)
    (e' : W ≤ f ⁻¹ᵁ V') : (f.appLE V' W e').hom.Etale :=
  HasRingHomProperty.appLE_of_appLE_of_le (P := @Etale) hU hV e h hV' hW hWU e'

-- Needed (Mathlib v4.35): instance search for `IsZariskiLocalAtSource @Etale` or
-- `(@LocallyOfFiniteType ⊓ @FormallyUnramified).IsMultiplicative` fails without it.
set_option backward.isDefEq.respectTransparency false in
/-- Stacks Definition 29.37.1, second clause: `f` is étale iff it is étale at every point;
in Mathlib this is `Etale f`. -/
@[stacks 02GI "second clause: étale morphism, as Mathlib's `Etale`"]
theorem forall_isStacksEtaleAt_iff : (∀ x, IsStacksEtaleAt f x) ↔ Etale f := by
  simp_rw [isStacksEtaleAt_iff_exists_etale]
  exact (IsZariskiLocalAtSource.iff_forall_exists_comp_ι (P := @Etale)).symm

/-- An étale morphism (Mathlib's `Etale`) is étale at every point. -/
theorem isStacksEtaleAt_of_etale [Etale f] (x : X) : IsStacksEtaleAt f x :=
  forall_isStacksEtaleAt_iff.2 ‹_› x

/-- The étale locus `{x | f is étale at x}` is open. -/
theorem isOpen_setOf_isStacksEtaleAt : IsOpen {x : X | IsStacksEtaleAt f x} := by
  simp_rw [isStacksEtaleAt_iff_exists_etale]
  exact IsZariskiLocalAtSource.isOpen_setOf_exists_comp_ι

-- Needed (Mathlib v4.35): instance search for `IsZariskiLocalAtSource @Etale` or
-- `(@LocallyOfFiniteType ⊓ @FormallyUnramified).IsMultiplicative` fails without it.
set_option backward.isDefEq.respectTransparency false in
/-- Étaleness at a point is insensitive to precomposition with open immersions. -/
theorem isStacksEtaleAt_comp_iff_of_isOpenImmersion {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsOpenImmersion i] (z : Z) : IsStacksEtaleAt (i ≫ f) z ↔ IsStacksEtaleAt f (i z) := by
  rw [isStacksEtaleAt_iff_exists_etale, isStacksEtaleAt_iff_exists_etale]
  exact IsZariskiLocalAtSource.exists_comp_ι_comp_iff (P := @Etale) i z

/-- Restricting `f` to an open `U ⊆ X` does not change étaleness at points of `U`. -/
theorem isStacksEtaleAt_ι_comp_iff (U : X.Opens) (x : U) :
    IsStacksEtaleAt (U.ι ≫ f) x ↔ IsStacksEtaleAt f x.1 :=
  isStacksEtaleAt_comp_iff_of_isOpenImmersion U.ι x

end Etale

section Unramified

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

-- Needed (Mathlib v4.35): instance search for `IsZariskiLocalAtSource @Etale` or
-- `(@LocallyOfFiniteType ⊓ @FormallyUnramified).IsMultiplicative` fails without it.
set_option backward.isDefEq.respectTransparency false in
/-- `f` is unramified at `x` (Stacks) iff on some open neighbourhood of `x` it is locally
of finite type and formally unramified (Mathlib's `LocallyOfFiniteType`,
`FormallyUnramified`). -/
theorem isStacksUnramifiedAt_iff_exists (x : X) :
    IsStacksUnramifiedAt f x ↔
      ∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧ FormallyUnramified (U.ι ≫ f) := by
  have := HasRingHomProperty.inf (P := @LocallyOfFiniteType) (P' := @FormallyUnramified)
  exact HasRingHomProperty.exists_appLE_iff_exists_comp_ι
    (P := @LocallyOfFiniteType ⊓ @FormallyUnramified) x

/-- Stacks Definition 29.36.1, third clause: `f` is unramified iff it is unramified at every
point; in Mathlib this is `LocallyOfFiniteType f ∧ FormallyUnramified f`. -/
@[stacks 02G4 "third clause: unramified morphism, as Mathlib's `LocallyOfFiniteType` and \
  `FormallyUnramified`"]
theorem forall_isStacksUnramifiedAt_iff :
    (∀ x, IsStacksUnramifiedAt f x) ↔ LocallyOfFiniteType f ∧ FormallyUnramified f := by
  have := HasRingHomProperty.inf (P := @LocallyOfFiniteType) (P' := @FormallyUnramified)
  simp_rw [isStacksUnramifiedAt_iff_exists]
  exact (IsZariskiLocalAtSource.iff_forall_exists_comp_ι
    (P := @LocallyOfFiniteType ⊓ @FormallyUnramified)).symm

/-- The unramified locus `{x | f is unramified at x}` is open. -/
theorem isOpen_setOf_isStacksUnramifiedAt : IsOpen {x : X | IsStacksUnramifiedAt f x} := by
  simp_rw [isStacksUnramifiedAt_iff_exists]
  exact IsZariskiLocalAtSource.isOpen_setOf_exists_comp_ι
    (P := @LocallyOfFiniteType ⊓ @FormallyUnramified)

/-- Unramifiedness at a point is insensitive to precomposition with open immersions. -/
theorem isStacksUnramifiedAt_comp_iff_of_isOpenImmersion {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsOpenImmersion i] (z : Z) :
    IsStacksUnramifiedAt (i ≫ f) z ↔ IsStacksUnramifiedAt f (i z) := by
  have := HasRingHomProperty.inf (P := @LocallyOfFiniteType) (P' := @FormallyUnramified)
  rw [isStacksUnramifiedAt_iff_exists, isStacksUnramifiedAt_iff_exists]
  exact IsZariskiLocalAtSource.exists_comp_ι_comp_iff
    (P := @LocallyOfFiniteType ⊓ @FormallyUnramified) i z

/-- **Stalk criterion.** `f` is unramified at `x` iff `f` is locally of finite type near `x`
and the stalk map `𝒪_{Y,f x} → 𝒪_{X,x}` is formally unramified. -/
theorem isStacksUnramifiedAt_iff_stalkMap (x : X) :
    IsStacksUnramifiedAt f x ↔ (∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f)) ∧
      (f.stalkMap x).hom.FormallyUnramified := by
  constructor
  · intro h
    obtain ⟨U, hx, hU, -⟩ := (isStacksUnramifiedAt_iff_exists x).1 h
    exact ⟨⟨U, hx, hU⟩, formallyUnramified_stalkMap_of_isStacksUnramifiedAt h⟩
  · rintro ⟨⟨U, hxU, hU⟩, hst⟩
    obtain ⟨V, hV, hfx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (f x))
    obtain ⟨W, hW, hxW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X.isBasis_affineOpens (show x ∈ U ⊓ f ⁻¹ᵁ V from ⟨hxU, hfx⟩)
    have e : W ≤ f ⁻¹ᵁ V := hWle.trans inf_le_right
    have hft : (f.appLE V W e).hom.FiniteType :=
      HasRingHomProperty.appLE_of_comp_ι (P := @LocallyOfFiniteType) hU hV hW
        (hWle.trans inf_le_left) e
    algebraize [(f.appLE V W e).hom]
    rw [formallyUnramified_stalkMap_iff V hV W hW e hxW] at hst
    obtain ⟨r, hr, hun⟩ :=
      Algebra.exists_unramified_of_isUnramifiedAt (R := Γ(Y, V)) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
    refine ⟨_, hW.basicOpen r, V, hV, (X.basicOpen_le r).trans e,
      mem_basicOpen_of_notMem_primeIdealOf hW hxW hr, ?_, ?_⟩
    · refine appLE_basicOpen_of_away RingHom.finiteType_respectsIso hW e r ?_
      rw [RingHom.finiteType_algebraMap]
      exact hun.finiteType
    · refine appLE_basicOpen_of_away RingHom.FormallyUnramified.respectsIso hW e r ?_
      rw [RingHom.formallyUnramified_algebraMap]
      exact hun.formallyUnramified

/-- Étale at `x` implies unramified at `x`. -/
theorem IsStacksEtaleAt.isStacksUnramifiedAt {x : X} (h : IsStacksEtaleAt f x) :
    IsStacksUnramifiedAt f x := by
  obtain ⟨U, hx, hU⟩ := (isStacksEtaleAt_iff_exists_etale x).1 h
  exact (isStacksUnramifiedAt_iff_exists x).2 ⟨U, hx, inferInstance, inferInstance⟩

end Unramified

section QuasiFinite

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- For affine opens `x ∈ U`, `V ⊇ f(U)`, Mathlib's `f.QuasiFiniteAt x` (the stalk map is
quasi-finite) is equivalent to `𝒪_Y(V) → 𝒪_X(U)` being quasi-finite at the prime of `x`.
Mathlib has the forward direction (`Scheme.Hom.QuasiFiniteAt.quasiFiniteAt`). -/
theorem quasiFiniteAt_iff_appLE {x : X} (V : Y.Opens) (hV : IsAffineOpen V) (U : X.Opens)
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U) :
    f.QuasiFiniteAt x ↔ (f.appLE V U e).hom.QuasiFiniteAt (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  refine ⟨fun h ↦ h.quasiFiniteAt hU hV e hx, fun h ↦ ?_⟩
  algebraize [(f.appLE V U e).hom]
  let p := (hV.primeIdealOf ⟨f x, e hx⟩).asIdeal
  let q := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.QuasiFinite Γ(Y, V) (Localization.AtPrime q) := h
  have : Algebra.QuasiFinite (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_restrictScalars Γ(Y, V) _ _
  exact (RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
    (IsAffineOpen.arrowStalkMapIso f V hV U hU e hx)).2
    (RingHom.quasiFinite_algebraMap.2 this)

/-- `f` is quasi-finite at `x` (Stacks) iff `f` is locally of finite type near `x` and
quasi-finite at `x` in Mathlib's stalk sense (`Scheme.Hom.QuasiFiniteAt`). -/
theorem isStacksQuasiFiniteAt_iff (x : X) :
    IsStacksQuasiFiniteAt f x ↔
      (∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f)) ∧ f.QuasiFiniteAt x := by
  constructor
  · rintro ⟨U, hU, V, hV, e, hx, hft, hqf⟩
    exact ⟨(HasRingHomProperty.exists_appLE_iff_exists_comp_ι (P := @LocallyOfFiniteType) x).1
      ⟨U, hU, V, hV, e, hx, hft⟩, (quasiFiniteAt_iff_appLE V hV U hU e hx).2 hqf⟩
  · rintro ⟨⟨U, hxU, hU⟩, hqf⟩
    obtain ⟨V, hV, hfx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (f x))
    obtain ⟨W, hW, hxW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X.isBasis_affineOpens (show x ∈ U ⊓ f ⁻¹ᵁ V from ⟨hxU, hfx⟩)
    have e : W ≤ f ⁻¹ᵁ V := hWle.trans inf_le_right
    exact ⟨W, hW, V, hV, e, hxW,
      HasRingHomProperty.appLE_of_comp_ι (P := @LocallyOfFiniteType) hU hV hW
        (hWle.trans inf_le_left) e,
      hqf.quasiFiniteAt hW hV e hxW⟩

-- Needed (Mathlib v4.35): instance search for `IsZariskiLocalAtSource @Etale` or
-- `(@LocallyOfFiniteType ⊓ @FormallyUnramified).IsMultiplicative` fails without it.
set_option backward.isDefEq.respectTransparency false in
/-- For `f` locally of finite type, Stacks' quasi-finiteness at `x` is exactly Mathlib's
`f.QuasiFiniteAt x`. -/
theorem isStacksQuasiFiniteAt_iff_quasiFiniteAt [LocallyOfFiniteType f] (x : X) :
    IsStacksQuasiFiniteAt f x ↔ f.QuasiFiniteAt x := by
  rw [isStacksQuasiFiniteAt_iff]
  exact and_iff_right ⟨⊤, trivial, IsZariskiLocalAtSource.comp ‹_› _⟩

-- Needed (Mathlib v4.35): instance search for `IsZariskiLocalAtSource @Etale` or
-- `(@LocallyOfFiniteType ⊓ @FormallyUnramified).IsMultiplicative` fails without it.
set_option backward.isDefEq.respectTransparency false in
/-- Stacks Definition 29.21.1, second clause: `f` is locally quasi-finite iff it is
quasi-finite at every point. Mathlib's `LocallyQuasiFinite` omits the finite-type condition, so
the Stacks notion is `LocallyOfFiniteType f ∧ LocallyQuasiFinite f`. -/
@[stacks 01TD "second clause: locally quasi-finite, as Mathlib's `LocallyOfFiniteType` and \
  `LocallyQuasiFinite`"]
theorem forall_isStacksQuasiFiniteAt_iff :
    (∀ x, IsStacksQuasiFiniteAt f x) ↔ LocallyOfFiniteType f ∧ LocallyQuasiFinite f := by
  simp_rw [isStacksQuasiFiniteAt_iff]
  constructor
  · intro h
    have : LocallyOfFiniteType f :=
      IsZariskiLocalAtSource.iff_forall_exists_comp_ι.2 fun x ↦ (h x).1
    exact ⟨this, f.quasiFiniteLocus_eq_top_iff.1 (top_le_iff.1 fun x _ ↦ (h x).2)⟩
  · rintro ⟨h₁, h₂⟩ x
    exact ⟨⟨⊤, trivial, IsZariskiLocalAtSource.comp h₁ _⟩, f.quasiFiniteAt x⟩

/-- Unramified at `x` implies quasi-finite at `x`. -/
theorem IsStacksUnramifiedAt.isStacksQuasiFiniteAt {x : X} (h : IsStacksUnramifiedAt f x) :
    IsStacksQuasiFiniteAt f x := by
  obtain ⟨U, hU, V, hV, e, hx, hft, hfu⟩ := h
  refine ⟨U, hU, V, hV, e, hx, hft, ?_⟩
  algebraize [(f.appLE V U e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite Γ(Y, V) (Localization.AtPrime _))

/-- Étale at `x` implies quasi-finite at `x`. -/
theorem IsStacksEtaleAt.isStacksQuasiFiniteAt {x : X} (h : IsStacksEtaleAt f x) :
    IsStacksQuasiFiniteAt f x :=
  h.isStacksUnramifiedAt.isStacksQuasiFiniteAt

/-- The quasi-finite locus `{x | f is quasi-finite at x}` is open (via Mathlib's
`Scheme.Hom.isOpen_quasiFiniteAt`, a consequence of Zariski's main theorem). -/
theorem isOpen_setOf_isStacksQuasiFiniteAt : IsOpen {x : X | IsStacksQuasiFiniteAt f x} := by
  simp_rw [isStacksQuasiFiniteAt_iff]
  refine isOpen_iff_forall_mem_open.2 fun x ⟨⟨U, hxU, hU⟩, hx⟩ ↦
    ⟨U.ι '' {y | (U.ι ≫ f).QuasiFiniteAt y}, ?_,
      U.ι.isOpenEmbedding.isOpenMap _ (U.ι ≫ f).isOpen_quasiFiniteAt, ⟨x, hxU⟩, ?_, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨U, y.2, hU⟩, Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.1 hy⟩
  · exact Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.2 hx

-- Needed (Mathlib v4.35): instance search for `IsZariskiLocalAtSource @Etale` or
-- `(@LocallyOfFiniteType ⊓ @FormallyUnramified).IsMultiplicative` fails without it.
set_option backward.isDefEq.respectTransparency false in
/-- Quasi-finiteness at a point is insensitive to precomposition with open immersions. -/
theorem isStacksQuasiFiniteAt_comp_iff_of_isOpenImmersion {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsOpenImmersion i] (z : Z) :
    IsStacksQuasiFiniteAt (i ≫ f) z ↔ IsStacksQuasiFiniteAt f (i z) := by
  rw [isStacksQuasiFiniteAt_iff, isStacksQuasiFiniteAt_iff,
    IsZariskiLocalAtSource.exists_comp_ι_comp_iff (P := @LocallyOfFiniteType) i z,
    Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion]

end QuasiFinite

section Purity

variable {X Y : Scheme.{u}}

/-- **Purity of branch locus (Stacks Lemma 58.21.4, Tag `0BMB`), in Mathlib vocabulary.**

Let `f : X ⟶ Y` be a morphism of locally Noetherian schemes and `x ∈ X`. Assume `𝒪_{X,x}` is a
normal domain, `𝒪_{Y,f x}` is regular, `f` is locally of finite type near `x` and quasi-finite at
`x` (`Scheme.Hom.QuasiFiniteAt`), `dim 𝒪_{X,x} = dim 𝒪_{Y,f x} ≥ 1`, and the stalk map of `f` is
formally unramified at every specialization `x' ⤳ x` with `dim 𝒪_{X,x'} = 1`. Then `f` is
étale (`Etale`) on an open neighbourhood of `x`.

This is `isStacksEtaleAt_of_zariskiNagataPurity` (the Stacks-literal statement, which also
carries the tag) transported along the bridges of this file; it is the form intended for reuse. -/
@[stacks 0BMB "Mathlib vocabulary: normal domain stalk, stalkwise formally unramified, \
  conclusion Etale on a neighbourhood"]
theorem exists_etale_of_zariskiNagataPurity [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (x : X) [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    (hft : ∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f)) (hqf : f.QuasiFiniteAt x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hpos : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
      (f.stalkMap x').hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  obtain ⟨U, hxU, hU⟩ := hft
  rw [← isStacksEtaleAt_iff_exists_etale]
  exact isStacksEtaleAt_of_zariskiNagataPurity f x IsStacksNormalRing.of_isDomain ‹_›
    ((isStacksQuasiFiniteAt_iff x).2 ⟨⟨U, hxU, hU⟩, hqf⟩) hdim hpos fun x' hx' h1 ↦
      (isStacksUnramifiedAt_iff_stalkMap x').2 ⟨⟨U, hx'.mem_open U.2 hxU, hU⟩, hunr x' hx' h1⟩

-- Needed (Mathlib v4.35): instance search for `IsZariskiLocalAtSource @Etale` or
-- `(@LocallyOfFiniteType ⊓ @FormallyUnramified).IsMultiplicative` fails without it.
set_option backward.isDefEq.respectTransparency false in
/-- Purity of branch locus (Tag `0BMB`) for `f` locally of finite type, in Mathlib
vocabulary: see `exists_etale_of_zariskiNagataPurity`. -/
theorem exists_etale_of_zariskiNagataPurity_of_locallyOfFiniteType [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsRegularLocalRing (Y.presheaf.stalk (f x))] (hqf : f.QuasiFiniteAt x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hpos : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
      (f.stalkMap x').hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) :=
  exists_etale_of_zariskiNagataPurity f x ⟨⊤, trivial, IsZariskiLocalAtSource.comp ‹_› _⟩ hqf
    hdim hpos hunr

end Purity

end Pcf.Stacks
