/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Pcf.Stacks.Purity.Tag0BMA
public import Pcf.Stacks.Common.AffineBasicOpen

/-!
# Zariski--Nagata purity at the scheme level (Stacks Tag `0BMB`)

Stacks Lemma 58.21.4 (`0BMB`, purity of branch locus): let `f : X → Y` be a morphism of locally
Noetherian schemes, `x ∈ X`, `y = f(x)`, with `𝒪_{X,x}` normal, `𝒪_{Y,y}` regular, `f`
quasi-finite at `x`, `dim 𝒪_{X,x} = dim 𝒪_{Y,y} ≥ 1`, and `f` unramified at every specialization
`x' ⤳ x` with `dim 𝒪_{X,x'} = 1`. Then `f` is étale at `x`.

## The pointwise notions

Mathlib at the pin has no scheme-level "unramified at a point" or "étale at a point", and its
`Scheme.Hom.QuasiFiniteAt` (quasi-finiteness of the stalk map) omits the finite-type condition of
Stacks. This file therefore states the three Stacks definitions literally, as existence of affine
opens `x ∈ U ⊆ X`, `V ⊆ Y` with `f(U) ⊆ V` such that the ring map `𝒪_Y(V) → 𝒪_X(U)`
(`f.appLE V U _`) has the relevant property:

* `StacksQuasiFiniteAt` — Definition 29.21.1(1) (Tag `01TD`): of finite type and quasi-finite at
  the prime of `x`. Quasi-finiteness at a prime is Mathlib's `RingHom.QuasiFiniteAt` (the
  localization is quasi-finite), the same encoding as the ring-level `ZariskiNagataPurityInputsAt`.
  For finite-type ring maps it is equivalent to Stacks' Definition 10.122.3 ("isolated in its
  fibre"); Mathlib proves the scheme form of this equivalence as
  `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber` (this file does not restate it).
* `StacksUnramifiedAt` — Definition 29.36.1(1) (Tag `02G4`): the ring map is unramified, i.e. of
  finite type with `Ω = 0` (`RingHom.FiniteType` and `RingHom.FormallyUnramified`).
* `StacksEtaleAt` — Definition 29.37.1(1) (Tag `02GI`): the ring map is étale (`RingHom.Etale`: of
  finite presentation and formally étale; Stacks Definition 10.143.1 asks for finite presentation
  with `H₁(NL) = 0` and `Ω = 0`, which is formal étaleness by Mathlib's
  `Algebra.formallyEtale_iff`).

"Normal" for `𝒪_{X,x}` is `IsStacksNormalRing` (Stacks Definition 10.37.11, `00GV`), "regular"
is `IsRegularLocalRing`, and `dim` is `ringKrullDim`.

## Proof

The proof reduces to the affine pointwise theorem `Pcf.Stacks.zariskiNagataPurity`
(`Purity/Tag0BMA.lean`). The affine opens supplied by quasi-finiteness at `x` give a
finite-type map `R = 𝒪_Y(V) → A = 𝒪_X(U)` of Noetherian rings; stalks are localizations of
`A` and `R` at the corresponding primes (`IsAffineOpen.isLocalization_stalk`), which transports
normality, regularity, and dimensions (heights); unramifiedness at codimension-one
specializations is transported through the stalk maps (`formallyUnramified_stalkMap_iff`);
finally the affine conclusion `Algebra.IsEtaleAt R w` spreads out to a basic open
`D(g) ∋ x` with `R → A_g` étale (`Algebra.exists_etale_of_isEtaleAt`).

**Divergence of the proof route from Stacks.** Stacks proves `0BMB` by induction on
`d = dim 𝒪_{X,x}` directly on schemes, localizing étale-locally on base and target (Descent
`35.23.31`, `35.31.1`, More on Morphisms `37.41.1`). Here the scheme statement is instead reduced
Zariski-locally to the affine theorem, whose proof carries out that induction at the ring level
(`zariskiNagataPurity_of_inputs`, with the étale localization done through the algebra form
`00UJ`; see `Purity/Tag0BMB.lean` and `Purity/Tag0BMBLocalModel.lean`).
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace Pcf.Stacks

variable {X Y : Scheme.{u}}

/-- **Quasi-finite at a point**, Stacks Definition 29.21.1(1) (Tag `01TD`): there are affine opens
`x ∈ U ⊆ X` and `V ⊆ Y` with `f(U) ⊆ V` such that `𝒪_Y(V) → 𝒪_X(U)` is of finite type and
quasi-finite at the prime corresponding to `x`. Tag `01TD` also defines locally quasi-finite and
quasi-finite morphisms; only the first clause, quasi-finite at `x`, is formalized here. -/
@[stacks 01TD "first clause: quasi-finite at a point"]
def StacksQuasiFiniteAt (f : X ⟶ Y) (x : X) : Prop :=
  ∃ (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U),
    (f.appLE V U hUV).hom.FiniteType ∧
      (f.appLE V U hUV).hom.QuasiFiniteAt (hU.primeIdealOf ⟨x, hx⟩).asIdeal

/-- **Unramified at a point**, Stacks Definition 29.36.1(1): there are affine opens `x ∈ U ⊆ X`
and `V ⊆ Y` with `f(U) ⊆ V` such that `𝒪_Y(V) → 𝒪_X(U)` is unramified, i.e. of finite type with
vanishing module of differentials (Stacks Definition 10.151.1, Tag `00UT`; vanishing of `Ω` is
`RingHom.FormallyUnramified`). Tag `02G4` also defines G-unramified at `x` and unramified
morphisms; only the first clause, unramified at `x`, is formalized here. -/
@[stacks 02G4 "first clause: unramified at a point"]
def StacksUnramifiedAt (f : X ⟶ Y) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V), x ∈ U ∧
    (f.appLE V U hUV).hom.FiniteType ∧ (f.appLE V U hUV).hom.FormallyUnramified

/-- **Étale at a point**, Stacks Definition 29.37.1(1): there are affine opens `x ∈ U ⊆ X` and
`V ⊆ Y` with `f(U) ⊆ V` such that `𝒪_Y(V) → 𝒪_X(U)` is étale. Tag `02GI` also defines étale
and standard étale morphisms; only the first clause, étale at `x`, is formalized here. -/
@[stacks 02GI "first clause: étale at a point"]
def StacksEtaleAt (f : X ⟶ Y) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V), x ∈ U ∧ (f.appLE V U hUV).hom.Etale

/-- A Stacks-normal local ring is a normal domain. -/
theorem IsStacksNormalRing.isDomain_isIntegrallyClosed_of_isLocalRing
    (R : Type*) [CommRing R] [IsLocalRing R] (h : IsStacksNormalRing R) :
    IsDomain R ∧ IsIntegrallyClosed R := by
  let m := IsLocalRing.maximalIdeal R
  let e : R ≃ₐ[R] Localization.AtPrime m :=
    IsLocalization.atUnits R m.primeCompl
      (fun y hy ↦ by
        simpa [m, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsUnit.mem_submonoid_iff]
          using hy)
  obtain ⟨h₁, h₂⟩ := h ⟨m, inferInstance⟩
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv.symm⟩

/-- For affine opens `x ∈ V ⊆ f⁻¹(U)`, the stalk map of `f` at `x` is formally unramified iff
`𝒪_Y(U) → 𝒪_X(V)` is unramified at the prime of `x`. -/
theorem formallyUnramified_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyUnramified ↔
      Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyUnramified_algebraMap]
    exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · constructor
    · intro _
      have : Algebra.FormallyEtale Γ(Y, U) (Localization.AtPrime p) :=
        .of_isLocalization p.primeCompl
      exact Algebra.FormallyUnramified.comp Γ(Y, U) (Localization.AtPrime p) _
    · intro _
      exact .of_restrictScalars Γ(Y, U) _ _

/-- If `f` is unramified at `x` (Stacks sense), its stalk map at `x` is formally unramified. -/
theorem formallyUnramified_stalkMap_of_stacksUnramifiedAt {f : X ⟶ Y} {x : X}
    (h : StacksUnramifiedAt f x) : (f.stalkMap x).hom.FormallyUnramified := by
  obtain ⟨U, hU, V, hV, hUV, hx, -, hfu⟩ := h
  algebraize [(f.appLE V U hUV).hom]
  rw [formallyUnramified_stalkMap_iff V hV U hU hUV hx]
  have : Algebra.FormallyEtale Γ(X, U) (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :=
    .of_isLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  exact Algebra.FormallyUnramified.comp Γ(Y, V) Γ(X, U) _

-- Both options are needed (Mathlib v4.35): without them the final `simp only [..., appLE_map]`
-- does not close the goal; Mathlib uses the same `… in` options in `AlgebraicGeometry`.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Spreading out to a basic open: if `𝒪_Y(V) → 𝒪_X(U)_r` has the (isomorphism-invariant)
property `Q`, then so does `𝒪_Y(V) → 𝒪_X(D(r))`. -/
theorem appLE_basicOpen_of_away
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.RespectsIso Q) {f : X ⟶ Y} {U : X.Opens} (hU : IsAffineOpen U)
    {V : Y.Opens} (hUV : U ≤ f ⁻¹ᵁ V) (r : Γ(X, U))
    (h : letI := (f.appLE V U hUV).hom.toAlgebra
      Q (algebraMap Γ(Y, V) (Localization.Away r))) :
    Q (f.appLE V (X.basicOpen r) ((X.basicOpen_le r).trans hUV)).hom := by
  algebraize [(f.appLE V U hUV).hom]
  have := hU.isLocalization_basicOpen r
  convert hQ.1 _ (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv h
  ext
  dsimp
  simp only [IsScalarTower.algebraMap_apply Γ(Y, V) Γ(X, U) (Localization _),
    IsLocalization.map_eq]
  simp only [RingHom.algebraMap_toAlgebra, RingHomCompTriple.comp_apply,
    ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

/-- If `𝒪_Y(V) → 𝒪_X(U)` is of finite presentation and étale at the prime of `x`, then `f` is
étale at `x` in the sense of Stacks: it is étale on some basic open `D(g) ∋ x` of `U`. -/
theorem stacksEtaleAt_of_isEtaleAt {f : X ⟶ Y} {x : X} (U : X.Opens) (hU : IsAffineOpen U)
    (V : Y.Opens) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U)
    (hfp : (f.appLE V U hUV).hom.FinitePresentation)
    (h : letI := (f.appLE V U hUV).hom.toAlgebra
      Algebra.IsEtaleAt Γ(Y, V) (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    StacksEtaleAt f x := by
  algebraize [(f.appLE V U hUV).hom]
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_etale_of_isEtaleAt (R := Γ(Y, V))
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  refine ⟨_, hU.basicOpen r, V, hV, (X.basicOpen_le r).trans hUV, ?_, ?_⟩
  · exact (SchemeLevel.mem_basicOpen_iff_notMem_primeIdealOf hU r ⟨x, hx⟩).2 hrx
  · rw [← RingHom.etale_algebraMap] at hr
    exact appLE_basicOpen_of_away RingHom.Etale.respectsIso hU hUV r hr

/-- Regularity of `R_I` only depends on the prime ideal `I`. -/
theorem isRegularLocalRing_atPrime_of_eq {R : Type*} [CommRing R] {I J : Ideal R}
    [I.IsPrime] [J.IsPrime] (h : I = J) [IsRegularLocalRing (Localization.AtPrime J)] :
    IsRegularLocalRing (Localization.AtPrime I) := by
  subst h
  assumption

-- Needed (Mathlib v4.35): without it the `IsLocalization.AtPrime` instance for the stalk at
-- `hU.fromSpec w'` is not found.
set_option backward.isDefEq.respectTransparency false in
/-- **Purity of branch locus, Stacks Lemma 58.21.4 (Tag `0BMB`).**

Let `f : X ⟶ Y` be a morphism of locally Noetherian schemes and `x ∈ X`, `y = f x`. Assume
`𝒪_{X,x}` is normal, `𝒪_{Y,y}` is regular, `f` is quasi-finite at `x`,
`dim 𝒪_{X,x} = dim 𝒪_{Y,y} ≥ 1`, and `f` is unramified at every specialization `x' ⤳ x` with
`dim 𝒪_{X,x'} = 1`. Then `f` is étale at `x`.

The pointwise notions are the literal Stacks definitions `StacksQuasiFiniteAt` (29.21.1),
`StacksUnramifiedAt` (29.36.1), `StacksEtaleAt` (29.37.1); normality is `IsStacksNormalRing`
(10.37.11) and `dim` is `ringKrullDim`.

**Proof route (diverges from Stacks).** Stacks argues by induction on `d` directly on schemes,
working étale-locally on base and target (Descent `35.23.31`, `35.31.1`; More on Morphisms
`37.41.1`), base changing to `Spec 𝒪_{Y,y}`, and concluding with `0BMA`. Here the statement is
reduced Zariski-locally to the affine pointwise theorem `Pcf.Stacks.zariskiNagataPurity`,
whose own proof runs the Stacks induction at the ring level:

1. quasi-finiteness at `x` provides affine opens `x ∈ U`, `V ⊇ f(U)` with
   `R = 𝒪_Y(V) → A = 𝒪_X(U)` of finite type; `R`, `A` are Noetherian (`IsLocallyNoetherian`);
2. stalks are localizations at the primes `w` of `x` and `w ∩ R` of `y`
   (`IsAffineOpen.isLocalization_stalk`, `IsAffineOpen.comap_primeIdealOf_appLE`), which
   transports normality, regularity and the dimensions (`ringKrullDim_eq_height`);
3. a height-one generization `w'` of `w` is a point `x' ⤳ x` of `U` with `dim 𝒪_{X,x'} = 1`,
   and unramifiedness at `x'` passes through the stalk map
   (`formallyUnramified_stalkMap_iff`);
4. `Pcf.Stacks.zariskiNagataPurity` gives `Algebra.IsEtaleAt R w`, which spreads out to a basic
   open neighbourhood of `x` (`stacksEtaleAt_of_isEtaleAt`). -/
@[stacks 0BMB]
theorem stacksEtaleAt_of_zariskiNagataPurity [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (x : X)
    (hnormal : IsStacksNormalRing (X.presheaf.stalk x))
    (hregular : IsRegularLocalRing (Y.presheaf.stalk (f x)))
    (hqf : StacksQuasiFiniteAt f x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hpos : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
      StacksUnramifiedAt f x') :
    StacksEtaleAt f x := by
  obtain ⟨U, hU, V, hV, hUV, hx, hft, hqfat⟩ := hqf
  algebraize [(f.appLE V U hUV).hom]
  have hR : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hA : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  set w := hU.primeIdealOf ⟨x, hx⟩ with hw_def
  have hw : w.asIdeal.under Γ(Y, V) = (hV.primeIdealOf ⟨f x, hUV hx⟩).asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hx).1)
  -- Step 2: stalks as localizations.
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  let := Y.presheaf.algebra_section_stalk ⟨f x, hUV hx⟩
  have := hV.isLocalization_stalk ⟨f x, hUV hx⟩
  let eX := IsLocalization.algEquiv w.asIdeal.primeCompl (X.presheaf.stalk x)
    (Localization.AtPrime w.asIdeal)
  let eY := IsLocalization.algEquiv (hV.primeIdealOf ⟨f x, hUV hx⟩).asIdeal.primeCompl
    (Y.presheaf.stalk (f x)) (Localization.AtPrime (hV.primeIdealOf ⟨f x, hUV hx⟩).asIdeal)
  obtain ⟨hdom, hic⟩ :=
    IsStacksNormalRing.isDomain_isIntegrallyClosed_of_isLocalRing _ hnormal
  have hdimX : ringKrullDim (X.presheaf.stalk x) = w.asIdeal.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height w.asIdeal _
  have hdimY : ringKrullDim (Y.presheaf.stalk (f x)) = (w.asIdeal.under Γ(Y, V)).height := by
    rw [hw]
    exact IsLocalization.AtPrime.ringKrullDim_eq_height _ _
  have hregY : IsRegularLocalRing
      (Localization.AtPrime (hV.primeIdealOf ⟨f x, hUV hx⟩).asIdeal) :=
    IsRegularLocalRing.of_ringEquiv eY.toRingEquiv
  have inputs : ZariskiNagataPurityInputsAt Γ(Y, V) Γ(X, U) w :=
    { source_isDomain := eX.symm.toMulEquiv.isDomain _
      source_isIntegrallyClosed := IsIntegrallyClosed.of_equiv eX.toRingEquiv
      target_isRegular := isRegularLocalRing_atPrime_of_eq hw
      quasiFinite := hqfat
      equalDimension := by
        have := hdimX.symm.trans (hdim.trans hdimY)
        exact_mod_cast this
      positiveDimension := by
        rw [hdimX] at hpos
        exact_mod_cast hpos
      unramifiedCodimensionOne := by
        -- Step 3: codimension-one generizations.
        intro w' hw'w hw'1
        have hx' : hU.fromSpec w' ∈ U := by
          change hU.fromSpec w' ∈ (U : Set X)
          rw [← hU.range_fromSpec]
          exact ⟨w', rfl⟩
        have hspec : hU.fromSpec w' ⤳ x := by
          have := hw'w.map hU.fromSpec.continuous
          rwa [hw_def, hU.fromSpec_primeIdealOf] at this
        have hdim' : ringKrullDim (X.presheaf.stalk (hU.fromSpec w')) = 1 := by
          let := X.presheaf.algebra_section_stalk ⟨hU.fromSpec w', hx'⟩
          have := hU.isLocalization_stalk' w' hx'
          rw [IsLocalization.AtPrime.ringKrullDim_eq_height w'.asIdeal, hw'1]
          rfl
        have hst := formallyUnramified_stalkMap_of_stacksUnramifiedAt (hunr _ hspec hdim')
        rw [formallyUnramified_stalkMap_iff V hV U hU hUV hx'] at hst
        have hpt : hU.primeIdealOf ⟨hU.fromSpec w', hx'⟩ = w' :=
          hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨_, hx'⟩)
        rwa [hpt] at hst }
  -- Step 4: the affine theorem and spreading out.
  have hetale := zariskiNagataPurity Γ(Y, V) Γ(X, U) hR hA hft w inputs
  exact stacksEtaleAt_of_isEtaleAt U hU V hV hUV hx
    (RingHom.FinitePresentation.of_finiteType.mp hft) hetale

end Pcf.Stacks
