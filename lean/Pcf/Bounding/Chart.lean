/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.Stacks
import Pcf.Bounding.StandardPiece
import Pcf.Bounding.LocalStructure
import Pcf.Bounding.Pieces
import Pcf.Bounding.Reduced
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Theorem `thm:bounding`, derived on an affine chart

This file **derives** the conclusion of Theorem `thm:bounding` of `latex/paper.tex` from
Zariski–Nagata purity and Abhyankar's lemma, following Steps 0–4 of the manuscript's proof.
Until this file, the formalization *assumed* that conclusion (`Pcf.PcfSetup.key`,
`Pcf.PcfSetup1.key1`, and — in a disguised form caught by two adversarial reviews — the
`KummerWitness`-valued field `standardForm`). Here it is a theorem,
`Pcf.BoundingChart.isEtaleAt_restriction`.

## The chart

The manuscript proves the theorem at one integral effective divisor `E ⊆ B` at a time, by
choosing an affine open `U ⊆ Y` through the generic point of `E` that avoids `Σ`, and working
over `U`. `Pcf.BoundingChart R S a 𝔭` is the algebraic content of that choice:

| Manuscript | Chart datum |
| --- | --- |
| `U = Spec R` affine open of normal `Y`, `U ∩ Sing(Y) = ∅` | `R` Noetherian regular |
| `D = B ∩ U = V(a)` effective Cartier, `U ∩ Sing(B) = ∅` | `a` nonzerodivisor, `R/(a)` regular |
| `V = f⁻¹(U) = Spec S` normal, finite surjective over `U` | `S` Noetherian domain, finite, normal |
| `U ∩ Z = ∅`, so `branch(f) ∩ U ⊆ D` (Lemma `lem:dictionary`) | `unramified_codim_one` |
| the function-field extension is separable | `generic_etale` |
| `V` is the normalization of `U` in `W = V ∖ f⁻¹(D)` | `normalization` |
| characteristic zero (tameness) | `tame` |
| `A ∩ V` is a component of `f⁻¹(D)`, cut out by `𝔭` | `𝔭` a minimal prime over `aS` |
| Zariski–Nagata purity | `purity` (`Pcf.Stacks.ZariskiNagataPurity`) |
| Abhyankar's lemma | `abhyankar` (`Pcf.Stacks.AbhyankarLemma`) |

Every field except the last two is a hypothesis the manuscript states in Step 0 or in the
one-sentence verification inside Step 1. The last two are the classical theorems, stated
faithfully to the Stacks Project in `Pcf/Bounding/Stacks.lean`.

## The derivation

* **Step 1** — `Pcf.BoundingChart.isEtaleAt_of_notMem`: `S` is étale over `R` at every prime
  not containing `a`. Proved from `purity`, by verifying its hypotheses exactly as the
  manuscript does.
* **Step 2** — `Pcf.BoundingChart.exists_standardPieces`: Abhyankar's lemma applies, giving
  the étale neighbourhood `R'` and the decomposition `R' ⊗_R S ≅ ∏ R'[zᵢ]/(zᵢ^{eᵢ} − uᵢ a)`.
* **Steps 3–4** — `Pcf.BoundingChart.isEtaleAt_quot_of_pieces`: the base change of the
  restriction `R/(a) → S/𝔭` along `R → R'` is étale at every point. Step 3 is
  `Pcf.LocalModel.quotientMap_bijective` and `radical_span_algebraMap_eq_span_root`; the
  manuscript's dimension count and "union of connected components" argument are the two
  general lemmas of `Pcf/Bounding/LocalStructure.lean`; the conclusion at a point is
  `Pcf.Bounding.formallyEtale_of_localStructure`.
* **Descent** — `Pcf.BoundingChart.isEtaleAt_restriction`: étaleness descends from the
  étale cover to `R/(a) → S/𝔭` itself. The finite-presentation case of Stacks Tag 036W is
  proved in `Pcf/Bounding/Stacks.lean`; existence of a point of the cover over a given point
  is Tag 01JT.

## What is assumed, and where

Besides the chart, `isEtaleAt_restriction` takes only
`Pcf.Stacks.ExistsPrimeOverBoth` (Tag 01JT). It is **proved** in
`Pcf/Bounding/FibreProduct.lean` and remains a parameter here only to keep the scheme library
out of this file. The finite-presentation case of Tag 036W needed here is
`Pcf.Stacks.etaleLocalOnSource`. Tag 033B, reducedness of étale base change, is proved in
`Pcf/Bounding/Reduced.lean` for a domain base, which is all Step 3 needs. See
`lean/AXIOMS.md` §G.

Nothing here is a `KummerWitness`; nothing here lets the supplier of the data choose the
algebra to which Abhyankar's lemma is applied. The local extension is `R → S` itself, the
standard pieces are produced by the `abhyankar` field *for that extension*, and Step 3 is
applied to those pieces.
-/

universe u

open TensorProduct IsLocalRing

-- The proofs below install algebra structures on tensor products and quotients with `letI`.
-- Mathlib's style linter prefers `let` in proofs of propositions, but `let` would hide the
-- instance behind a local definition and `Algebra.TensorProduct.right_isScalarTower` would
-- no longer be found; `letI` is needed here, so the linter is switched off for this file.
set_option linter.style.haveILetI false

namespace Pcf

/-- **The data of Theorem `thm:bounding` on one affine chart.** See the module docstring for
the dictionary with the manuscript. All fields are propositions; the structure is a `Prop`. -/
structure BoundingChart (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R)
    (𝔭 : Ideal S) : Prop where
  /-- `U` is Noetherian (a variety). -/
  noetherian_base : IsNoetherianRing R
  /-- `V` is Noetherian. -/
  noetherian_cover : IsNoetherianRing S
  /-- `f` is finite. -/
  finite : Module.Finite R S
  /-- `V` is integral. -/
  domain : IsDomain S
  /-- `D = V(a)` is an effective Cartier divisor. -/
  nonZeroDivisor : a ∈ nonZeroDivisors R
  /-- `U ∩ Sing(Y) = ∅`: `U` is regular. -/
  regular : IsRegularRing R
  /-- `U ∩ Sing(B) = ∅`: `D` is regular. -/
  regular_divisor : IsRegularRing (R ⧸ Ideal.span {a})
  /-- `V` is normal: every local ring is integrally closed. -/
  normal : ∀ w : PrimeSpectrum S, IsIntegrallyClosed (Localization.AtPrime w.asIdeal)
  /-- Characteristic zero: every positive integer is invertible. -/
  tame : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)
  /-- `dim 𝒪_{V,w} = dim 𝒪_{U,f(w)}`, because `f` is finite and surjective between varieties
  (the sentence in Step 1). -/
  dim_eq : ∀ w : PrimeSpectrum S, w.asIdeal.height = (w.asIdeal.under R).height
  /-- The function-field extension is separable: `f` is étale at the generic point of `V`. -/
  generic_etale : ∀ w : PrimeSpectrum S, w.asIdeal.height = 0 → Algebra.IsEtaleAt R w.asIdeal
  /-- `branch(f) ∩ U ⊆ D` together with Lemma `lem:dictionary`: at a codimension-one point of
  `V` not over `D`, `f` is unramified. This encodes `U ∩ Z = ∅`. -/
  unramified_codim_one : ∀ w : PrimeSpectrum S, w.asIdeal.height = 1 →
    algebraMap R S a ∉ w.asIdeal → Algebra.IsUnramifiedAt R w.asIdeal
  /-- `V` is the normalization of `U` in `W = V ∖ f⁻¹(D)` (Step 2's second sentence). -/
  normalization : IsIntegralClosure S R (Localization.Away (algebraMap R S a))
  /-- `A ∩ V` is an integral closed subscheme. -/
  prime : 𝔭.IsPrime
  /-- `A ∩ V` is an irreducible component of `f⁻¹(D)` (Step 3's first sentence). -/
  minimal : 𝔭 ∈ (Ideal.span {algebraMap R S a}).minimalPrimes
  /-- **Zariski–Nagata purity**, Stacks Tag 0BMB. -/
  purity : Stacks.ZariskiNagataPurity R S
  /-- **Abhyankar's lemma**, Stacks Tags 0EYG/0EYH. -/
  abhyankar : Stacks.AbhyankarLemma R S a

namespace BoundingChart

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {a : R} {𝔭 : Ideal S}
  (h : BoundingChart R S a 𝔭)

include h

/-- `a ∈ 𝔭`: the divisor `A` lies over `D`. -/
theorem algebraMap_mem : algebraMap R S a ∈ 𝔭 :=
  h.minimal.1.2 (Ideal.mem_span_singleton_self _)

/-- `(a) ≤ 𝔭 ∩ R`: the hypothesis for the canonical map `R/(a) → S/𝔭`. -/
theorem span_le_comap : Ideal.span ({a} : Set R) ≤ 𝔭.comap (algebraMap R S) :=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h.algebraMap_mem)

/-! ### Step 1: purity makes `f` étale over `U ∖ D` -/

/-- **Step 1.** `S` is étale over `R` at every prime not containing `a`.

The manuscript: "If `w` is the generic point of `V`, then `f_V` is étale at `w` because the
extension of function fields is separable. Otherwise `dim 𝒪_{V,w} = dim 𝒪_{U,f(w)} ≥ 1` …
and we check the hypotheses of Theorem `thm:purity`: `𝒪_{V,w}` is normal, `𝒪_{U,f(w)}` is
regular, and `f_V` is quasi-finite. A codimension-one point `w'` specializing to `w` does not
lie in the closed set `f⁻¹(D)`, so `f(w') ∉ branch(f)`; hence `e = 1` at `w'`, and `f_V` is
étale, in particular unramified, at `w'` by Lemma `lem:dictionary`. Purity shows that `f_V` is
étale at `w`." -/
theorem isEtaleAt_of_notMem (w : PrimeSpectrum S) (hw : algebraMap R S a ∉ w.asIdeal) :
    Algebra.IsEtaleAt R w.asIdeal := by
  have := h.noetherian_base
  have := h.noetherian_cover
  have := h.finite
  have := h.domain
  have := h.regular
  rcases eq_or_ne w.asIdeal.height 0 with h0 | hne
  · exact h.generic_etale w h0
  · have h1 : 1 ≤ w.asIdeal.height := Order.one_le_iff_ne_zero.mpr hne
    refine h.purity inferInstance inferInstance inferInstance w
      { source_isDomain :=
          IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
        source_isIntegrallyClosed := h.normal w
        target_isRegular := inferInstance
        quasiFinite := inferInstance
        equalDimension := h.dim_eq w
        positiveDimension := h1
        unramifiedCodimensionOne := ?_ }
    intro w' hw' hw'1
    refine h.unramified_codim_one w' hw'1 fun hmem => hw ?_
    exact (PrimeSpectrum.le_iff_specializes w' w).mpr hw' hmem

/-! ### Step 2: Abhyankar's lemma applies -/

/-- **Step 2.** At every point `y` of `D`, Abhyankar's lemma produces an étale neighbourhood
`R'` over which the cover is a finite disjoint union of standard pieces. The hypotheses of
`Pcf.Stacks.AbhyankarLemma` are discharged by the chart and by Step 1. -/
theorem exists_standardPieces (y : PrimeSpectrum R) (hy : a ∈ y.asIdeal) :
    Stacks.HasAbhyankarStandardCoverAt R S a y :=
  h.abhyankar h.noetherian_base h.nonZeroDivisor h.regular_divisor h.finite
    h.isEtaleAt_of_notMem h.normalization h.tame y hy

/-! ### Steps 3–4: the base-changed restriction is étale everywhere -/

section Pieces

variable (R' : Type u) [CommRing R'] [Algebra R R']

omit h in
/-- `a` maps to the same element of `R' ⊗[R] S` through `R'` and through `S`. -/
theorem algebraMap_tensor_eq :
    letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    algebraMap R' (R' ⊗[R] S) (algebraMap R R' a)
      = algebraMap S (R' ⊗[R] S) (algebraMap R S a) := by
  letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  rw [← IsScalarTower.algebraMap_apply R R' (R' ⊗[R] S),
    ← IsScalarTower.algebraMap_apply R S (R' ⊗[R] S)]

/-- The hypothesis for the canonical map `R'/(a) → (R' ⊗[R] S)/𝔭(R' ⊗[R] S)`. -/
theorem span_le_comap_tensor :
    letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    Ideal.span {algebraMap R R' a}
      ≤ (𝔭.map (algebraMap S (R' ⊗[R] S))).comap (algebraMap R' (R' ⊗[R] S)) := by
  letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr ?_))
  rw [algebraMap_tensor_eq (a := a) R']
  exact Ideal.mem_map_of_mem _ h.algebraMap_mem

omit h in
/-- `R' ⊗[R] S` is étale over `S` when `R'` is étale over `R`. -/
theorem etale_tensor [Algebra.Etale R R'] :
    letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    Algebra.Etale S (R' ⊗[R] S) := by
  letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let e : S ⊗[R] R' ≃ₐ[S] R' ⊗[R] S :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R S R').toRingEquiv) <| by
      intro s
      simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  exact Algebra.Etale.of_equiv e

/-- **Steps 3 and 4.** Given the output of Abhyankar's lemma — the étale neighbourhood `R'`
and the decomposition `R' ⊗_R S ≅ ∏ R'[zᵢ]/(zᵢ^{eᵢ} − uᵢ a)` — together with the
local-domain conclusion supplied by Tag 00NP, the base change
`R'/(a) → (R' ⊗_R S)/𝔭(R' ⊗_R S)` of the restriction `g = f|_A` is étale at **every** point.

This is the manuscript's Step 3 ("`T` is a union of connected components of `∐ V(zᵢ)`, each
mapping isomorphically onto a connected component of `D'`") followed by the first sentence
of Step 4 ("`T → D'` is étale at `ξ'`"). The tameness of the `eᵢ` is **not** used here: it is
consumed inside Abhyankar's lemma, and once the pieces are standard the restriction is an
isomorphism for any `e ≥ 1`. -/
theorem isEtaleAt_quot_of_pieces (hEt : Algebra.Etale R R')
    (hdom : ∀ q : PrimeSpectrum (R' ⧸ Ideal.span {algebraMap R R' a}),
      IsDomain (Localization.AtPrime q.asIdeal))
    (ι : Type) [Finite ι] (e : ι → ℕ) (u : ι → R'ˣ) (he : ∀ i, e i ≠ 0)
    (φ : (R' ⊗[R] S) ≃ₐ[R']
      ∀ i, AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))) :
    letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra (R' ⧸ Ideal.span {algebraMap R R' a})
        ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) :=
      Ideal.Quotient.algebraQuotientOfLEComap (h.span_le_comap_tensor R')
    ∀ ξ' : PrimeSpectrum ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))),
      Algebra.IsEtaleAt (R' ⧸ Ideal.span {algebraMap R R' a}) ξ'.asIdeal := by
  classical
  letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra (R' ⧸ Ideal.span {algebraMap R R' a})
      ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) :=
    Ideal.Quotient.algebraQuotientOfLEComap (h.span_le_comap_tensor R')
  have := h.prime
  have : Algebra.Etale S (R' ⊗[R] S) := etale_tensor R'
  -- `B'` is étale over the domain `S/𝔭`, hence reduced (Tag 033B, `Pcf/Bounding/Reduced.lean`).
  have hB'red : IsReduced ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) := by
    have hEt : Algebra.Etale (S ⧸ 𝔭) ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) :=
      Algebra.Etale.of_equiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (R' ⊗[R] S) 𝔭).symm
    exact Stacks.isReduced_of_etale_of_isDomain (S ⧸ 𝔭) _
  -- `R'/(a)` is reduced, because its local rings are domains.
  have hA'red : IsReduced (R' ⧸ Ideal.span {algebraMap R R' a}) := by
    refine isReduced_ofLocalizationMaximal _ fun J hJ => ?_
    have := hJ.isPrime
    have := hdom ⟨J, hJ.isPrime⟩
    infer_instance
  intro ξ'
  -- The local ring at `ξ'` and the structure map from `R' ⊗[R] S`.
  have hLred : IsReduced (Localization.AtPrime ξ'.asIdeal) := by
    have := isReduced_localizationPreserves ξ'.asIdeal.primeCompl
      (Localization.AtPrime ξ'.asIdeal) hB'red
    exact this
  let ρ : (R' ⊗[R] S) →+* Localization.AtPrime ξ'.asIdeal :=
    (algebraMap _ _).comp (Ideal.Quotient.mk (𝔭.map (algebraMap S (R' ⊗[R] S))))
  have hρunit : ∀ s, IsUnit (ρ s) ↔
      Ideal.Quotient.mk (𝔭.map (algebraMap S (R' ⊗[R] S))) s ∈ ξ'.asIdeal.primeCompl := fun s =>
    IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime ξ'.asIdeal) ξ'.asIdeal _
  have hρJ : ∀ w ∈ 𝔭.map (algebraMap S (R' ⊗[R] S)), ρ w = 0 := fun w hw => by
    change algebraMap ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) _
      (Ideal.Quotient.mk (𝔭.map (algebraMap S (R' ⊗[R] S))) w) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hw, map_zero]
  -- The piece containing the point, and the map `θ` from it to the local ring.
  let ρP : (∀ j, AdjoinRoot (LocalModel.localPoly (u j) (algebraMap R R' a) (e j))) →+*
      Localization.AtPrime ξ'.asIdeal := ρ.comp φ.symm.toRingEquiv.toRingHom
  obtain ⟨i, hi⟩ := Bounding.exists_isUnit_evalRingHom_single
    (C := fun j => AdjoinRoot (LocalModel.localPoly (u j) (algebraMap R R' a) (e j)))
    (L := Localization.AtPrime ξ'.asIdeal) ρP
  obtain ⟨θ, hθ⟩ := Bounding.exists_lift_of_isUnit_single
    (C := fun j => AdjoinRoot (LocalModel.localPoly (u j) (algebraMap R R' a) (e j)))
    (L := Localization.AtPrime ξ'.asIdeal) ρP i hi
  -- Notation for the piece.
  let π : (R' ⊗[R] S) →+* AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i)) :=
    (Pi.evalRingHom _ i).comp φ.toRingEquiv.toRingHom
  have hθπ : ∀ w, θ (π w) = ρ w := fun w => by
    change θ (Pi.evalRingHom _ i (φ w)) = ρ w
    rw [hθ]
    change ρ (φ.symm (φ w)) = ρ w
    rw [AlgEquiv.symm_apply_apply]
  have hπalg : ∀ r : R', π (algebraMap R' (R' ⊗[R] S) r) = algebraMap R' _ r := fun r => by
    change Pi.evalRingHom _ i (φ (algebraMap R' (R' ⊗[R] S) r)) = _
    rw [AlgEquiv.commutes]
    rfl
  have hπsymm : ∀ x, π (φ.symm x) = Pi.evalRingHom _ i x := fun x => by
    change Pi.evalRingHom _ i (φ (φ.symm x)) = _
    rw [AlgEquiv.apply_symm_apply]
  -- The piece is étale over `S`: `S → R' ⊗[R] S` is étale, and the projection to the piece is a
  -- localization at an idempotent.
  let algS'P : Algebra (R' ⊗[R] S)
      (∀ j, AdjoinRoot (LocalModel.localPoly (u j) (algebraMap R R' a) (e j))) :=
    φ.toRingEquiv.toRingHom.toAlgebra
  have : Algebra.Etale (R' ⊗[R] S)
      (∀ j, AdjoinRoot (LocalModel.localPoly (u j) (algebraMap R R' a) (e j))) :=
    Algebra.Etale.of_equiv (AlgEquiv.ofRingEquiv (R := R' ⊗[R] S) (f := φ.toRingEquiv)
      fun _ => rfl)
  letI algPC : Algebra (∀ j, AdjoinRoot (LocalModel.localPoly (u j) (algebraMap R R' a) (e j)))
      (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))) :=
    (Pi.evalRingHom _ i).toAlgebra
  have := Bounding.isLocalizationAway_evalRingHom
    (C := fun j => AdjoinRoot (LocalModel.localPoly (u j) (algebraMap R R' a) (e j))) i
  have : Algebra.Etale (∀ j, AdjoinRoot (LocalModel.localPoly (u j) (algebraMap R R' a) (e j)))
      (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))) :=
    Algebra.Etale.of_isLocalizationAway (Pi.single i 1)
  let algS'C : Algebra (R' ⊗[R] S)
      (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))) := π.toAlgebra
  have : IsScalarTower (R' ⊗[R] S)
      (∀ j, AdjoinRoot (LocalModel.localPoly (u j) (algebraMap R R' a) (e j)))
      (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.Etale (R' ⊗[R] S)
      (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))) :=
    Algebra.Etale.comp (R' ⊗[R] S)
      (∀ j, AdjoinRoot (LocalModel.localPoly (u j) (algebraMap R R' a) (e j)))
      (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i)))
  letI algSC : Algebra S (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))) :=
    (π.comp (algebraMap S (R' ⊗[R] S))).toAlgebra
  have : IsScalarTower S (R' ⊗[R] S)
      (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.Etale S (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))) :=
    Algebra.Etale.comp S (R' ⊗[R] S)
      (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i)))
  -- The ideal of the preimage of `A ∩ V` in the piece, and the prime of the piece at the point.
  set I := (𝔭.map (algebraMap S (R' ⊗[R] S))).map π with hI
  have hIeq : I = 𝔭.map (algebraMap S
      (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i)))) := by
    rw [hI, Ideal.map_map]
    rfl
  have hIker : ∀ c ∈ I, θ c = 0 := by
    intro c hc
    have : I ≤ RingHom.ker θ := by
      rw [hI, Ideal.map_le_iff_le_comap]
      intro w hw
      rw [Ideal.mem_comap, RingHom.mem_ker, hθπ]
      exact hρJ w hw
    exact this hc
  have ha'C : algebraMap S (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i)))
      (algebraMap R S a) = algebraMap R' _ (algebraMap R R' a) := by
    change π (algebraMap S (R' ⊗[R] S) (algebraMap R S a)) = _
    rw [← algebraMap_tensor_eq (a := a) R', hπalg]
  have haI : algebraMap R' (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i)))
      (algebraMap R R' a) ∈ I := by
    rw [hIeq, ← ha'C]
    exact Ideal.mem_map_of_mem _ h.algebraMap_mem
  set 𝔫 : Ideal (AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))) :=
    (maximalIdeal (Localization.AtPrime ξ'.asIdeal)).comap θ with h𝔫
  have h𝔫p : 𝔫.IsPrime := Ideal.comap_isPrime _ _
  have hθunit : ∀ c, IsUnit (θ c) ↔ c ∉ 𝔫 := fun c => by
    rw [h𝔫, Ideal.mem_comap, IsLocalRing.notMem_maximalIdeal]
  -- `L` is a localization of `C/I` through `θ`.
  have hsurj : ∀ x : Localization.AtPrime ξ'.asIdeal, ∃ c s, IsUnit (θ s) ∧ x * θ s = θ c := by
    intro x
    obtain ⟨⟨y, s, hs⟩, hx⟩ := IsLocalization.surj ξ'.asIdeal.primeCompl x
    obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨s₀, rfl⟩ := Ideal.Quotient.mk_surjective s
    refine ⟨π y₀, π s₀, ?_, ?_⟩
    · rw [hθπ, hρunit]
      exact hs
    · rw [hθπ, hθπ]
      exact hx
  have hker : ∀ c, θ c = 0 → ∃ t, IsUnit (θ t) ∧ t * c ∈ I := by
    intro c hc
    have hcw : c = π (φ.symm (Pi.single i c)) := by rw [hπsymm]; simp
    have hρw : algebraMap _ (Localization.AtPrime ξ'.asIdeal)
        (Ideal.Quotient.mk (𝔭.map (algebraMap S (R' ⊗[R] S))) (φ.symm (Pi.single i c))) = 0 := by
      change ρ _ = 0
      rw [← hθπ, ← hcw]
      exact hc
    obtain ⟨⟨s, hs⟩, hsw⟩ := (IsLocalization.map_eq_zero_iff ξ'.asIdeal.primeCompl _ _).mp hρw
    obtain ⟨s₀, rfl⟩ := Ideal.Quotient.mk_surjective s
    refine ⟨π s₀, ?_, ?_⟩
    · rw [hθπ, hρunit]
      exact hs
    · rw [hcw, ← map_mul]
      apply Ideal.mem_map_of_mem
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact hsw
  -- `I ⊆ 𝔫`, and `z ∈ 𝔫`.
  have hI𝔫 : I ≤ 𝔫 := by
    intro c hc
    by_contra hc𝔫
    have := (hθunit c).mpr hc𝔫
    rw [hIker c hc] at this
    exact not_isUnit_zero this
  have he1 : 1 ≤ e i := Nat.one_le_iff_ne_zero.mpr (he i)
  have hz𝔫 : AdjoinRoot.root (LocalModel.localPoly (u i) (algebraMap R R' a) (e i)) ∈ 𝔫 := by
    refine h𝔫p.mem_of_pow_mem (e i) ?_
    rw [LocalModel.root_pow_eq, map_mul]
    exact Ideal.mul_mem_left _ _ (hI𝔫 haI)
  -- `I ⊆ (z)` locally at `𝔫`: the dimension count and the component argument.
  have hloc : ∀ c ∈ I, ∃ t, IsUnit (θ t) ∧ t * c ∈
      Ideal.span {AdjoinRoot.root (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))} := by
    obtain ⟨𝔮', h𝔮', h𝔮'le⟩ := Ideal.exists_minimalPrimes_le hI𝔫
    have h𝔮'I : I ≤ 𝔮' := h𝔮'.1.2
    -- Step 3's dimension count: `𝔮'` is minimal over `(a)`, hence over `(z)`.
    have h𝔮'z : 𝔮' ∈ (Ideal.span {AdjoinRoot.root
        (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))}).minimalPrimes := by
      rw [← LocalModel.radical_span_algebraMap_eq_span_root (u i) (algebraMap R R' a) he1,
        Ideal.radical_minimalPrimes, ← ha'C]
      rw [hIeq] at h𝔮'
      exact Bounding.mem_minimalPrimes_span_of_mem_minimalPrimes_map h.minimal h𝔮'
    -- The map `C → R'/(a)` with kernel `(z)`.
    let f : AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i)) →+*
        R' ⧸ Ideal.span {algebraMap R R' a} :=
      (LocalModel.quotientRootEquiv (u i) (algebraMap R R' a) he1).toRingEquiv.toRingHom.comp
        (Ideal.Quotient.mk _)
    have hf_surj : Function.Surjective f :=
      (LocalModel.quotientRootEquiv (u i) (algebraMap R R' a) he1).surjective.comp
        Ideal.Quotient.mk_surjective
    have hf_ker : RingHom.ker f = Ideal.span {AdjoinRoot.root
        (LocalModel.localPoly (u i) (algebraMap R R' a) (e i))} := by
      ext c
      rw [RingHom.mem_ker]
      change (LocalModel.quotientRootEquiv (u i) (algebraMap R R' a) he1)
        (Ideal.Quotient.mk _ c) = 0 ↔ _
      rw [map_eq_zero_iff _ (LocalModel.quotientRootEquiv (u i) (algebraMap R R' a) he1).injective,
        Ideal.Quotient.eq_zero_iff_mem]
    have hker𝔫 : RingHom.ker f ≤ 𝔫 := by
      rw [hf_ker, Ideal.span_le, Set.singleton_subset_iff]
      exact hz𝔫
    have h𝔫'p : (𝔫.map f).IsPrime := Ideal.map_isPrime_of_surjective hf_surj hker𝔫
    have := hdom ⟨𝔫.map f, h𝔫'p⟩
    rw [← hf_ker] at h𝔮'z
    have hle : 𝔮' ≤ (𝔫.map f).comap f := h𝔮'le.trans (Ideal.le_comap_map)
    have hcomp𝔫 : (𝔫.map f).comap f = 𝔫 := by
      rw [Ideal.comap_map_of_surjective f hf_surj, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hker𝔫]
    intro c hc
    obtain ⟨t, ht, htc⟩ := Bounding.exists_mul_mem_ker_of_mem_minimalPrimes_ker f hf_surj h𝔮'z
      (𝔫.map f) hle c (h𝔮'I hc)
    refine ⟨t, (hθunit t).mpr ?_, ?_⟩
    · rwa [← hcomp𝔫]
    · rwa [← hf_ker]
  -- Compatibility of `θ` with the structure map `R'/(a) → L`.
  have hcomp : ∀ r : R', θ (algebraMap R' _ r)
      = algebraMap (R' ⧸ Ideal.span {algebraMap R R' a}) (Localization.AtPrime ξ'.asIdeal)
        (Ideal.Quotient.mk _ r) := by
    intro r
    rw [← hπalg, hθπ]
    change algebraMap ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S)))
      (Localization.AtPrime ξ'.asIdeal)
      (Ideal.Quotient.mk (𝔭.map (algebraMap S (R' ⊗[R] S))) (algebraMap R' (R' ⊗[R] S) r)) = _
    rw [IsScalarTower.algebraMap_apply (R' ⧸ Ideal.span {algebraMap R R' a})
      ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) (Localization.AtPrime ξ'.asIdeal)]
    rfl
  -- Conclude by the local-structure lemma.
  exact Bounding.formallyEtale_of_localStructure (algebraMap R R' a) _ θ I hcomp
    (LocalModel.span_le_comap_span_root (u i) (algebraMap R R' a) he1)
    (LocalModel.quotientMap_bijective (u i) (algebraMap R R' a) he1)
    (LocalModel.root_pow_mem_span_algebraMap' (u i) (algebraMap R R' a)) haI hIker hsurj hker hloc

end Pieces

/-! ### Descent: Theorem `thm:bounding` on the chart -/

/-- **Theorem `thm:bounding`, derived on the chart.** The restriction `g = f|_A`, i.e. the
canonical map `R/(a) → S/𝔭`, is étale at every prime of `S/𝔭`.

Steps 1–2 produce the étale neighbourhood `R'` and the standard pieces
(`Pcf.BoundingChart.exists_standardPieces`); Steps 3–4 show the base change of `g` to `R'`
is étale at every point (`Pcf.BoundingChart.isEtaleAt_quot_of_pieces`); the point `ξ` of
`A ∩ V` lifts to the base change by Tag 01JT (`hF3`, proved in `Pcf/Bounding/FibreProduct.lean`
and supplied by the wiring); and étaleness descends by the proved finite-presentation case
of Tag 036W. Reducedness of the
base change, Tag 033B, is proved in `Pcf/Bounding/Reduced.lean` and used inside Step 3.

Since `U` was chosen inside the complement of `Σ`, this is exactly the manuscript's
conclusion: `g` is étale at every point of `A` over `U`, in particular at the generic point
of every integral effective divisor of `A` whose image is not contained in `Σ`. -/
theorem isEtaleAt_restriction (hF3 : Stacks.ExistsPrimeOverBoth.{u}) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.span_le_comap
    ∀ ξ : PrimeSpectrum (S ⧸ 𝔭), Algebra.IsEtaleAt (R ⧸ Ideal.span {a}) ξ.asIdeal := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.span_le_comap
  have := h.noetherian_base
  have := h.finite
  have := h.prime
  intro ξ
  -- The prime of `S` under `ξ`, and the point `y ∈ D` under it.
  set 𝔓S : Ideal S := ξ.asIdeal.comap (Ideal.Quotient.mk 𝔭) with h𝔓S
  have : 𝔓S.IsPrime := Ideal.comap_isPrime _ _
  have h𝔭𝔓S : 𝔭 ≤ 𝔓S := fun x hx => by
    rw [h𝔓S, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact zero_mem _
  let y : PrimeSpectrum R := ⟨𝔓S.under R, inferInstance⟩
  have hy : a ∈ y.asIdeal := Ideal.mem_comap.mpr (h𝔭𝔓S h.algebraMap_mem)
  -- Steps 1–2.
  obtain ⟨R', _, _, hEt, ⟨y', hy'⟩, -, -, hreg, ι, _, e, u, he, -, ⟨φ⟩⟩ :=
    h.exists_standardPieces y hy
  have hdom : ∀ q : PrimeSpectrum (R' ⧸ Ideal.span {algebraMap R R' a}),
      IsDomain (Localization.AtPrime q.asIdeal) := by
    letI : IsRegularRing (R' ⧸ Ideal.span {algebraMap R R' a}) := hreg
    intro q
    exact Stacks.isDomain_of_isRegularLocalRing _
  have := hEt
  letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.Etale S (R' ⊗[R] S) := etale_tensor R'
  have halgS : (algebraMap S (R' ⊗[R] S))
      = (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom := rfl
  -- A point of the base change over `ξ` (Tag 01JT).
  obtain ⟨r, hr₁, -⟩ := hF3 R S R' ⟨𝔓S, inferInstance⟩ y' (by rw [hy'])
  have hJr : 𝔭.map (algebraMap S (R' ⊗[R] S)) ≤ r.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, halgS, hr₁]
    exact h𝔭𝔓S
  let ξ' : PrimeSpectrum ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) :=
    ⟨r.asIdeal.map (Ideal.Quotient.mk _),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩
  have hξ' : ξ'.asIdeal.under (S ⧸ 𝔭) = ξ.asIdeal := by
    ext x
    obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (algebraMap S (R' ⊗[R] S) x₀) ∈ r.asIdeal.map (Ideal.Quotient.mk _)
      ↔ _
    rw [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr hJr]
    change algebraMap S (R' ⊗[R] S) x₀ ∈ r.asIdeal ↔ x₀ ∈ 𝔓S
    have hr₁' : Ideal.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom
        r.asIdeal = 𝔓S := hr₁
    rw [← hr₁', halgS]
    rfl
  -- The algebra structures for descent.
  have hle : Ideal.span ({a} : Set R)
      ≤ (𝔭.map (algebraMap S (R' ⊗[R] S))).comap (algebraMap R (R' ⊗[R] S)) := by
    refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr ?_))
    rw [IsScalarTower.algebraMap_apply R S (R' ⊗[R] S)]
    exact Ideal.mem_map_of_mem _ h.algebraMap_mem
  letI : Algebra (R ⧸ Ideal.span {a}) ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  have : IsScalarTower (R ⧸ Ideal.span {a}) (S ⧸ 𝔭)
      ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (algebraMap R (R' ⊗[R] S) r₀)
      = algebraMap (S ⧸ 𝔭) _ (Ideal.Quotient.mk 𝔭 (algebraMap R S r₀))
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient,
      IsScalarTower.algebraMap_apply R S (R' ⊗[R] S)]
  have : Algebra.Etale (S ⧸ 𝔭) ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) :=
    Algebra.Etale.of_equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (R' ⊗[R] S) 𝔭).symm
  -- Steps 3–4, transported from `R'/(a)` down to `R/(a)`.
  have hall : ∀ ξ'' : PrimeSpectrum ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))),
      Algebra.IsEtaleAt (R ⧸ Ideal.span {a}) ξ''.asIdeal := by
    intro ξ''
    letI : Algebra (R' ⧸ Ideal.span {algebraMap R R' a})
        ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) :=
      Ideal.Quotient.algebraQuotientOfLEComap (h.span_le_comap_tensor R')
    have hA' : Algebra.IsEtaleAt (R' ⧸ Ideal.span {algebraMap R R' a}) ξ''.asIdeal :=
      h.isEtaleAt_quot_of_pieces R' hEt hdom ι e u he φ ξ''
    have hle' : Ideal.span ({a} : Set R)
        ≤ (Ideal.span {algebraMap R R' a}).comap (algebraMap R R') :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
        (Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)))
    letI : Algebra (R ⧸ Ideal.span {a}) (R' ⧸ Ideal.span {algebraMap R R' a}) :=
      Ideal.Quotient.algebraQuotientOfLEComap hle'
    have : IsScalarTower (R ⧸ Ideal.span {a}) (R' ⧸ Ideal.span {algebraMap R R' a})
        ((R' ⊗[R] S) ⧸ 𝔭.map (algebraMap S (R' ⊗[R] S))) := by
      refine IsScalarTower.of_algebraMap_eq fun x => ?_
      obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk _ (algebraMap R (R' ⊗[R] S) r₀)
        = Ideal.Quotient.mk _ (algebraMap R' (R' ⊗[R] S) (algebraMap R R' r₀))
      rw [IsScalarTower.algebraMap_apply R R' (R' ⊗[R] S)]
    -- `R/(a) → R'/(a)` is étale: it is the base change of `R → R'`.
    have hmap : (Ideal.span ({a} : Set R)).map (algebraMap R R')
        = Ideal.span {algebraMap R R' a} := by
      rw [Ideal.map_span, Set.image_singleton]
    let e₁ : (R' ⧸ (Ideal.span ({a} : Set R)).map (algebraMap R R'))
        ≃ₐ[R ⧸ Ideal.span {a}] (R' ⧸ Ideal.span {algebraMap R R' a}) :=
      AlgEquiv.ofRingEquiv (f := Ideal.quotEquivOfEq hmap) fun x => by
        obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.quotEquivOfEq_mk]
        rfl
    have : Algebra.Etale (R ⧸ Ideal.span {a}) (R' ⧸ Ideal.span {algebraMap R R' a}) :=
      Algebra.Etale.of_equiv
        ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor R' (Ideal.span {a})).symm.trans e₁)
    have : Algebra.IsEtaleAt (R ⧸ Ideal.span {a})
        (ξ''.asIdeal.under (R' ⧸ Ideal.span {algebraMap R R' a})) := inferInstance
    exact Algebra.IsEtaleAt.comp (ξ''.asIdeal.under (R' ⧸ Ideal.span {algebraMap R R' a}))
      ξ''.asIdeal
  -- Descent (the finite-presentation case of Tag 036W).
  haveI : IsScalarTower R (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let _ : Module.Finite R (S ⧸ 𝔭) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R 𝔭).toLinearMap
      Ideal.Quotient.mk_surjective
  let _ : Module.Finite (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
    Module.Finite.of_restrictScalars_finite R _ _
  let _ : Algebra.FinitePresentation (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Stacks.etaleLocalOnSource (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) _ inferInstance hall ξ ⟨ξ', hξ'⟩

end BoundingChart

end Pcf
