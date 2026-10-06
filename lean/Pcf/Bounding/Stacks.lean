/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Pcf.LocalModel

/-!
# The classical inputs of Theorem `thm:bounding`, stated as the Stacks Project states them

§`sec:bounding` of `latex/paper.tex` proves Theorem `thm:bounding` from two classical theorems,
Zariski–Nagata purity (Stacks Tag 0BMB) and Abhyankar's lemma (Stacks Tags 0EYG, 0EYH), and
from three facts it cites in passing: étale base change preserves reducedness (Tag 033B),
étaleness is étale-local on the source (Tag 036W), and points of a fibre product exist over
compatible pairs of points (Tag 01JT). Neither classical theorem is in Mathlib. This file
states them as `Prop`s about **arbitrary commutative rings**, in the
commutative-algebra language of one affine chart, so that `Pcf/Bounding/Chart.lean` can take
them as hypotheses and *derive* the bounding theorem. The finite-presentation case of Tag
036W needed by the chart is **proved below**; Tag 01JT is stated here and **proved** in
`Pcf/Bounding/FibreProduct.lean`; Tag 033B is **proved** directly, for a domain base, in
`Pcf/Bounding/Reduced.lean`.

## Design rule

Every statement here is a statement about rings given to it as arguments. None of them
mentions the prime `𝔭` cutting out the divisor `A`, none mentions the restriction
`R/(a) → S/𝔭`, and none mentions étaleness of that restriction. So none of them is, or can
be, a restatement of the conclusion of Theorem `thm:bounding`; that conclusion is about
`S/𝔭`, which is not in their vocabulary. The facts of Tags 036W and 01JT are universally
quantified over *all* rings of the universe, so they cannot be tailored to any particular
datum at all.

## Faithfulness

Each docstring below records how the Lean `Prop` relates to the tag it is named after:
where it is the tag verbatim, where it is **weaker** (we assume less: extra hypotheses, or a
smaller conclusion, or a special case), and where a consequence has been adjoined because
Mathlib lacks the lemma that would derive it. The side-by-side comparison is repeated in
`lean/AXIOMS.md` §G.
-/

universe u

open TensorProduct

namespace Pcf.Stacks

/-- **Zariski–Nagata purity, Stacks Tag 0BMB**, for the morphism `Spec S → Spec R`.

Tag 0BMB: *Let `f : X → Y` be a morphism of locally Noetherian schemes, `x ∈ X`, `y = f(x)`.
Assume (1) `𝒪_{X,x}` is normal, (2) `𝒪_{Y,y}` is regular, (3) `f` is quasi-finite at `x`,
(4) `dim 𝒪_{X,x} = dim 𝒪_{Y,y} ≥ 1`, (5) for specializations `x' ⤳ x` with
`dim 𝒪_{X,x'} = 1`, `f` is unramified at `x'`. Then `f` is étale at `x`.*

Here `X = Spec S`, `Y = Spec R`, `x = w`, `y = w ∩ R`; `𝒪_{X,x} = S_w`,
`𝒪_{Y,y} = R_{w ∩ R}`; `dim 𝒪_{X,x}` is the height of `w`; "normal" is "integrally closed
domain"; `x' ⤳ x` is `w' ≤ w` (`PrimeSpectrum.le_iff_specializes`). "Quasi-finite at `x`"
in the Stacks Project presupposes locally of finite type, so `Algebra.FiniteType R S` is an
explicit premise alongside Mathlib's `Algebra.QuasiFiniteAt`. "Unramified at `x'`" and
"étale at `x`" are Mathlib's `IsUnramifiedAt`/`IsEtaleAt`, i.e. the local ring at the point
is formally unramified/étale over `R`; for algebras of finite type over a Noetherian ring
this is the Stacks meaning (étale on a neighbourhood).

**Verdict: faithful** — a special case of the tag (affine source and target). -/
def ZariskiNagataPurity (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  IsNoetherianRing R → IsNoetherianRing S → Algebra.FiniteType R S →
  ∀ w : PrimeSpectrum S,
    IsDomain (Localization.AtPrime w.asIdeal) →
    IsIntegrallyClosed (Localization.AtPrime w.asIdeal) →
    IsRegularLocalRing (Localization.AtPrime (w.asIdeal.under R)) →
    Algebra.QuasiFiniteAt R w.asIdeal →
    w.asIdeal.height = (w.asIdeal.under R).height →
    1 ≤ w.asIdeal.height →
    (∀ w' : PrimeSpectrum S, w' ⤳ w → w'.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt R w'.asIdeal) →
    Algebra.IsEtaleAt R w.asIdeal

/-- **Abhyankar's lemma for a regular divisor, Stacks Tags 0EYG and 0EYH**, for
`X = Spec R`, `D = V(a)`, `Y = Spec S_a`, and the normalization `Spec S` of `X` in `Y`.

Tag 0EYG: *Let `X` be a locally Noetherian scheme, `D ⊂ X` an effective Cartier divisor
such that `D` is a regular scheme, `Y → X ∖ D` a finite étale morphism. If `Y` is tamely
ramified over `X` in codimension 1, then étale locally on `X` the morphism `Y → X` is a
finite disjoint union of standard tamely ramified morphisms.*
Tag 0EYH: *… the normalization of `X` in `Y` is a finite locally free morphism
`π : Y' → X` … and étale locally on `X` the morphism `Y' → X` is a finite disjoint union of
morphisms `Spec(A[x]/(x^e − f)) → Spec(A)` where `A` is Noetherian, `f ∈ A` a nonzerodivisor
with `A/fA` regular, and `e ≥ 1` invertible in `A`.*

Premises, in order: `R` Noetherian (locally Noetherian `X`); `a` a nonzerodivisor (`D`
effective Cartier); `R/aR` regular (`D` regular); `S` finite over `R` and étale at every
prime not containing `a` (`Y = Spec S_a → X ∖ D` finite étale, written pointwise — for a
finite algebra over a Noetherian ring, étale at every point of `D(a)` is étale over
`Spec R_a`); `S` is the integral closure of `R` in `S_a` (`Spec S` is the normalization of
`X` in `Y`); and every positive integer is invertible in `R`. The last premise is **stronger**
than 0EYG's "tamely ramified in codimension 1" (it is the manuscript's standing
characteristic-zero hypothesis), so what is assumed is **weaker** than the tag.

Conclusion, for every point `y ∈ D`: an étale `R`-algebra `R'` with a point over `y` such
that `S ⊗_R R' ≅ ∏ᵢ R'[z]/(z^{eᵢ} − uᵢ a)` as `R'`-algebras, with each `eᵢ ≥ 1` invertible in
`R'`, `a` a nonzerodivisor of `R'`, `R'` Noetherian and `R'/aR'` regular — exactly 0EYH's
list, except that (i) the units `uᵢ` are allowed (the manuscript's form; 0EYH has `uᵢ = 1`,
so this conclusion is **weaker**), (ii) only points of `D` are covered (**weaker**), and
(iii) the clause "every local ring of `R'/aR'` is a domain" is adjoined. Clause (iii) is a
consequence of "`R'/aR'` regular" by Stacks Tag 00NP (a regular local ring is a domain),
which Mathlib does not yet have; with 00NP the two conclusions are equivalent, so (iii) adds
nothing to what is assumed beyond a lemma Mathlib lacks.

**Verdict: weaker** than 0EYG + 0EYH, modulo Tag 00NP. -/
def AbhyankarLemma (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) : Prop :=
  IsNoetherianRing R →
  a ∈ nonZeroDivisors R →
  IsRegularRing (R ⧸ Ideal.span {a}) →
  Module.Finite R S →
  (∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal) →
  IsIntegralClosure S R (Localization.Away (algebraMap R S a)) →
  (∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) →
  ∀ y : PrimeSpectrum R, a ∈ y.asIdeal →
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
      Algebra.Etale R R' ∧
      (∃ y' : PrimeSpectrum R', y'.asIdeal.under R = y.asIdeal) ∧
      IsNoetherianRing R' ∧
      algebraMap R R' a ∈ nonZeroDivisors R' ∧
      IsRegularRing (R' ⧸ Ideal.span {algebraMap R R' a}) ∧
      (∀ q : PrimeSpectrum (R' ⧸ Ideal.span {algebraMap R R' a}),
        IsDomain (Localization.AtPrime q.asIdeal)) ∧
      ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (u : ι → R'ˣ),
        (∀ i, e i ≠ 0) ∧ (∀ i, IsUnit ((e i : ℕ) : R')) ∧
        Nonempty ((R' ⊗[R] S) ≃ₐ[R']
          ∀ i, AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i)))

/-- **Étaleness is étale-local on the source, Stacks Tag 036W**, at a point.

Tag 036W: *The property "`f` is étale" is étale local on the source*, i.e. for an étale
covering `{Xᵢ → X}`, `f : X → Y` is étale iff every `Xᵢ → Y` is étale. Here `X = Spec B`,
`Y = Spec A`, and a single étale `X' = Spec B' → X`. The statement below says: if
`X' → Y` is étale at every point and `ξ ∈ X` is in the image of `X'`, then `X → Y` is étale
at `ξ`. It follows from 036W applied to the open image `U ⊆ X` of `X'` (étale morphisms are
open, Tag 03WT), which `X'` covers étale-locally.

The chart map is finite, so the statement includes the finite-presentation hypothesis on
`A → B`. This is enough to shrink the image of the étale cover to a faithfully flat basic
open and descend flatness and formal unramifiedness.

**Verdict: weaker** (a finite-presentation pointwise consequence of 036W together with
03WT).

**Status: proved**, as `Pcf.Stacks.etaleLocalOnSource`. -/
def EtaleLocalOnSource : Prop :=
  ∀ (A B B' : Type u) [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    [Algebra B B'] [IsScalarTower A B B'] [Algebra.FinitePresentation A B],
    Algebra.Etale B B' →
    (∀ ξ' : PrimeSpectrum B', Algebra.IsEtaleAt A ξ'.asIdeal) →
    ∀ ξ : PrimeSpectrum B, (∃ ξ' : PrimeSpectrum B', ξ'.asIdeal.under B = ξ.asIdeal) →
      Algebra.IsEtaleAt A ξ.asIdeal

open TensorProduct

/-- Flatness descends through a faithfully flat extension of the target. -/
private theorem flat_of_faithfullyFlat_restrictScalars
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro M N _ _ _ _ f hf
  refine (Module.FaithfullyFlat.lTensor_injective_iff_injective S T
    (AlgebraTensorModule.lTensor S S f)).mp ?_
  change Function.Injective ⇑(AlgebraTensorModule.lTensor T T
    (AlgebraTensorModule.lTensor S S f))
  intro x y hxy
  let eM := AlgebraTensorModule.cancelBaseChange R S T T M
  let eN := AlgebraTensorModule.cancelBaseChange R S T T N
  apply eM.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hcomm := AlgebraTensorModule.lTensor_comp_cancelBaseChange R S T (M := T) f
  have hx := LinearMap.congr_fun hcomm x
  have hy := LinearMap.congr_fun hcomm y
  simp only [LinearMap.comp_apply] at hx hy
  exact hx.trans ((congrArg (fun z ↦ eN z) hxy).trans hy.symm)

/-- If `S → T` is faithfully flat and étale, and `R → T` is étale, then a
finite-presentation map `R → S` is étale. -/
private theorem etale_of_faithfullyFlat_restrictScalars
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Algebra.Etale R T] [Algebra.Etale S T]
    [Algebra.FinitePresentation R S] : Algebra.Etale R S := by
  let _ : Module.Flat R S := flat_of_faithfullyFlat_restrictScalars R S T
  let _ : Algebra.FormallyUnramified R S :=
    Algebra.formallyUnramified_iff R S |>.mpr <| by
      let _ : Subsingleton (T ⊗[S] Ω[S⁄R]) :=
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).subsingleton
      exact Module.FaithfullyFlat.lTensor_reflects_triviality S T Ω[S⁄R]
  exact Algebra.Etale.of_formallyUnramified_of_flat

set_option linter.style.haveILetI false in
/-- The finite-presentation pointwise form of Stacks Tag 036W used by the bounding chart. -/
theorem etaleLocalOnSource : EtaleLocalOnSource.{u} := by
  intro A B C _ _ _ _ _ _ _ _ hBC hall p hp
  let _ : Algebra.Etale B C := hBC
  let _ : Algebra.FinitePresentation A C :=
    Algebra.FinitePresentation.trans A B C
  have hAC : Algebra.Etale A C :=
    Algebra.etaleLocus_eq_univ_iff_etale.mp <|
      Set.eq_univ_iff_forall.mpr hall
  obtain ⟨q, hqp⟩ := hp
  have hpRange : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B C)) :=
    ⟨q, PrimeSpectrum.ext hqp⟩
  have hOpenRange : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap B C))) := by
    rw [← Set.image_univ]
    exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      Set.univ isOpen_univ
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hfRange⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpRange hOpenRange
  let Bf := Localization.Away f
  let Cf := Localization.Away (algebraMap B C f)
  haveI : IsScalarTower A B Bf := by infer_instance
  haveI : IsScalarTower A C Cf := by infer_instance
  haveI : IsScalarTower B C Cf := by infer_instance
  letI : Algebra Bf Cf :=
    (IsLocalization.Away.map Bf Cf (algebraMap B C) f).toAlgebra
  haveI : IsScalarTower B Bf Cf := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp [RingHom.algebraMap_toAlgebra, IsLocalization.Away.map,
      ← IsScalarTower.algebraMap_apply B C]
  haveI : IsScalarTower A Bf Cf := .to₁₃₄ A B Bf Cf
  let _ : Algebra.Etale A Cf := by
    let _ : Algebra.Etale A C := hAC
    exact Algebra.Etale.comp A C Cf
  let _ : Algebra.Etale Bf Cf := by
    let _ : Algebra.Etale B Cf := Algebra.Etale.comp B C Cf
    exact Algebra.Etale.of_restrictScalars B Bf Cf
  let _ : Algebra.FinitePresentation A Bf :=
    Algebra.FinitePresentation.trans A B Bf
  let _ : Module.FaithfullyFlat Bf Cf :=
    Module.FaithfullyFlat.of_comap_surjective (by
      intro P
      let pB : PrimeSpectrum B := PrimeSpectrum.comap (algebraMap B Bf) P
      have hpBf : pB ∈ PrimeSpectrum.basicOpen f := by
        change pB ∈ (↑(PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum B))
        rw [← PrimeSpectrum.localization_away_comap_range Bf f]
        exact ⟨P, rfl⟩
      obtain ⟨Q, hQ⟩ := hfRange hpBf
      have hQideal : Q.asIdeal.under B = pB.asIdeal := by
        simpa only [PrimeSpectrum.comap_asIdeal] using congr_arg PrimeSpectrum.asIdeal hQ
      have hQf : Q ∈ PrimeSpectrum.basicOpen (algebraMap B C f) := by
        rw [PrimeSpectrum.mem_basicOpen]
        intro hfQ
        change f ∈ Q.asIdeal.under B at hfQ
        rw [hQideal] at hfQ
        exact (PrimeSpectrum.mem_basicOpen f pB).mp hpBf hfQ
      have hQf' : Q ∈ Set.range (PrimeSpectrum.comap (algebraMap C Cf)) := by
        rw [PrimeSpectrum.localization_away_comap_range Cf (algebraMap B C f)]
        exact hQf
      obtain ⟨Qf, hQf⟩ := hQf'
      have hQfIdeal : Qf.asIdeal.under C = Q.asIdeal := by
        simpa only [PrimeSpectrum.comap_asIdeal] using congr_arg PrimeSpectrum.asIdeal hQf
      refine ⟨Qf, ?_⟩
      apply PrimeSpectrum.localization_comap_injective Bf (.powers f)
      apply PrimeSpectrum.ext
      simp only [PrimeSpectrum.comap_asIdeal]
      calc
        (Qf.asIdeal.under Bf).under B = Qf.asIdeal.under B :=
          Ideal.under_under Qf.asIdeal
        _ = (Qf.asIdeal.under C).under B := (Ideal.under_under Qf.asIdeal).symm
        _ = Q.asIdeal.under B := congr_arg (Ideal.under B) hQfIdeal
        _ = pB.asIdeal := hQideal
        _ = P.asIdeal.under B := rfl)
  have : Algebra.Etale A Bf := etale_of_faithfullyFlat_restrictScalars A Bf Cf
  exact (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr this) hpf

/-- **Points of a fibre product, Stacks Tag 01JT.**

Tag 01JT: *Let `f : X → S` and `g : Y → S` be morphisms of schemes. Points `z` of `X ×_S Y`
are in bijective correspondence to quadruples `(x, y, s, 𝔭)` where `f(x) = s = g(y)` and `𝔭`
is a prime of `κ(x) ⊗_{κ(s)} κ(y)`.* Since the tensor product of two field extensions of
`κ(s)` is a nonzero ring, it has a prime, so every pair `(x, y)` over the same `s` is the
image of a point of the fibre product. Below: `X = Spec S`, `Y = Spec T`, `S = Spec R`.

**Verdict: weaker** (the existence half of the bijection, for affine schemes).

**Status: proved**, in `Pcf/Bounding/FibreProduct.lean` (`Pcf.Stacks.existsPrimeOverBoth`),
from Mathlib's `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback` and
`AlgebraicGeometry.pullbackSpecIso`. It is kept as a named `Prop` so that
`Pcf.BoundingChart.isEtaleAt_restriction` can be stated without importing the scheme
library; the wiring supplies the proof. -/
def ExistsPrimeOverBoth : Prop :=
  ∀ (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (p : PrimeSpectrum S) (q : PrimeSpectrum T), p.asIdeal.under R = q.asIdeal.under R →
    ∃ r : PrimeSpectrum (T ⊗[R] S),
      r.asIdeal.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).toRingHom
        = p.asIdeal ∧
      r.asIdeal.under T = q.asIdeal

/-! ### Self-checks on the two theorem-level inputs

Neither `ZariskiNagataPurity R S` nor `AbhyankarLemma R S a` mentions a prime `𝔭` of `S` or
the quotient `S ⧸ 𝔭`; both are statements about the cover `R → S` alone. The conclusion of
Theorem `thm:bounding` on a chart (`Pcf.BoundingChart.isEtaleAt_restriction`) is a statement
about `R ⧸ (a) → S ⧸ 𝔭`. So neither input can be equivalent to that conclusion. The two
lemmas below make the cheapest instance of this visible: purity holds outright for an étale
cover, with no information about any divisor. -/

/-- Purity is satisfied by any étale algebra, whatever `a` or `𝔭` may later be: the
conclusion of 0BMB is étaleness at `w`, which an étale algebra has at every prime. -/
theorem ZariskiNagataPurity.of_etale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] : ZariskiNagataPurity R S :=
  fun _ _ _ w _ _ _ _ _ _ _ =>
    inferInstanceAs (Algebra.FormallyEtale R (Localization.AtPrime w.asIdeal))

end Pcf.Stacks
