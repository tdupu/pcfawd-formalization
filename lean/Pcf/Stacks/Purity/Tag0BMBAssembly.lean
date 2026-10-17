/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.DimensionOne
public import Pcf.Stacks.Purity.EtaleLocalization
public import Pcf.Stacks.Purity.FiniteNormalAlgebra

/-!
# The terminal affine assembly in Stacks Tag `0BMB`

This file isolates the last passage in the proof of Zariski--Nagata purity.  The passage has two
mathematically distinct inputs.

* Tag `00UJ` (the affine form used in Tag `02LK`) replaces a quasi-finite map near the chosen
  point by a finite component after a pointed etale base change.  The theorem
  `exists_etale_finiteComponent_of_zariskiNagataPurityHypothesesAt` applies the actual Mathlib
  theorem, with no proxy data.
* Clause (2) of Tag `0BMA` says that a finite torsion-free normal algebra which is etale on the
  punctured spectrum is etale.  `FiniteNormalPuncturedEtalePurity` records exactly this corrected
  affine clause.  Torsion-freeness is explicit because it excludes vertical closed-point
  factors, which restriction to the punctured spectrum cannot detect.

`zariskiNagataPurity_of_finiteLocalModels` performs the terminal dimension split and applies
clause (2) of `0BMA` to the localized finite model.  Its only remaining input is
`ZariskiNagataFiniteLocalModel`: the output that the `00UJ` component, etale descent, and the
induction on the nonclosed points must produce.  In particular, this file does not replace that
geometric reduction by an assumption of the desired `0BMB` conclusion.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct

set_option linter.style.haveILetI false

universe u v

namespace Pcf.Stacks

/-- The corrected affine form of clause (2) of Stacks Tag `0BMA`.

Divergence from Stacks: the literal clause (2) (any finite `A → B` with `B` normal, étale over the
punctured spectrum, is étale) is false, since `B = A × κ(𝔪)` is finite, normal, étale over the
punctured spectrum `U` (the `κ(𝔪)` factor lies over the closed point, so `Spec B ×_X U = U`), but
not flat over `A` when `dim A ≥ 2`.  The hypothesis "`B` torsion-free over `A`" (no component of
`Spec B` over the closed point) is added; it is what the Stacks proof uses.

The target category is the literal finite, torsion-free, Stacks-normal category of Tag `0BM9`.
The conclusion says that such an algebra is finite etale when its spectrum is etale over the
punctured spectrum. -/
def FiniteNormalPuncturedEtalePurity
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] : Prop :=
  ∀ B : (CommAlgCat R)ᵒᵖ,
    finiteNormalPuncturedEtaleAlgebraProperty R B → Algebra.Etale R B.unop

/-- The exact finite-local output needed after the `00UJ`/`02LK` reduction in Tag `0BMB`.

Here `R_p → S_q` is the canonical map of local rings at the chosen point.  Finiteness is the
finite-component conclusion of `00UJ`; torsion-freeness is the injective/equidimensional part of
the Stacks argument; and the last field is the induction conclusion on the punctured spectrum.
Normality is deliberately absent: it follows from the `ZariskiNagataPurityHypothesesAt` hypothesis
on `S_q` and is installed in the terminal theorem below. -/
def ZariskiNagataFiniteLocalModel
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (w : PrimeSpectrum S) : Prop :=
  let p := w.asIdeal.under R
  let q := w.asIdeal
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let _ : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  Module.Finite Rp Sq ∧ Module.IsTorsionFree Rp Sq ∧
    Etale (((Over.pullback (puncturedSpectrum Rp).ι).obj
      ((algSpec (.of Rp)).obj (Opposite.op (.of Rp Sq)))).hom)

/-- Tag `00UJ`, specialized to the pointwise hypotheses of Tag `0BMB`.

The selected idempotent cuts out a finite component after an etale base change.  The selected
component contains a unique prime over the pointed prime and that prime maps to the original
point.  This is the actual affine construction invoked at the `02LK` sentence of the Stacks
proof, rather than a conclusion-shaped finite-model premise. -/
theorem exists_etale_finiteComponent_of_zariskiNagataPurityHypothesesAt
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    (w : PrimeSpectrum S) (h : ZariskiNagataPurityHypothesesAt R S w) :
    let p := w.asIdeal.under R
    let q := w.asIdeal
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p) (e : R' ⊗[R] S)
      (_ : IsIdempotentElem e) (P' : Ideal (R' ⊗[R] S)) (_ : P'.IsPrime)
      (_ : P'.LiesOver P),
      P'.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ P' ∧
      Function.Bijective
        (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      Module.Finite R' (Localization.Away e) ∧
      ∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P' := by
  dsimp only
  let p := w.asIdeal.under R
  let q := w.asIdeal
  letI : Algebra.QuasiFiniteAt R q := h.quasiFinite
  letI : q.LiesOver p := ⟨rfl⟩
  exact exists_etale_finite_component_of_quasiFiniteAt p q

/-- Once the finite local model has been produced, clause (2) of Tag `0BMA` gives the desired
etaleness at the original point.

This theorem is the final local composition in Tag `0BMB`: normality of `S_q` comes directly
from the pointwise hypotheses, while formal etaleness over `R` is the composite of localization
`R → R_p` and the finite-etale local model `R_p → S_q`. -/
theorem hasZariskiNagataPurityAt_of_finiteLocalModel
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType R S]
    (w : PrimeSpectrum S)
    (h0BMA : FiniteNormalPuncturedEtalePurity
      (Localization.AtPrime (w.asIdeal.under R)))
    (hmodel : ZariskiNagataFiniteLocalModel R S w) :
    HasZariskiNagataPurityAt R S w := by
  intro h
  let p := w.asIdeal.under R
  let q := w.asIdeal
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  letI : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  letI : IsScalarTower R Rp Sq := by infer_instance
  change Module.Finite Rp Sq ∧ Module.IsTorsionFree Rp Sq ∧
    Etale (((Over.pullback (puncturedSpectrum Rp).ι).obj
      ((algSpec (.of Rp)).obj (Opposite.op (.of Rp Sq)))).hom) at hmodel
  letI : Module.Finite Rp Sq := hmodel.1
  letI : Module.IsTorsionFree Rp Sq := hmodel.2.1
  letI : IsDomain Sq := h.source_isDomain
  letI : IsIntegrallyClosed Sq := h.source_isIntegrallyClosed
  have hnormal : IsStacksNormalRing Sq := IsStacksNormalRing.of_isDomain
  let B : (CommAlgCat Rp)ᵒᵖ := Opposite.op (.of Rp Sq)
  have hB : finiteNormalPuncturedEtaleAlgebraProperty Rp B :=
    ⟨inferInstance, inferInstance, hnormal, hmodel.2.2⟩
  letI : Algebra.Etale Rp Sq := h0BMA B hB
  exact Algebra.FormallyEtale.comp R Rp Sq

/-- The terminal `0BMB` assembly.

Dimension one is the already proved DVR case.  In dimension at least two, the theorem consumes
the exact finite local model produced by `00UJ`/`02LK` plus induction on the puncture and invokes
the finite-normal clause of `0BMA`. -/
theorem zariskiNagataPurity_of_finiteLocalModels
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType R S]
    (h0BMA : ∀ (w : PrimeSpectrum S), ZariskiNagataPurityHypothesesAt R S w →
      2 ≤ w.asIdeal.height →
      FiniteNormalPuncturedEtalePurity
        (Localization.AtPrime (w.asIdeal.under R)))
    (hmodels : ∀ (w : PrimeSpectrum S), ZariskiNagataPurityHypothesesAt R S w →
      2 ≤ w.asIdeal.height →
      ZariskiNagataFiniteLocalModel R S w) :
    ZariskiNagataPurity R S := by
  intro _ _ _ w h
  by_cases hw : w.asIdeal.height = 1
  · exact hasZariskiNagataPurityAt_of_height_eq_one R S w hw h
  · have hwlt : 1 < w.asIdeal.height :=
      lt_of_le_of_ne h.positiveDimension (Ne.symm hw)
    have hw2 : 2 ≤ w.asIdeal.height := by
      exact ENat.natCast_add_one_le_iff.mpr hwlt
    exact hasZariskiNagataPurityAt_of_finiteLocalModel R S w
      (h0BMA w h hw2) (hmodels w h hw2) h

#print axioms exists_etale_finiteComponent_of_zariskiNagataPurityHypothesesAt
#print axioms hasZariskiNagataPurityAt_of_finiteLocalModel
#print axioms zariskiNagataPurity_of_finiteLocalModels

end Pcf.Stacks
