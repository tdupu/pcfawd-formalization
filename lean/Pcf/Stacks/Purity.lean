/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.Defs
public import Pcf.Stacks.Purity.LocalEtale
public import Pcf.Stacks.Purity.LocalFlatness
public import Pcf.Stacks.Purity.RegularHypersurface
public import Pcf.Stacks.Purity.FpqcEtaleDescent
public import Pcf.Stacks.Purity.DimensionOne
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Pcf.Stacks.Purity.NormalRing
public import Pcf.Stacks.Purity.IntegralClosure
public import Pcf.Stacks.Purity.PuncturedSpectrum
public import Pcf.Stacks.Purity.Hartogs
public import Pcf.Stacks.Purity.DepthTwo
public import Pcf.Stacks.Purity.HartogsAlgebra
public import Pcf.Stacks.Purity.HartogsRecovery
public import Pcf.Stacks.Purity.FiniteNormalAlgebra
public import Pcf.Stacks.Purity.FiniteNormalHartogs
public import Pcf.Stacks.Purity.FiniteNormalAlgebraRecovery
public import Pcf.Stacks.Purity.DiscriminantFiber
public import Pcf.Stacks.Purity.HeightOneEtaleBridge
public import Pcf.Stacks.Purity.OuterInduction
public import Pcf.Stacks.Purity.HypersurfaceLifting
public import Pcf.Stacks.Purity.HenselianIdempotents
public import Pcf.Stacks.Purity.FiniteAlgebraIdempotents
public import Pcf.Stacks.Purity.HenselianGabberPolynomial
public import Pcf.Stacks.Purity.GabberPolynomialSplit
public import Pcf.Stacks.Purity.GenericFiberDecomposition
public import Pcf.Stacks.Purity.GenericCoverFiber
public import Pcf.Stacks.Purity.GenericBaseNormalization
public import Pcf.Stacks.Purity.GenericFiberNormalization
public import Pcf.Stacks.Purity.GenericFiberExtension
public import Pcf.Stacks.Purity.NormalizationTower
public import Pcf.Stacks.Purity.FiniteNormalModel
public import Pcf.Stacks.Purity.CoverNormalModel
public import Pcf.Stacks.Purity.NormalizationExtension
public import Pcf.Stacks.Purity.Tag0BM9Equivalence
public import Pcf.Stacks.Purity.Tag0BMBAssembly
public import Pcf.Stacks.Purity.Tag0BMAClauses

/-!
# Zariski--Nagata purity: assembly boundary

This module is the stable import boundary for the affine statement consumed by PCFAWD and for
the proved pieces of its Stacks Tag `0BMB` proof.

## Proved here

* the faithful affine pointwise statement (`ZariskiNagataPurity`);
* the local essentially-finite-presentation flat-plus-unramified criterion;
* the full dimension-one branch of Tag `0BMB`, including both DVR reductions.
* the actual finite-étale restriction, global-sections, and affine-extension functors at the
  start of Tag `0BM9`.
* the literal possibly-disconnected Stacks-normal-ring predicate and the actual finite-normal
  algebra target category of Tag `0BM9`, including its obvious `Spec`-and-restrict functor.
* finiteness and Stacks-normality of the integral closure in the finite separable field-extension
  component of the construction in Tag `0BM9`.
* quasi-compactness and a finite maximal-ideal basic-open cover of the Noetherian punctured
  spectrum, together with injectivity of restriction of functions from a positive-dimensional
  local domain.
* the regular-sequence/associated-prime reduction of the missing depth-two (Serre S2) input.
* the numerator-denominator common-value calculation underlying the intersection of two away
  localizations along a regular pair.
* the resulting Hartogs isomorphism for a normal Noetherian local domain of dimension at least
  two.
* the actual relative normalization of the generic point over a normal affine domain is an
  isomorphism, ready for smooth base change.
* the complete height-one bridge from codimension-one unramifiedness to the finite-free
  discriminant criterion of Tags `0BJH`/`0BJF`.
* the outer regular-hypersurface induction step for Tag `0BMA`, conditional only on the exact
  hypersurface finite-etale lifting statement of Tag `0BLM`.

## Where the proof is completed

This file sits upstream of the proof of `0BMB`, so it cannot import it (that would be an import
cycle). The completed proof is downstream:

* `Pcf.Stacks.Purity.Tag0BMA`: `finiteNormalPuncturedEtalePurity_of_isRegularLocalRing` (`0BMA`)
  and `Pcf.Stacks.zariskiNagataPurity : ∀ R S, ZariskiNagataPurity R S` (`0BMB`, affine
  pointwise form), with axioms `[propext, Classical.choice, Quot.sound]`;
* `Pcf.Stacks.Purity.Tag0BMB`: the `0BMB` assembly from `033C` and `0BMA`;
* `Pcf.Stacks.Purity.HypersurfaceLiftingComplete`: `0BLM` for complete regular local rings.
* `Pcf.Stacks.Purity.Tag0BMBScheme`: `Pcf.Stacks.isStacksEtaleAt_of_zariskiNagataPurity`, the
  scheme-level pointwise form of `0BMB` (morphisms of locally Noetherian schemes).

All of these modules are imported by the root module `Pcf`.
-/

@[expose] public section

