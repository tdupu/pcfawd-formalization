/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Purity.Defs
import Pcf.Stacks.Purity.LocalEtale
import Pcf.Stacks.Purity.DimensionOne
import Pcf.Stacks.Purity.EtaleLocalization
import Pcf.Stacks.Purity.NormalRing
import Pcf.Stacks.Purity.IntegralClosure
import Pcf.Stacks.Purity.PuncturedSpectrum
import Pcf.Stacks.Purity.Hartogs
import Pcf.Stacks.Purity.FiniteNormalAlgebra

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
* quasi-compactness of the Noetherian punctured spectrum, together with injectivity of restriction
  of functions from a positive-dimensional local domain.

## Remaining Stacks spine

The higher-dimensional induction still requires punctured-spectrum purity (Tag `0BMA`). At the
pinned Mathlib revision, the key étale-local finite factor of Tag `02LK` is already available as
Tag `00UJ`, `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`. The categorical
depth-two/reflexive Hartogs recovery theorem needed to prove the equivalence in Tag `0BM9`, and
the hyperplane-section lifting theorem (Tag `0BLM`), remain absent.

No declaration in this assembly file asserts the unproved terminal theorem.
-/
