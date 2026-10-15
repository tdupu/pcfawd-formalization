/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.QuasiFinite

/-!
# The étale-local finite component of a quasi-finite algebra

Stacks Tag `02LK` is the scheme-level étale-local finite reduction used in Tag `0BMB`.
Mathlib's Tag `00UJ` already proves its crucial affine pointed construction: after an étale
base change, an idempotent selects a finite component containing the chosen point, and this
component contains a unique point over the chosen base point.

The theorem below exposes that existing result under the purity namespace. It deliberately has
no `02LK` tag: its conclusion is the pointed affine finite-component result `00UJ`, not every
clause of the scheme-level tag `02LK`.
-/

@[expose] public section

open TensorProduct

namespace Pcf.Stacks

universe u v

/-- The pointed affine étale-local finite-component reduction supplied by Mathlib's faithful
formalization of Stacks Tag `00UJ`.

This is the algebraic construction required at the `02LK` step of the Tag `0BMB` proof. -/
theorem exists_etale_finite_component_of_quasiFiniteAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.QuasiFiniteAt R q] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p) (e : R' ⊗[R] S)
      (_ : IsIdempotentElem e) (P' : Ideal (R' ⊗[R] S)) (_ : P'.IsPrime)
      (_ : P'.LiesOver P),
      P'.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ P' ∧
      Function.Bijective
        (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      Module.Finite R' (Localization.Away e) ∧
      ∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P' :=
  Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q

end Pcf.Stacks
