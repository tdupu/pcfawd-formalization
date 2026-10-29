/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Henselian

/-!
# Lifting sections of standard etale algebras over a henselian pair

For a henselian pair `(R, I)`, every `R`-algebra map from a standard etale `R`-algebra to
`R ⧸ I` lifts to an `R`-algebra map to `R`.  A standard etale presentation reduces the problem
to lifting one simple root.  Mathlib's definition of `HenselianRing` supplies that root directly;
the localization polynomial remains invertible because `R → R ⧸ I` is a local homomorphism.

This is the standard-etale case of condition (2) in Stacks Project Tag `09XI`.  It is not the
full condition: an arbitrary etale algebra is only locally standard etale, and passing from those
local presentations to a global lifted section still requires the integral-closure and clopen
assembly in the proof of Tag `09XI`, implication `(5) ⇒ (2)`.
-/

@[expose] public section

noncomputable section

open Polynomial

universe u v

namespace Pcf.Stacks

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

private theorem quotient_eval_eq_eval₂
    (I : Ideal R) (p : R[X]) {a : R} {abar : R ⧸ I}
    (ha : Ideal.Quotient.mk I a = abar) :
    Ideal.Quotient.mk I (p.eval a) = p.eval₂ (Ideal.Quotient.mk I) abar := by
  calc
    Ideal.Quotient.mk I (p.eval a) =
        p.eval₂ (Ideal.Quotient.mk I) (Ideal.Quotient.mk I a) :=
      (eval₂_at_apply (Ideal.Quotient.mk I) a).symm
    _ = p.eval₂ (Ideal.Quotient.mk I) abar := by rw [ha]

/-- A section modulo a henselian ideal of a standard etale algebra lifts to the base ring.

This is the standard-etale presentation step in Stacks Project Tag `09XI`, condition (2), not
the assertion for an arbitrary etale algebra. -/
theorem exists_algHom_lift_of_isStandardEtale
    (I : Ideal R) [HenselianRing R I] [Algebra.IsStandardEtale R S]
    (σ : S →ₐ[R] R ⧸ I) :
    ∃ τ : S →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp τ = σ := by
  let P : StandardEtalePresentation R S :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let σP : P.Ring →ₐ[R] R ⧸ I := σ.comp P.equivRing.symm.toAlgHom
  let xbar : R ⧸ I := σP P.X
  have hxbar : P.HasMap xbar := P.hasMap_X.map σP
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective xbar
  have hroot : P.f.eval a₀ ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (quotient_eval_eq_eval₂ I P.f ha₀).trans
      (by simpa [aeval_def] using hxbar.1)
  have hderiv : IsUnit (Ideal.Quotient.mk I (P.f.derivative.eval a₀)) := by
    rw [quotient_eval_eq_eval₂ I P.f.derivative ha₀]
    simpa [aeval_def] using hxbar.isUnit_derivative_f
  obtain ⟨a, ha, haa₀⟩ :=
    HenselianRing.is_henselian P.f P.monic_f a₀ hroot hderiv
  have hqa : Ideal.Quotient.mk I a = xbar := by
    calc
      Ideal.Quotient.mk I a = Ideal.Quotient.mk I a₀ :=
        Ideal.Quotient.eq.mpr haa₀
      _ = xbar := ha₀
  have hgmap : Ideal.Quotient.mk I (aeval a P.g) = aeval xbar P.g := by
    simpa [aeval_def] using quotient_eval_eq_eval₂ I P.g hqa
  let _ : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (HenselianRing.jac (R := R) (I := I))
  have hgunit : IsUnit (aeval a P.g) := by
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    rw [hgmap]
    exact hxbar.2
  have haMap : P.HasMap a := by
    refine ⟨?_, hgunit⟩
    simpa [aeval_def] using ha
  let τP : P.Ring →ₐ[R] R := P.lift a haMap
  let τ : S →ₐ[R] R := τP.comp P.equivRing.toAlgHom
  refine ⟨τ, ?_⟩
  apply P.hom_ext
  calc
    ((Ideal.Quotient.mkₐ R I).comp τ) P.x = Ideal.Quotient.mk I a := by
      simp [τ, τP]
    _ = xbar := hqa
    _ = σ P.x := by simp [xbar, σP]

#print axioms exists_algHom_lift_of_isStandardEtale

end Pcf.Stacks
