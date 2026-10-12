/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Pcf.Stacks.Purity.GabberPolynomialSplit

/-!
# Extracting an idempotent from Gabber's coprime factorization

Stacks Tag `09XI`, implication `(5) ⇒ (2)`, uses Lemma `0EM0` to produce a special polynomial
annihilating a distinguished element of a finite subalgebra of the integral closure.  The
Gabber root splits that polynomial into coprime factors.  Evaluating a Bezout idempotent for
those factors produces the required idempotent in every algebra in which the distinguished
element remains a root.

This file formalizes that extraction step.  The remaining upstream input is exactly the
finite-subalgebra/integral-closure construction that supplies the special polynomial in `0EM0`;
no idempotent lift is assumed here.
-/

noncomputable section

open Polynomial

universe u v

namespace Pcf.Stacks

variable {R : Type u} [CommRing R]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- A root in an `R`-algebra of the special polynomial from Stacks Tag `0EM0` yields an
idempotent lifting the same residue idempotent.

This is the explicit Bezout-idempotent form of the Chinese-remainder splitting used in the last
paragraph of Tag `09XI`, implication `(5) ⇒ (2)`. -/
theorem exists_isIdempotentElem_sub_mem_of_aeval_eq_zero_of_gabberPolynomial
    (I : Ideal R) [HenselianRing R I]
    (b : B)
    (hb : IsIdempotentElem
      (Ideal.Quotient.mk (I.map (algebraMap R B)) b))
    (f : R[X]) (hf : f.Monic) (n : ℕ) (hn : 1 ≤ n)
    (hred : f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1))
    (hroot : aeval b f = 0) :
    ∃ e : B, IsIdempotentElem e ∧ e - b ∈ I.map (algebraMap R B) := by
  obtain ⟨a, g, haI, _hgmonic, hfactor, hgmap, hcoprime⟩ :=
    exists_coprime_factorization_of_map_eq_X_pow_mul_X_sub_one I f hf n hn hred
  obtain ⟨u, v, huv⟩ := hcoprime
  let e : B := aeval b (v * g)
  let d : B := aeval b (u * (X - C a))
  have hsum : d + e = 1 := by
    dsimp [d, e]
    rw [← map_add, huv, map_one]
  have hprod : d * e = 0 := by
    dsimp [d, e]
    rw [← map_mul]
    have hpoly : (u * (X - C a)) * (v * g) = (u * v) * f := by
      rw [hfactor]
      ring
    rw [hpoly, map_mul, hroot, mul_zero]
  have he : IsIdempotentElem e := by
    change e * e = e
    calc
      e * e = (1 - d) * e := by rw [← hsum]; ring
      _ = e := by rw [sub_mul, hprod]; ring
  let J : Ideal B := I.map (algebraMap R B)
  let qB : B →+* B ⧸ J := Ideal.Quotient.mk J
  let coeffMap : R →+* B ⧸ J := qB.comp (algebraMap R B)
  let phi : R ⧸ I →+* B ⧸ J :=
    Ideal.quotientMap J (algebraMap R B) Ideal.le_comap_map
  have hphi : phi.comp (Ideal.Quotient.mk I) = coeffMap := by
    dsimp [phi, coeffMap, qB, J]
    exact Ideal.quotientMap_comp_mk Ideal.le_comap_map
  have ha_bar : coeffMap a = 1 := by
    change Ideal.Quotient.mk J (algebraMap R B a) = 1
    apply (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := J) _).mpr
    change algebraMap R B a - 1 ∈ J
    simpa only [map_sub, map_one] using
      (Ideal.mem_map_of_mem (algebraMap R B) haI)
  have hgmapB : g.map coeffMap = X ^ n := by
    calc
      g.map coeffMap = g.map (phi.comp (Ideal.Quotient.mk I)) := by rw [hphi]
      _ = (g.map (Ideal.Quotient.mk I)).map phi := by rw [map_map]
      _ = (X ^ n).map phi := by rw [hgmap]
      _ = X ^ n := by simp
  let bbar : B ⧸ J := qB b
  have hg_eval_bar : g.eval₂ coeffMap bbar = bbar := by
    rw [eval₂_eq_eval_map, hgmapB, eval_pow, eval_X,
      hb.pow_eq (Nat.ne_of_gt hn)]
  have hbezout_bar :
      u.eval₂ coeffMap bbar * (bbar - 1) + v.eval₂ coeffMap bbar * bbar = 1 := by
    have h := congrArg (fun p : R[X] ↦ p.eval₂ coeffMap bbar) huv
    simpa [ha_bar, hg_eval_bar] using h
  have hvb : v.eval₂ coeffMap bbar * bbar = bbar := by
    apply sub_eq_zero.mp
    calc
      v.eval₂ coeffMap bbar * bbar - bbar =
          bbar *
              (u.eval₂ coeffMap bbar * (bbar - 1) +
                v.eval₂ coeffMap bbar * bbar - 1) -
            (u.eval₂ coeffMap bbar + v.eval₂ coeffMap bbar) *
              (bbar * bbar - bbar) := by ring
      _ = 0 := by rw [hbezout_bar, hb.eq]; ring
  have he_bar : qB e = bbar := by
    dsimp [e]
    rw [aeval_def, Polynomial.hom_eval₂, eval₂_mul, hg_eval_bar, hvb]
  refine ⟨e, he, ?_⟩
  change e - b ∈ J
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, he_bar, sub_self]

#print axioms exists_isIdempotentElem_sub_mem_of_aeval_eq_zero_of_gabberPolynomial

end Pcf.Stacks
