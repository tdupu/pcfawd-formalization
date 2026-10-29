/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryFinitePureStage
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# Polynomial data descend to finite purely inseparable stages

Stacks Project, Tag 04KM constructs its finite purely inseparable alteration
from finitely many coefficients of defining polynomials. This lemma isolates
the finite-coefficient descent from a possibly infinite purely inseparable
ambient extension. It is an input to, rather than a proof of, the generic
geometric-reducedness alteration in `paper-p.tex`, Lemma `lem:primary-fibres`.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

/-- A polynomial over a purely inseparable extension is already defined over
some finite purely inseparable intermediate field. -/
theorem polynomial_descends_to_finite_pure_stage
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    [IsPurelyInseparable K E] (P : Polynomial E) :
    ∃ F : IntermediateField K E,
      FiniteDimensional K F ∧ IsPurelyInseparable K F ∧
        ∃ Q : Polynomial F, Q.map (algebraMap F E) = P := by
  classical
  obtain ⟨F, hfin, hpure, hs⟩ :=
    finite_set_contained_in_finite_pure_subextension K E
      (P.support.image P.coeff)
  have hcoeff (n : ℕ) (hn : n ∈ P.support) : P.coeff n ∈ F :=
    hs (P.coeff n) (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  let Q : Polynomial F :=
    P.support.attach.sum fun n =>
      Polynomial.monomial n (⟨P.coeff n, hcoeff n n.property⟩ : F)
  refine ⟨F, hfin, hpure, Q, ?_⟩
  calc
    Q.map (algebraMap F E) =
        ∑ n ∈ P.support, Polynomial.monomial n (P.coeff n) := by
          dsimp [Q]
          rw [Polynomial.map_sum]
          simp only [Polynomial.map_monomial]
          simp only [IntermediateField.algebraMap_apply]
          exact Finset.sum_attach P.support (fun n => Polynomial.monomial n (P.coeff n))
    _ = P := by
      simpa [Polynomial.sum] using (Polynomial.sum_monomial_eq P)

/-- A separable irreducible monic defining polynomial retains all three
properties at the same finite coefficient stage. -/
theorem separable_irreducible_polynomial_descends_to_finite_pure_stage
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    [IsPurelyInseparable K E] (P : Polynomial E)
    (hmon : P.Monic) (hsep : P.Separable) (hirr : Irreducible P) :
    ∃ F : IntermediateField K E,
      FiniteDimensional K F ∧ IsPurelyInseparable K F ∧
        ∃ Q : Polynomial F,
          Q.map (algebraMap F E) = P ∧ Q.Separable ∧ Irreducible Q := by
  obtain ⟨F, hfin, hpure, Q, hQ⟩ := polynomial_descends_to_finite_pure_stage K E P
  refine ⟨F, hfin, hpure, Q, hQ, ?_, ?_⟩
  · exact (Polynomial.separable_map (algebraMap F E)).mp (hQ ▸ hsep)
  · have hQmon : Q.Monic :=
      Polynomial.monic_of_injective (algebraMap F E).injective (hQ ▸ hmon)
    exact Polynomial.Monic.irreducible_of_irreducible_map
      (algebraMap F E) Q hQmon (hQ ▸ hirr)

#print axioms polynomial_descends_to_finite_pure_stage
#print axioms separable_irreducible_polynomial_descends_to_finite_pure_stage

end Pcf.Bounding.PrimaryFibres
