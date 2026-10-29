/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingStandardPiece

/-!
# The canonical maps of `eq:standard-piece`

`Pcf.PaperCharZero.standard_piece` records the identifications of `eq:standard-piece` in
`paper.tex` as bare `Nonempty` ring equivalences. This file shows that the equivalences
constructed there are the canonical ones:

* `C/aC ≅ (R/a)[z]/(z^e)` is an isomorphism of `R`-algebras sending the class of the
  root `z` to the class of the variable `z`;
* `(C/aC)_red ≅ C/zC` sends the class of the class of `c ∈ C` to the class of `c`;
* `C/zC ≅ R/aR` is an isomorphism of `R`-algebras, so it sends the class of `r ∈ R` to
  the class of `r`, and the composite `(C/aC)_red ≅ R/aR` is `R`-linear.
-/

@[expose] public section

namespace Pcf.PaperCharZero

open Polynomial LocalModel

variable {R : Type*} [CommRing R] (u : Rˣ) (a : R) {e : ℕ}

local notation "C" => AdjoinRoot (localPoly u a e)
local notation "I" => Ideal.span ({algebraMap R C a} : Set C)
local notation "J" => Ideal.span ({AdjoinRoot.root (localPoly u a e)} : Set C)

/-- The first identification sends the class of the root `z` to the class of `X`. -/
theorem standardPiece_quotientParameterEquiv_root :
    standardPiece_quotientParameterEquiv u a
        (Ideal.Quotient.mk I (AdjoinRoot.root (localPoly u a e))) =
      Ideal.Quotient.mk _ X := by
  calc _ = Ideal.Quotient.mk (Ideal.span ({X ^ e} : Set (R ⧸ Ideal.span ({a} : Set R))[X]))
        ((X : R[X]).map (Ideal.Quotient.mk _)) := rfl
    _ = _ := by rw [Polynomial.map_X]

/-- The first identification is compatible with the structure maps from `R`. -/
theorem standardPiece_quotientParameterEquiv_algebraMap (r : R) :
    standardPiece_quotientParameterEquiv u a
        (Ideal.Quotient.mk I (algebraMap R C r)) =
      Ideal.Quotient.mk _ (Polynomial.C (Ideal.Quotient.mk _ r)) := by
  calc _ = Ideal.Quotient.mk (Ideal.span ({X ^ e} : Set (R ⧸ Ideal.span ({a} : Set R))[X]))
        ((Polynomial.C r).map (Ideal.Quotient.mk _)) := rfl
    _ = _ := by rw [Polynomial.map_C]

/-- `eq:standard-piece`, first equality, as an isomorphism of `R`-algebras. -/
noncomputable def standardPiece_quotientParameterAlgEquiv :
    (C ⧸ I) ≃ₐ[R] (R ⧸ Ideal.span ({a} : Set R))[X] ⧸
      Ideal.span ({X ^ e} : Set (R ⧸ Ideal.span ({a} : Set R))[X]) :=
  AlgEquiv.ofRingEquiv (f := standardPiece_quotientParameterEquiv u a) fun r => by
    exact standardPiece_quotientParameterEquiv_algebraMap u a r

/-- The reduction identification is induced by the identity of `C`. -/
theorem standardPiece_reductionRootEquiv_mk (he : 1 ≤ e)
    [IsReduced (R ⧸ Ideal.span ({a} : Set R))] (c : C) :
    standardPiece_reductionRootEquiv u a he
        (Ideal.Quotient.mk _ (Ideal.Quotient.mk I c)) =
      Ideal.Quotient.mk J c :=
  rfl

/-- `eq:standard-piece`, with the canonical maps: `C/aC ≅ (R/a)[z]/(z^e)` as `R`-algebras
with `z ↦ z`; `(C/aC)_red ≅ C/zC` is induced by the identity of `C`; and
`C/zC ≅ R/aR` is an `R`-algebra isomorphism, so that the composite reduction
`(C/aC)_red ≅ R/aR` sends the class of each `r ∈ R` to the class of `r`.

Manuscript: `eq:standard-piece` (equation (2)). -/
theorem standard_piece_canonical (he : 1 ≤ e)
    [IsReduced (R ⧸ Ideal.span ({a} : Set R))] :
    (∃ φ : (C ⧸ I) ≃ₐ[R] (R ⧸ Ideal.span ({a} : Set R))[X] ⧸
    Ideal.span ({X ^ e} : Set (R ⧸ Ideal.span ({a} : Set R))[X]),
      φ (Ideal.Quotient.mk I (AdjoinRoot.root (localPoly u a e))) = Ideal.Quotient.mk _ X) ∧
    (∃ ψ : (C ⧸ I) ⧸ nilradical (C ⧸ I) ≃+* C ⧸ J,
      ∀ c : C, ψ (Ideal.Quotient.mk _ (Ideal.Quotient.mk I c)) = Ideal.Quotient.mk J c) ∧
    (∃ χ : (C ⧸ J) ≃ₐ[R] R ⧸ Ideal.span ({a} : Set R),
      ∀ r : R, χ (Ideal.Quotient.mk J (algebraMap R C r)) = Ideal.Quotient.mk _ r) ∧
    (∃ ρ : (C ⧸ I) ⧸ nilradical (C ⧸ I) ≃+* R ⧸ Ideal.span ({a} : Set R),
      ∀ r : R, ρ (Ideal.Quotient.mk _ (Ideal.Quotient.mk I (algebraMap R C r))) =
        Ideal.Quotient.mk _ r) := by
  have hχ : ∀ r : R, quotientRootEquiv u a he (Ideal.Quotient.mk J (algebraMap R C r)) =
      Ideal.Quotient.mk _ r := fun r => by
    exact (quotientRootEquiv u a he).commutes r
  refine ⟨⟨standardPiece_quotientParameterAlgEquiv u a,
      standardPiece_quotientParameterEquiv_root u a⟩,
    ⟨standardPiece_reductionRootEquiv u a he, standardPiece_reductionRootEquiv_mk u a he⟩,
    ⟨quotientRootEquiv u a he, hχ⟩,
    ⟨(standardPiece_reductionRootEquiv u a he).trans
      (quotientRootEquiv u a he).toRingEquiv, fun r => ?_⟩⟩
  rw [RingEquiv.trans_apply, standardPiece_reductionRootEquiv_mk]
  exact hχ r

end Pcf.PaperCharZero

#print axioms Pcf.PaperCharZero.standardPiece_quotientParameterEquiv_root
#print axioms Pcf.PaperCharZero.standardPiece_quotientParameterAlgEquiv
#print axioms Pcf.PaperCharZero.standardPiece_reductionRootEquiv_mk
#print axioms Pcf.PaperCharZero.standard_piece_canonical
