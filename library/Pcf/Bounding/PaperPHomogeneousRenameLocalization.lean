/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPDegreeMultiplyingLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Coordinate renaming on homogeneous projective chart rings
-/

@[expose] public section
namespace Pcf
open MvPolynomial HomogeneousLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- Coordinate renaming on a homogeneous affine chart, with explicitly
named source and target denominators. -/
noncomputable def paperPRenameAwayMap
    (e : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (P Q : MvPolynomial (Fin n ⊕ Unit) K) (hQ : Q = rename e P) :
    Away polyGrade P →+* Away polyGrade Q :=
  paperPDegreeLocalizationMap (𝒜 := polyGrade) (ℬ := polyGrade)
    (rename e).toRingHom 1 (by
      intro m a ha
      change (rename e a).IsHomogeneous (1 * m)
      simpa only [one_mul] using ha.rename_isHomogeneous (f := e)) (by
      rintro x ⟨m, rfl⟩
      change rename e (P ^ m) ∈ Submonoid.powers Q
      rw [map_pow, ← hQ]
      exact ⟨m, rfl⟩)

/-- Renaming acts entrywise on a homogeneous fraction. -/
theorem paperPRenameAwayMap_mk
    (e : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (P Q : MvPolynomial (Fin n ⊕ Unit) K) (hQ : Q = rename e P)
    {k : ℕ} (hP : P.IsHomogeneous k) (m : ℕ)
    (a : MvPolynomial (Fin n ⊕ Unit) K) (ha : a.IsHomogeneous (m * k)) :
    paperPRenameAwayMap e P Q hQ (Away.mk polyGrade hP m a ha) =
      Away.mk polyGrade (show Q.IsHomogeneous k by rw [hQ]; exact hP.rename_isHomogeneous)
        m (rename e a) ha.rename_isHomogeneous := by
  apply val_injective
  simp only [paperPRenameAwayMap, Away.mk, paperPDegreeLocalizationMap_mk,
    paperPDegreeMapFraction, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, val_mk]
  simp only [map_pow, ← hQ]

/-- Renaming coordinates gives an actual isomorphism of homogeneous
localization chart rings. -/
noncomputable def paperPRenameAwayEquiv
    (e : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (P Q : MvPolynomial (Fin n ⊕ Unit) K) (hQ : Q = rename e P) :
    Away polyGrade P ≃+* Away polyGrade Q where
  __ := paperPRenameAwayMap e P Q hQ
  invFun := paperPRenameAwayMap e.symm Q P (by rw [hQ]; simp)
  left_inv x := by
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
    apply val_injective
    change Localization.mk (rename e.symm (rename e c.num.1))
      ⟨rename e.symm (rename e c.den.1), _⟩ = Localization.mk c.num.1 ⟨c.den.1, _⟩
    simp
  right_inv x := by
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
    apply val_injective
    change Localization.mk (rename e (rename e.symm c.num.1))
      ⟨rename e (rename e.symm c.den.1), _⟩ = Localization.mk c.num.1 ⟨c.den.1, _⟩
    simp

@[simp] theorem paperPRenameAwayEquiv_toRingHom
    (e : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (P Q : MvPolynomial (Fin n ⊕ Unit) K) (hQ : Q = rename e P) :
    (paperPRenameAwayEquiv e P Q hQ).toRingHom = paperPRenameAwayMap e P Q hQ := rfl

#print axioms paperPRenameAwayMap
#print axioms paperPRenameAwayMap_mk
#print axioms paperPRenameAwayEquiv
end Pcf
