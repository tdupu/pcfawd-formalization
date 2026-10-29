/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianFinitePresentation
public import Pcf.Bounding.CriticalLoci
public import Pcf.Stacks.Purity.Tag0BMBScheme

/-!
# Étaleness and the homogeneous Jacobian of the global projective morphism

This is the first assertion of `paper-p.tex`, Lemma `lem:jacobian`, for
arbitrary scheme points. The étale-at-point predicate is the existing tagged
Stacks Definition 29.37.1(1), with actual affine neighborhoods and étale maps.
The normalized divisorial final assertion is a separate obligation.
-/

@[expose] public section
namespace Pcf
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- The actual global projective morphism is étale at an arbitrary scheme
point exactly where its homogeneous Jacobian does not vanish. Étaleness is
expressed by affine neighborhoods as in the tagged Stacks definition.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPFormsProjective_etaleAt_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) (hdK : (d : K) ≠ 0)
    (x : AlgebraicGeometry.Proj polyGrade) :
    Stacks.IsStacksEtaleAt (paperPFormsProjectiveSchemeMap F d hd hF hcover) x ↔
      Matrix.det (fun i j => pderiv j (F i)) ∉ x.asHomogeneousIdeal := by
  rw [← paperPFormsProjective_stalk_formallyEtale_iff F d hd hF hcover hdK x]
  constructor
  · rintro ⟨V, hV, U, hU, hVU, hx, hφ⟩
    algebraize [((paperPFormsProjectiveSchemeMap F d hd hF hcover).appLE U V hVU).hom]
    exact (formallyEtale_stalkMap_iff U hU V hV hVU hx).mpr
      (inferInstanceAs (Algebra.IsEtaleAt _ _))
  · intro h
    obtain ⟨U, hU, V, hV, hVU, hx, hφ⟩ :=
      exists_etale_of_formallyEtale_stalk
        (paperPFormsProjectiveSchemeMap F d hd hF hcover) x h
    exact ⟨V, hV, U, hU, hVU, hx, hφ⟩

/-- The full actual non-étale stalk locus of the global projective map is
the projective zero locus of the homogeneous Jacobian determinant.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPFormsProjective_nonEtaleLocus_eq_zeroLocus
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) (hdK : (d : K) ≠ 0) :
    schemeNonEtaleLocus (paperPFormsProjectiveSchemeMap F d hd hF hcover) =
      ProjectiveSpectrum.zeroLocus polyGrade
        {Matrix.det (fun i j => pderiv j (F i))} := by
  ext x
  simp only [schemeNonEtaleLocus, SchemeStalkNotFormallyEtaleAt,
    Set.mem_ofPred_eq]
  rw [paperPFormsProjective_stalk_formallyEtale_iff F d hd hF hcover hdK x]
  change (¬¬ Matrix.det (fun i j => pderiv j (F i)) ∈ x.asHomogeneousIdeal) ↔
    ({Matrix.det (fun i j => pderiv j (F i))} : Set (MvPolynomial (Fin n ⊕ Unit) K)) ⊆
      (x.asHomogeneousIdeal : Set (MvPolynomial (Fin n ⊕ Unit) K))
  simp only [not_not, Set.singleton_subset_iff]
  rfl

/-- At every actual codimension-one point of projective space, failure of
formal étaleness is exactly vanishing of the homogeneous Jacobian. This is
the divisorial stalk locus, before comparison with normalization weights.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPFormsProjective_divisorNonEtaleLocus_eq
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) (hdK : (d : K) ≠ 0) :
    schemeDivisorNonEtaleLocus (paperPFormsProjectiveSchemeMap F d hd hF hcover) =
      {x : SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade) |
        Matrix.det (fun i j => pderiv j (F i)) ∈ x.1.asHomogeneousIdeal} := by
  ext x
  rw [mem_schemeDivisorNonEtaleLocus_iff,
    paperPFormsProjective_stalk_formallyEtale_iff F d hd hF hcover hdK x.1]
  exact not_not

#print axioms paperPFormsProjective_etaleAt_iff
#print axioms paperPFormsProjective_nonEtaleLocus_eq_zeroLocus
#print axioms paperPFormsProjective_divisorNonEtaleLocus_eq
end Pcf
