/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperSquaringRestriction

/-!
# The restriction of `ψ` to `H_i` is squaring on `ℙ^{N-1}`, `ex:squaring-PN`

The closed immersion `ι : ℙ^{N-1} → ℙ^N` onto `H_i` intertwines coordinatewise
squaring: `ψ' ≫ ι = ι ≫ ψ`. The identity is checked on the charts
`D₊(y_k^2) = D₊(y_k)` of `ℙ^{N-1}`, where both composites are `Spec` of explicit
maps of degree-zero homogeneous localizations. Consequently, under the canonical
identification of `ℙ^{N-1}` with the reduced closure subscheme of `H_i`, the actual
restriction `invariantClosureMap` of `ψ` to `H_i` is coordinatewise squaring on
`ℙ^{N-1}`.
-/

@[expose] public section
namespace Pcf.Examples.CharZeroPaperSquaringRestriction
open MvPolynomial AlgebraicGeometry CategoryTheory HomogeneousLocalization Pcf.PaperCharZero
open Pcf.Examples.CharZeroPaperSquaringProjective Pcf.Examples.CharZeroPaperSquaringBranch
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {m : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "gradeA" => MvPolynomial.homogeneousSubmodule (Fin (m + 1) ⊕ Unit) K
local notation "gradeB" => MvPolynomial.homogeneousSubmodule (Fin m ⊕ Unit) K
local notation "PolyA" => MvPolynomial (Fin (m + 1) ⊕ Unit) K
local notation "PolyB" => MvPolynomial (Fin m ⊕ Unit) K
local notation "sqA" => squaringForms (K := K) (n := m + 1)
local notation "sqB" => squaringForms (K := K) (n := m)

/-- Setting `x_i = 0` commutes with squaring the coordinates. -/
theorem dropHom_aeval_squaring (i : Fin (m + 1) ⊕ Unit) (P : PolyA) :
    dropHom (K := K) i (aeval squaringForms P) = aeval squaringForms (dropHom i P) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.coe_comp, Function.comp_apply, aeval_X, dropHom_X, squaringForms, map_pow]
  unfold dropImage
  cases dropEquiv i j <;> simp [squaringForms]

/-- The value of the chart map of the projective morphism on a fraction. -/
theorem projFormsAwayMap_mk_val {n : ℕ} (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) {e : ℕ} (P : MvPolynomial (Fin n ⊕ Unit) K)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K e) (k : ℕ)
    (a : MvPolynomial (Fin n ⊕ Unit) K)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K (k • e)) :
    (projFormsAwayMap F d hF P (Away.mk _ hP k a ha)).val =
      Localization.mk (aeval F a) ⟨aeval F P ^ k, by use k⟩ := by
  simp only [projFormsAwayMap, degreeMulLocalizationMap_val, Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']
  simp

/-- The chart map of the projective morphism on a fraction, as a fraction. -/
theorem projFormsAwayMap_mk {n : ℕ} (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) {e : ℕ} (P : MvPolynomial (Fin n ⊕ Unit) K)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K e) (k : ℕ)
    (a : MvPolynomial (Fin n ⊕ Unit) K)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K (k • e)) :
    projFormsAwayMap F d hF P (Away.mk _ hP k a ha) =
      Away.mk _ (projForms_degreeMap F d hF e P hP) k (aeval F a) (by
        have h := projForms_degreeMap F d hF _ a ha
        have hdeg : k • (d * e) = d * (k • e) := by simp only [smul_eq_mul]; ring
        rwa [hdeg]) := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [projFormsAwayMap_mk_val, Away.val_mk]

/-- `ex:squaring-PN`: the embedding of `ℙ^{N-1}` onto `H_i` intertwines coordinatewise
squaring on `ℙ^{N-1}` with coordinatewise squaring on `ℙ^N`. -/
theorem squaringMap_comp_hyperplaneEmbedding (i : Fin (m + 1) ⊕ Unit) :
    squaringMap (K := K) (n := m) ≫ hyperplaneEmbedding i =
      hyperplaneEmbedding i ≫ squaringMap (K := K) (n := m + 1) := by
  apply (projFormsHomogeneousOpenCover (squaringForms (K := K) (n := m)) 2 two_pos
    squaringForms_isHomogeneous squaringForms_cover).hom_ext
  intro k
  let j := dropEmb i k
  let g := dropGradedHom (K := K) i
  have hf := irrelevant_le_map_of_surjective g (dropGradedHom_surjective i)
  have hXj : (X j : PolyA) ∈ gradeA 1 := isHomogeneous_X K j
  have hXk : (X k : PolyB) ∈ gradeB 1 := isHomogeneous_X K k
  have h1 : (1 : PolyB) ∈ gradeB 0 := SetLike.GradedOne.one_mem
  have hsqA : aeval (R := K) sqA (X j) ∈ gradeA (2 * 1) :=
    projForms_degreeMap _ 2 squaringForms_isHomogeneous 1 _ hXj
  have hsqB : aeval (R := K) sqB (X k) ∈ gradeB (2 * 1) :=
    projForms_degreeMap _ 2 squaringForms_isHomogeneous 1 _ hXk
  -- transport between equal chart elements
  have ex1 : (X k : PolyB) = g (X j) * 1 := by
    rw [mul_one]; exact (dropHom_X_dropEmb i k).symm
  have ex2 : aeval (R := K) sqB (X k) =
      g (aeval (R := K) sqA (X j)) * 1 := by
    rw [mul_one]
    change _ = dropHom i _
    rw [dropHom_aeval_squaring, dropHom_X_dropEmb]
  have T1 : Spec.map (CommRingCat.ofHom (awayMap gradeB h1 ex1)) ≫
      AlgebraicGeometry.Proj.awayι gradeB (g (X j)) (g.2 hXj) Nat.zero_lt_one =
      AlgebraicGeometry.Proj.awayι gradeB (X k) hXk Nat.zero_lt_one :=
    AlgebraicGeometry.Proj.SpecMap_awayMap_awayι gradeB (g.2 hXj) Nat.zero_lt_one h1 ex1
  have T2 : Spec.map (CommRingCat.ofHom (awayMap gradeB h1 ex2)) ≫
      AlgebraicGeometry.Proj.awayι gradeB (g (aeval (R := K) sqA (X j))) (g.2 hsqA)
        (Nat.mul_pos two_pos Nat.zero_lt_one) =
      AlgebraicGeometry.Proj.awayι gradeB (aeval (R := K) sqB (X k)) hsqB
        (Nat.mul_pos two_pos Nat.zero_lt_one) :=
    AlgebraicGeometry.Proj.SpecMap_awayMap_awayι gradeB (g.2 hsqA)
      (Nat.mul_pos two_pos Nat.zero_lt_one) h1 ex2
  have C1 := AlgebraicGeometry.Proj.awayι_comp_map g hf Nat.zero_lt_one (X j) hXj
  have C2 := AlgebraicGeometry.Proj.awayι_comp_map g hf (Nat.mul_pos two_pos Nat.zero_lt_one)
    (aeval (R := K) sqA (X j)) hsqA
  have SB := projForms_awayι_comp_map (squaringForms (K := K) (n := m)) 2 two_pos
    squaringForms_isHomogeneous squaringForms_cover Nat.zero_lt_one (X k) hXk
  have SA := projForms_awayι_comp_map (squaringForms (K := K) (n := m + 1)) 2 two_pos
    squaringForms_isHomogeneous squaringForms_cover Nat.zero_lt_one (X j) hXj
  change AlgebraicGeometry.Proj.awayι gradeB (aeval (R := K) sqB (X k)) hsqB
      (Nat.mul_pos two_pos Nat.zero_lt_one) ≫ squaringMap ≫ hyperplaneEmbedding i =
    AlgebraicGeometry.Proj.awayι gradeB (aeval (R := K) sqB (X k)) hsqB
      (Nat.mul_pos two_pos Nat.zero_lt_one) ≫ hyperplaneEmbedding i ≫ squaringMap
  calc _ = Spec.map (CommRingCat.ofHom (projFormsAwayMap squaringForms 2
          squaringForms_isHomogeneous (X k))) ≫
        Spec.map (CommRingCat.ofHom (awayMap gradeB h1 ex1)) ≫
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map g (X j))) ≫
        AlgebraicGeometry.Proj.awayι gradeA (X j) hXj Nat.zero_lt_one := by
          rw [← Category.assoc]
          erw [SB]
          rw [Category.assoc, ← T1, Category.assoc]
          erw [C1]
    _ = Spec.map (CommRingCat.ofHom (awayMap gradeB h1 ex2)) ≫
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.Away.map g (aeval (R := K) sqA (X j)))) ≫
        Spec.map (CommRingCat.ofHom (projFormsAwayMap squaringForms 2
          squaringForms_isHomogeneous (X j))) ≫
        AlgebraicGeometry.Proj.awayι gradeA (X j) hXj Nat.zero_lt_one := by
          simp only [← Spec.map_comp_assoc]
          congr 2
          apply CommRingCat.hom_ext
          apply RingHom.ext
          intro z
          obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective gradeA hXj z
          apply HomogeneousLocalization.val_injective
          simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
            Function.comp_apply, Away.map_mk, awayMap_mk, projFormsAwayMap_mk, Away.val_mk]
          simp only [one_pow, mul_one]
          congr 1
          exact (dropHom_aeval_squaring i a).symm
    _ = _ := by
          symm
          rw [← T2, Category.assoc]
          erw [AlgebraicGeometry.Proj.awayι_comp_map_assoc g hf
            (Nat.mul_pos two_pos Nat.zero_lt_one) _ hsqA]
          erw [SA]

/-- `ex:squaring-PN`: under the identification `hyperplaneSubschemeIso` of `ℙ^{N-1}`
with the reduced closure subscheme of `H_i`, the actual restriction of `ψ` to `H_i`
is coordinatewise squaring on `ℙ^{N-1}`. -/
theorem hyperplane_restriction_eq_squaring (i : Fin (m + 1) ⊕ Unit) :
    (hyperplaneSubschemeIso (K := K) i).hom ≫
        (hyperplaneDivisor (K := K) (n := m + 1) i).invariantClosureMap squaringMap
          (squaringMap_hyperplane i) =
      squaringMap (K := K) (n := m) ≫ (hyperplaneSubschemeIso (K := K) i).hom := by
  rw [← cancel_mono (pointClosureIdealSheaf (hyperplane (K := K) (n := m + 1) i)).subschemeι]
  have hres : (hyperplaneDivisor (K := K) (n := m + 1) i).invariantClosureMap squaringMap
        (squaringMap_hyperplane i) ≫
        (pointClosureIdealSheaf (hyperplane (K := K) (n := m + 1) i)).subschemeι =
      (pointClosureIdealSheaf (hyperplane (K := K) (n := m + 1) i)).subschemeι ≫
        squaringMap :=
    pointClosureSubschemeMap_subschemeι _ _ _ _
  rw [Category.assoc, hres, ← Category.assoc, hyperplaneSubschemeIso_hom_ι, Category.assoc,
    hyperplaneSubschemeIso_hom_ι]
  exact (squaringMap_comp_hyperplaneEmbedding i).symm

#print axioms dropHom_aeval_squaring
#print axioms projFormsAwayMap_mk_val
#print axioms projFormsAwayMap_mk
#print axioms squaringMap_comp_hyperplaneEmbedding
#print axioms hyperplane_restriction_eq_squaring

end Pcf.Examples.CharZeroPaperSquaringRestriction
