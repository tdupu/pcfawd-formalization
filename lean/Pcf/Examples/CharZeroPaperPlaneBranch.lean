/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveFormsCritical
public import Pcf.Examples.CharZeroPaperPlaneProjective

/-!
# Critical, branch and postcritical divisors of `ex:koch` and `ex:dupont`

Over a field of characteristic zero, for the actual endomorphisms of the
projective plane constructed in `CharZeroPaperPlaneProjective`, with the
paper's normalized critical and branch divisors (`def:crit-branch` of
`paper.tex`, computed on the actual canonical normalization):

* Belk–Koch: the Jacobian determinant is `8xyz`; the critical divisors are
  `H_0, H_1, H_2`; the branch divisors are `H_2, M_2, M_1`; the postcritical
  set is exactly the six lines, so the map is PCF.
* Dupont: the Jacobian determinant is `32 L_0 L_1 L_2`; the critical divisors
  are exactly the lines `L⁻¹(H_i) = V(L_i)`; the branch divisors are the `H_i`;
  the postcritical set is exactly the six lines, so the map is PCF.
-/

@[expose] public section
namespace Pcf.Examples.CharZeroPaperPlaneBranch
open MvPolynomial AlgebraicGeometry CategoryTheory Pcf.PaperCharZero
open Pcf.Examples.CharZeroPaperSquaringProjective Pcf.Examples.CharZeroPaperPlaneProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "planeGrade" => MvPolynomial.homogeneousSubmodule (Fin 2 ⊕ Unit) K
local notation "Plane" => MvPolynomial (Fin 2 ⊕ Unit) K

/-- The plane coordinates `x, y, z` as `Fin 3`. -/
def planeEquiv : Fin 2 ⊕ Unit ≃ Fin 3 where
  toFun := Sum.elim (fun i => i.castSucc) fun _ => 2
  invFun := ![ix, iy, iz]
  left_inv i := by rcases i with i | u <;> [fin_cases i; skip] <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The `3 × 3` determinant expansion in the plane coordinates. -/
theorem det_plane {R : Type*} [CommRing R] (A : Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) R) :
    A.det = A ix ix * A iy iy * A iz iz - A ix ix * A iy iz * A iz iy
      - A ix iy * A iy ix * A iz iz + A ix iy * A iy iz * A iz ix
      + A ix iz * A iy ix * A iz iy - A ix iz * A iy iy * A iz ix := by
  rw [← Matrix.det_reindex_self planeEquiv A, Matrix.det_fin_three]
  rfl

/-- The Belk–Koch Jacobian determinant `8xyz`. -/
theorem kochForms_jacobian :
    Matrix.det (fun i j => pderiv j (kochForms (K := K) i)) = 8 * (X ix * X iy * X iz) := by
  refine (det_plane (Matrix.of fun i j => pderiv j (kochForms (K := K) i))).trans ?_
  simp [kochForms, pderiv_X]
  ring

/-- Dupont's Jacobian determinant `32 L_0 L_1 L_2`. -/
theorem dupontForms_jacobian :
    Matrix.det (fun i j => pderiv j (dupontForms (K := K) i)) =
      32 * (dupontLinear ix * dupontLinear iy * dupontLinear iz) := by
  refine (det_plane (Matrix.of fun i j => pderiv j (dupontForms (K := K) i))).trans ?_
  simp [dupontForms, dupontLinear, pderiv_X]
  ring

/-- A unit times a product of three elements lies in a prime ideal exactly when
one of the factors does. -/
theorem unit_mul_three_mem_iff {R : Type*} [CommRing R] (I : Ideal R) [hI : I.IsPrime]
    {c : R} (hc : IsUnit c) (a b e : R) :
    c * (a * b * e) ∈ I ↔ a ∈ I ∨ b ∈ I ∨ e ∈ I := by
  have hc' : c ∉ I := fun h => hI.ne_top (Ideal.eq_top_of_isUnit_mem _ h hc)
  constructor
  · intro h
    rcases hI.mem_or_mem h with h | h
    · exact absurd h hc'
    rcases hI.mem_or_mem h with h | h
    · rcases hI.mem_or_mem h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact I.mul_mem_left _ (I.mul_mem_right _ (I.mul_mem_right _ h))
    · exact I.mul_mem_left _ (I.mul_mem_right _ (I.mul_mem_left _ h))
    · exact I.mul_mem_left _ (I.mul_mem_left _ h)

theorem isUnit_numeral [CharZero K] (c : ℕ) [c.AtLeastTwo] :
    IsUnit (OfNat.ofNat c : Plane) := by
  rw [show (OfNat.ofNat c : Plane) = C (OfNat.ofNat c : K) from (map_ofNat C c).symm]
  exact (Ne.isUnit (by simp)).map C

/-! ## The six lines as divisors -/

/-- The six lines `H_0, H_1, H_2, M_0, M_1, M_2` as integral effective divisors. -/
noncomputable def sixLineDivisor [CharZero K] (i : Fin 6) :
    SchemeDivisorPoint (AlgebraicGeometry.Proj planeGrade) :=
  projLineDivisor (sixForms i) (sixForms_isHomogeneous i) (sixForms_ne_zero i) (sixWitness i)
    (sixWitness_not_mem i)

theorem sixLineDivisor_val [CharZero K] (i : Fin 6) :
    (sixLineDivisor (K := K) i).1 = sixLines i := rfl

theorem sixLineDivisor_injective [CharZero K] :
    Function.Injective (sixLineDivisor (K := K)) := fun _ _ h =>
  sixLines_injective (congrArg Subtype.val h)

/-- A divisor contains the `i`-th linear form exactly when it is the `i`-th line. -/
theorem sixForms_mem_iff [CharZero K] (P : SchemeDivisorPoint (AlgebraicGeometry.Proj planeGrade))
    (i : Fin 6) :
    sixForms i ∈ P.1.asHomogeneousIdeal ↔ P = sixLineDivisor i :=
  proj_divisor_mem_iff_eq_projLinePoint _ _ _ _ _ P

/-! ## Belk–Koch -/

instance kochMap_isFinite : IsFinite (kochMap (K := K)) := kochMap_isFinite_surjective.1

instance kochMap_isDominant : IsDominant (kochMap (K := K)) :=
  projFormsProjective_isDominant _ _ _ _ _

instance kochMap_locallyOfFinitePresentation : LocallyOfFinitePresentation (kochMap (K := K)) :=
  projFormsProjectiveSchemeMap_locallyOfFinitePresentation _ _ _ _ _

theorem kochForms_jacobian_mem_iff [CharZero K]
    (P : SchemeDivisorPoint (AlgebraicGeometry.Proj planeGrade)) :
    Matrix.det (fun i j => pderiv j (kochForms (K := K) i)) ∈ P.1.asHomogeneousIdeal ↔
      P = sixLineDivisor 0 ∨ P = sixLineDivisor 1 ∨ P = sixLineDivisor 2 := by
  have hp : P.1.asHomogeneousIdeal.toIdeal.IsPrime := P.1.isPrime
  rw [kochForms_jacobian]
  change _ ∈ P.1.asHomogeneousIdeal.toIdeal ↔ _
  rw [unit_mul_three_mem_iff _ (isUnit_numeral 8)]
  exact or_congr (sixForms_mem_iff P 0) (or_congr (sixForms_mem_iff P 1) (sixForms_mem_iff P 2))

/-- `ex:koch`: the normalized critical divisors are exactly `H_0, H_1, H_2`. -/
theorem kochMap_criticalDivisors [CharZero K] :
    schemeNormalizedCriticalDivisors K (kochMap (K := K)) =
      {sixLineDivisor 0, sixLineDivisor 1, sixLineDivisor 2} := by
  ext P
  have h := projForms_mem_criticalDivisors_iff kochForms 2 two_pos kochForms_isHomogeneous
    kochForms_cover P
  refine h.trans ?_
  rw [kochForms_jacobian_mem_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

/-- The divisor step of the Belk–Koch map on the six lines. -/
def kochPerm : Fin 6 → Fin 6 := ![2, 5, 4, 0, 3, 1]

theorem kochMap_step [CharZero K] (i : Fin 6) :
    schemeDivisorMap (kochMap (K := K)) (coheight_apply_eq_one_of_finiteType _ K)
      (sixLineDivisor i) = sixLineDivisor (kochPerm i) := by
  obtain ⟨h02, h24, h43, h30, h15, h51⟩ := kochMap_itinerary (K := K)
  apply Subtype.ext
  change kochMap (sixLines i) = sixLines (kochPerm i)
  fin_cases i
  · exact h02
  · exact h15
  · exact h24
  · exact h30
  · exact h43
  · exact h51

theorem kochMap_iterate_step [CharZero K] (m : ℕ) (i : Fin 6) :
    (schemeDivisorMap (kochMap (K := K)) (coheight_apply_eq_one_of_finiteType _ K))^[m]
      (sixLineDivisor i) = sixLineDivisor (kochPerm^[m] i) := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, kochMap_step, ih]

/-- `ex:koch`: the normalized branch divisors are `H_2, M_2, M_1`.

Manuscript: `ex:koch` (Example 4.2). -/
theorem kochMap_branch [CharZero K] :
    schemeNormalizedBranch K (kochMap (K := K)) =
      {sixLineDivisor 2, sixLineDivisor 5, sixLineDivisor 4} := by
  ext E
  have h := projForms_mem_branch_iff kochForms 2 two_pos kochForms_isHomogeneous
    kochForms_cover E
  refine h.trans ?_
  simp only [kochForms_jacobian_mem_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hstep (i : Fin 6) :
      kochMap (K := K) (sixLineDivisor i).1 = (sixLineDivisor (kochPerm i)).1 :=
    congrArg Subtype.val (kochMap_step i)
  constructor
  · rintro ⟨P, hPE, rfl | rfl | rfl⟩
    · exact Or.inl (Subtype.ext ((hstep 0).symm.trans hPE).symm)
    · exact Or.inr (Or.inl (Subtype.ext ((hstep 1).symm.trans hPE).symm))
    · exact Or.inr (Or.inr (Subtype.ext ((hstep 2).symm.trans hPE).symm))
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, hstep 0, Or.inl rfl⟩
    · exact ⟨_, hstep 1, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, hstep 2, Or.inr (Or.inr rfl)⟩

/-- `ex:koch`: the postcritical set is exactly the six lines.

Manuscript: `ex:koch` (Example 4.2). -/
theorem kochMap_postcritical [CharZero K] :
    schemeNormalizedPostcriticalSet K (kochMap (K := K)) = Set.range sixLineDivisor := by
  rw [schemeNormalizedPostcriticalSet_eq_iUnion, kochMap_branch]
  ext E
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_range]
  constructor
  · rintro ⟨m, P, hP, rfl⟩
    rcases hP with rfl | rfl | rfl <;> exact ⟨_, (kochMap_iterate_step m _).symm⟩
  · rintro ⟨j, rfl⟩
    have hreach : ∃ m : ℕ, ∃ i : Fin 6, (i = 2 ∨ i = 5 ∨ i = 4) ∧ kochPerm^[m] i = j := by
      fin_cases j
      · exact ⟨2, 4, by decide, by decide⟩
      · exact ⟨1, 5, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide⟩
      · exact ⟨1, 4, by decide, by decide⟩
      · exact ⟨0, 4, by decide, by decide⟩
      · exact ⟨0, 5, by decide, by decide⟩
    obtain ⟨m, i, hi, rfl⟩ := hreach
    refine ⟨m, sixLineDivisor i, ?_, kochMap_iterate_step m i⟩
    rcases hi with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- `ex:koch`: the Belk–Koch map is PCF for the paper's normalized branch locus.

Manuscript: `ex:koch` (Example 4.2). -/
theorem kochMap_isPCF [CharZero K] : IsNormalizedPCF K (kochMap (K := K)) := by
  unfold IsNormalizedPCF
  rw [kochMap_postcritical]
  exact Set.finite_range _

/-! ## Dupont -/

instance dupontMap_isFinite [CharZero K] : IsFinite (dupontMap (K := K)) :=
  dupontMap_isFinite_surjective.1

instance dupontMap_isDominant [CharZero K] : IsDominant (dupontMap (K := K)) :=
  projFormsProjective_isDominant _ _ _ _ _

instance dupontMap_locallyOfFinitePresentation [CharZero K] :
    LocallyOfFinitePresentation (dupontMap (K := K)) :=
  projFormsProjectiveSchemeMap_locallyOfFinitePresentation _ _ _ _ _

/-- The line `L⁻¹(H_i) = V(L_i)` as an integral effective divisor. -/
noncomputable def criticalLineDivisor [CharZero K] (i : Fin 2 ⊕ Unit) :
    SchemeDivisorPoint (AlgebraicGeometry.Proj planeGrade) :=
  projLineDivisor (dupontLinear i) (dupontLinear_isHomogeneous i) (dupontLinear_ne_zero i) ix
    (X_not_mem_span_dupontLinear i)

theorem dupontLinear_mem_iff [CharZero K]
    (P : SchemeDivisorPoint (AlgebraicGeometry.Proj planeGrade)) (i : Fin 2 ⊕ Unit) :
    dupontLinear i ∈ P.1.asHomogeneousIdeal ↔ P = criticalLineDivisor i :=
  proj_divisor_mem_iff_eq_projLinePoint _ _ _ _ _ P

theorem dupontForms_jacobian_mem_iff [CharZero K]
    (P : SchemeDivisorPoint (AlgebraicGeometry.Proj planeGrade)) :
    Matrix.det (fun i j => pderiv j (dupontForms (K := K) i)) ∈ P.1.asHomogeneousIdeal ↔
      ∃ i, P = criticalLineDivisor i := by
  have hp : P.1.asHomogeneousIdeal.toIdeal.IsPrime := P.1.isPrime
  rw [dupontForms_jacobian]
  change _ ∈ P.1.asHomogeneousIdeal.toIdeal ↔ _
  rw [unit_mul_three_mem_iff _ (isUnit_numeral 32)]
  constructor
  · rintro (h | h | h)
    · exact ⟨ix, (dupontLinear_mem_iff P ix).mp h⟩
    · exact ⟨iy, (dupontLinear_mem_iff P iy).mp h⟩
    · exact ⟨iz, (dupontLinear_mem_iff P iz).mp h⟩
  · rintro ⟨i, hi⟩
    have h := (dupontLinear_mem_iff P i).mpr hi
    rcases i with i | u
    · fin_cases i
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- `ex:dupont`: the normalized critical divisors are exactly the lines
`L⁻¹(H_i)`.

Manuscript: `ex:dupont` (Example 4.3). -/
theorem dupontMap_criticalDivisors [CharZero K] :
    schemeNormalizedCriticalDivisors K (dupontMap (K := K)) = Set.range criticalLineDivisor := by
  ext P
  have h := projForms_mem_criticalDivisors_iff dupontForms 2 two_pos dupontForms_isHomogeneous
    dupontForms_cover P
  refine h.trans ?_
  rw [dupontForms_jacobian_mem_iff]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

/-- The index of the coordinate line `H_i` among the six lines. -/
def hyperplaneIndex : Fin 2 ⊕ Unit → Fin 6 := Sum.elim ![0, 1] fun _ => 2

theorem dupontMap_criticalLine_divisor [CharZero K] (i : Fin 2 ⊕ Unit) :
    dupontMap (K := K) (criticalLineDivisor i).1 = (sixLineDivisor (hyperplaneIndex i)).1 := by
  obtain ⟨hx, hy, hz⟩ := hyperplane_eq_sixLines (K := K)
  refine (dupontMap_criticalLine i).trans ?_
  rcases i with i | u
  · fin_cases i
    · exact hx
    · exact hy
  · exact hz

/-- `ex:dupont`: the normalized branch divisors are exactly `H_0, H_1, H_2`. -/
theorem dupontMap_branch [CharZero K] :
    schemeNormalizedBranch K (dupontMap (K := K)) =
      {sixLineDivisor 0, sixLineDivisor 1, sixLineDivisor 2} := by
  ext E
  have h := projForms_mem_branch_iff dupontForms 2 two_pos dupontForms_isHomogeneous
    dupontForms_cover E
  refine h.trans ?_
  simp only [dupontForms_jacobian_mem_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨P, hPE, i, rfl⟩
    have hE := Subtype.ext ((dupontMap_criticalLine_divisor i).symm.trans hPE)
    rcases i with i | u
    · fin_cases i
      · exact Or.inl hE.symm
      · exact Or.inr (Or.inl hE.symm)
    · exact Or.inr (Or.inr hE.symm)
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, dupontMap_criticalLine_divisor ix, ix, rfl⟩
    · exact ⟨_, dupontMap_criticalLine_divisor iy, iy, rfl⟩
    · exact ⟨_, dupontMap_criticalLine_divisor iz, iz, rfl⟩

/-- The divisor step of Dupont's map on the six lines. -/
def dupontPerm : Fin 6 → Fin 6 := ![3, 4, 5, 5, 3, 4]

theorem dupontMap_step [CharZero K] (i : Fin 6) :
    schemeDivisorMap (dupontMap (K := K)) (coheight_apply_eq_one_of_finiteType _ K)
      (sixLineDivisor i) = sixLineDivisor (dupontPerm i) := by
  obtain ⟨h03, h14, h25, h35, h54, h43⟩ := dupontMap_itinerary (K := K)
  apply Subtype.ext
  change dupontMap (sixLines i) = sixLines (dupontPerm i)
  fin_cases i
  · exact h03
  · exact h14
  · exact h25
  · exact h35
  · exact h43
  · exact h54

theorem dupontMap_iterate_step [CharZero K] (m : ℕ) (i : Fin 6) :
    (schemeDivisorMap (dupontMap (K := K)) (coheight_apply_eq_one_of_finiteType _ K))^[m]
      (sixLineDivisor i) = sixLineDivisor (dupontPerm^[m] i) := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dupontMap_step, ih]

/-- `ex:dupont`: the postcritical set consists exactly of the three `H_i` and the
three `M_i`.

Manuscript: `ex:dupont` (Example 4.3). -/
theorem dupontMap_postcritical [CharZero K] :
    schemeNormalizedPostcriticalSet K (dupontMap (K := K)) = Set.range sixLineDivisor := by
  rw [schemeNormalizedPostcriticalSet_eq_iUnion, dupontMap_branch]
  ext E
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_range]
  constructor
  · rintro ⟨m, P, hP, rfl⟩
    rcases hP with rfl | rfl | rfl <;> exact ⟨_, (dupontMap_iterate_step m _).symm⟩
  · rintro ⟨j, rfl⟩
    have hreach : ∃ m : ℕ, ∃ i : Fin 6, (i = 0 ∨ i = 1 ∨ i = 2) ∧ dupontPerm^[m] i = j := by
      fin_cases j
      · exact ⟨0, 0, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide⟩
      · exact ⟨1, 0, by decide, by decide⟩
      · exact ⟨1, 1, by decide, by decide⟩
      · exact ⟨1, 2, by decide, by decide⟩
    obtain ⟨m, i, hi, rfl⟩ := hreach
    refine ⟨m, sixLineDivisor i, ?_, dupontMap_iterate_step m i⟩
    rcases hi with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- `ex:dupont`: Dupont's map is PCF for the paper's normalized branch locus.

Manuscript: `ex:dupont` (Example 4.3). -/
theorem dupontMap_isPCF [CharZero K] : IsNormalizedPCF K (dupontMap (K := K)) := by
  unfold IsNormalizedPCF
  rw [dupontMap_postcritical]
  exact Set.finite_range _

#print axioms det_plane
#print axioms kochForms_jacobian
#print axioms dupontForms_jacobian
#print axioms sixForms_mem_iff
#print axioms kochMap_criticalDivisors
#print axioms kochMap_step
#print axioms kochMap_branch
#print axioms kochMap_postcritical
#print axioms kochMap_isPCF
#print axioms dupontForms_jacobian_mem_iff
#print axioms dupontMap_criticalDivisors
#print axioms dupontMap_branch
#print axioms dupontMap_step
#print axioms dupontMap_postcritical
#print axioms dupontMap_isPCF
end Pcf.Examples.CharZeroPaperPlaneBranch
