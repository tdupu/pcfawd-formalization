/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperSquaringProjective
public import Pcf.Examples.CharZeroPaperPlane

/-!
# Projective morphisms of `ex:koch` and `ex:dupont` in `paper.tex`

The projective plane is `Proj K[x, y, z]`, with coordinate index type
`Fin 2 ⊕ Unit`: `x = inl 0`, `y = inl 1`, `z = inr ()`. The displayed
homogeneous formulas are the renamings of `CharZeroPaperPlane.kochPolynomial`
and `CharZeroPaperPlane.dupontPolynomial`.

Both formulas define actual finite surjective endomorphisms of the projective
plane. The six lines `H_0 = V(x)`, `H_1 = V(y)`, `H_2 = V(z)`,
`M_0 = V(x - y)`, `M_1 = V(y - z)`, `M_2 = V(x - z)` are distinct integral
effective divisors, and the line itineraries are equalities of actual scheme
points:

* Belk–Koch: `H_0 → H_2 → M_1 → M_0 → H_0` and `H_1 ↔ M_2`.
* Dupont: `L⁻¹(H_i) → H_i`, `H_i → M_i`, and `M_0 → M_2 → M_1 → M_0`; the
  `H_i` are strictly preperiodic and the `M_i` form a three-cycle.

The identification of the actual critical and branch divisors, and hence of
the postcritical set with the six lines, is not proved here.
-/

@[expose] public section
namespace Pcf.Examples.CharZeroPaperPlaneProjective
open MvPolynomial AlgebraicGeometry Pcf.PaperCharZero
open Pcf.Examples.CharZeroPaperSquaringProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "planeGrade" => MvPolynomial.homogeneousSubmodule (Fin 2 ⊕ Unit) K
local notation "Plane" => MvPolynomial (Fin 2 ⊕ Unit) K

/-- Coordinate indices `x`, `y`, `z` of the projective plane. -/
abbrev ix : Fin 2 ⊕ Unit := Sum.inl 0
abbrev iy : Fin 2 ⊕ Unit := Sum.inl 1
abbrev iz : Fin 2 ⊕ Unit := Sum.inr ()

/-- The index map identifying `Fin 3` with the plane coordinates. -/
def planeIdx : Fin 3 → Fin 2 ⊕ Unit := ![ix, iy, iz]

/-- A homogeneous coordinate vector `(a, b, c)`. -/
def vec (a b c : K) : Fin 2 ⊕ Unit → K := Sum.elim ![a, b] fun _ => c

omit [Field K] in
@[simp] theorem vec_x (a b c : K) : vec a b c ix = a := by simp [vec]
omit [Field K] in
@[simp] theorem vec_y (a b c : K) : vec a b c iy = b := by simp [vec]
omit [Field K] in
@[simp] theorem vec_z (a b c : K) : vec a b c iz = c := by simp [vec]

/-! ## The six lines -/

/-- The six linear forms `x, y, z, x - y, y - z, x - z`. -/
noncomputable def sixForms : Fin 6 → Plane :=
  ![X ix, X iy, X iz, X ix - X iy, X iy - X iz, X ix - X iz]

theorem sixForms_isHomogeneous (i : Fin 6) : (sixForms (K := K) i).IsHomogeneous 1 := by
  fin_cases i <;> simp only [sixForms, Fin.reduceFinMk, Matrix.cons_val] <;>
    first
    | exact isHomogeneous_X K _
    | exact (isHomogeneous_X K _).sub (isHomogeneous_X K _)

/-- One vector on each line and on none of the other five lines. -/
def sixVectors [CharZero K] : Fin 6 → Fin 2 ⊕ Unit → K :=
  ![vec 0 1 2, vec 1 0 2, vec 1 2 0, vec 1 1 2, vec 2 1 1, vec 1 2 1]

/-- A coordinate not divisible by each linear form. -/
def sixWitness : Fin 6 → Fin 2 ⊕ Unit := ![iy, ix, ix, ix, iy, ix]

theorem sixVectors_eval [CharZero K] (i j : Fin 6) :
    eval (sixVectors (K := K) i) (sixForms j) = 0 ↔ i = j := by
  fin_cases i <;> fin_cases j <;> norm_num [sixVectors, sixForms]

theorem sixForms_ne_zero [CharZero K] (i : Fin 6) : sixForms (K := K) i ≠ 0 := by
  intro h
  have := (sixVectors_eval (K := K) (if i = 0 then 1 else 0) i).mp (by simp [h])
  fin_cases i <;> simp_all

theorem sixWitness_not_mem [CharZero K] (i : Fin 6) :
    (X (sixWitness i) : Plane) ∉ Ideal.span {sixForms (K := K) i} := by
  apply not_mem_span_of_eval (sixVectors i) ((sixVectors_eval i i).mpr rfl)
  fin_cases i <;> norm_num [sixVectors, sixWitness]

/-- The six lines as projective points: `H_0, H_1, H_2, M_0, M_1, M_2`. -/
noncomputable def sixLines [CharZero K] (i : Fin 6) : AlgebraicGeometry.Proj planeGrade :=
  projLinePoint (sixForms i) (sixForms_isHomogeneous i) (sixForms_ne_zero i) (sixWitness i)
    (sixWitness_not_mem i)

/-- Each of the six lines is an integral effective divisor. -/
theorem sixLines_coheight [CharZero K] (i : Fin 6) : Order.coheight (sixLines (K := K) i) = 1 :=
  projLinePoint_coheight _ _ _ _ _

/-- The support of each line is the zero locus of its form. -/
theorem sixLines_closure [CharZero K] (i : Fin 6) :
    closure ({sixLines (K := K) i} : Set (AlgebraicGeometry.Proj planeGrade)) =
      ProjectiveSpectrum.zeroLocus planeGrade {sixForms i} :=
  projLinePoint_closure _ _ _ _ _

/-- The six lines are pairwise distinct. -/
theorem sixLines_injective [CharZero K] : Function.Injective (sixLines (K := K)) := by
  intro i j h
  by_contra hij
  exact projLinePoint_ne_of_eval _ _ _ _ _ _ _ _ _ _ (sixVectors i)
    ((sixVectors_eval i i).mpr rfl) (fun h' => hij ((sixVectors_eval i j).mp h')) h

/-! ## The Belk–Koch map -/

/-- The Belk–Koch forms `[x^2 - y^2 : x^2 - z^2 : x^2]`. -/
noncomputable def kochForms : Fin 2 ⊕ Unit → Plane :=
  Sum.elim ![X ix ^ 2 - X iy ^ 2, X ix ^ 2 - X iz ^ 2] fun _ => X ix ^ 2

/-- The forms are the renaming of `CharZeroPaperPlane.kochPolynomial`. -/
theorem kochForms_planeIdx (i : Fin 3) :
    kochForms (K := K) (planeIdx i) =
      rename planeIdx (Pcf.Examples.CharZeroPaperPlane.kochPolynomial (K := K) i) := by
  fin_cases i <;> simp [kochForms, planeIdx, Pcf.Examples.CharZeroPaperPlane.kochPolynomial]

theorem kochForms_isHomogeneous (i : Fin 2 ⊕ Unit) : (kochForms (K := K) i).IsHomogeneous 2 := by
  have hx : (X ix ^ 2 : Plane).IsHomogeneous 2 := by
    simpa using (isHomogeneous_X K ix).pow 2
  have hy : (X iy ^ 2 : Plane).IsHomogeneous 2 := by
    simpa using (isHomogeneous_X K iy).pow 2
  have hz : (X iz ^ 2 : Plane).IsHomogeneous 2 := by
    simpa using (isHomogeneous_X K iz).pow 2
  rcases i with i | u
  · fin_cases i
    · exact hx.sub hy
    · exact hx.sub hz
  · exact hx

/-- The squares of the coordinates are substitutions of the forms. -/
theorem kochForms_sq (i : Fin 2 ⊕ Unit) :
    ∃ P : Plane, (X i : Plane) ^ 2 = aeval (R := K) kochForms P := by
  rcases i with i | u
  · fin_cases i
    · exact ⟨X iz, by simp [kochForms]⟩
    · exact ⟨X iz - X ix, by simp [kochForms]⟩
  · exact ⟨X iz - X iy, by simp [kochForms]⟩

theorem kochForms_cover : FormsCoverProjective (kochForms (K := K)) := by
  have hmem (j : Fin 2 ⊕ Unit) : kochForms (K := K) j ∈ Ideal.span (Set.range kochForms) :=
    Ideal.subset_span (Set.mem_range_self j)
  refine formsCoverProjective_of_pow_mem _ 2 fun i => ?_
  rcases i with i | u
  · fin_cases i
    · have h : (X ix ^ 2 : Plane) = kochForms iz := by simp [kochForms]
      simpa [h] using hmem iz
    · have h : (X iy ^ 2 : Plane) = kochForms iz - kochForms ix := by simp [kochForms]
      simpa [h] using Ideal.sub_mem _ (hmem iz) (hmem ix)
  · have h : (X iz ^ 2 : Plane) = kochForms iz - kochForms iy := by simp [kochForms]
    simpa [h] using Ideal.sub_mem _ (hmem iz) (hmem iy)

/-- The actual Belk–Koch endomorphism `F` of `ℙ^2`. -/
noncomputable def kochMap : AlgebraicGeometry.Proj planeGrade ⟶ AlgebraicGeometry.Proj planeGrade :=
  projFormsProjectiveSchemeMap kochForms 2 two_pos kochForms_isHomogeneous kochForms_cover

/-- `ex:koch`: the displayed triple has no common projective zero and
defines a finite surjective endomorphism of `ℙ^2`. -/
theorem kochMap_isFinite_surjective :
    IsFinite (kochMap (K := K)) ∧ Function.Surjective (kochMap (K := K)) :=
  projFormsProjective_isFinite_surjective _ _ _ _ _

/-- The linear forms `(u - v, u - w, u)` through which the Belk–Koch forms
factor after squaring. -/
noncomputable def kochLinear : Fin 2 ⊕ Unit → Plane :=
  Sum.elim ![X ix - X iy, X ix - X iz] fun _ => X ix

/-- Its inverse linear substitution. -/
noncomputable def kochLinearInv : Fin 2 ⊕ Unit → Plane :=
  Sum.elim ![X iz, X iz - X ix] fun _ => X iz - X iy

theorem kochForms_aeval_injective :
    Function.Injective (aeval (R := K) (kochForms (K := K))) := by
  have hfac : aeval (R := K) (kochForms (K := K)) =
      (aeval (R := K) (squaringForms (K := K) (n := 2))).comp (aeval kochLinear) := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | u
    · fin_cases i <;> simp [kochForms, kochLinear, squaringForms]
    · simp [kochForms, kochLinear, squaringForms]
  have hinv : (aeval (R := K) (kochLinearInv (K := K))).comp (aeval kochLinear) =
      AlgHom.id K Plane := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | u
    · fin_cases i <;> simp [kochLinear, kochLinearInv]
    · simp [kochLinear, kochLinearInv]
  have hlin : Function.Injective (aeval (R := K) (kochLinear (K := K))) :=
    Function.LeftInverse.injective (g := aeval (R := K) (kochLinearInv (K := K))) fun P => by
      simpa using congrArg (fun φ => φ P) hinv
  rw [hfac]
  exact squaringForms_aeval_injective.comp hlin

theorem kochForms_aeval_isIntegral :
    (aeval (R := K) (kochForms (K := K))).toRingHom.IsIntegral :=
  aeval_isIntegral_of_X _ fun i => by
    obtain ⟨P, hP⟩ := kochForms_sq (K := K) i
    exact isIntegralElem_of_sq_eq _ hP

/-- Image of one line under the Belk–Koch map, from one divisibility. -/
theorem kochMap_sixLines [CharZero K] (i j : Fin 6)
    (h : aeval (R := K) kochForms (sixForms j) ∈ Ideal.span {sixForms (K := K) i}) :
    kochMap (sixLines (K := K) i) = sixLines j :=
  projFormsProjectiveSchemeMap_projLinePoint _ _ _ _ _
    kochForms_aeval_injective kochForms_aeval_isIntegral _ _ _ _ _ _ _ _ _ _ h

/-- `ex:koch`, line itinerary `H_0 → H_2 → M_1 → M_0 → H_0`, `H_1 → M_2 → H_1`,
as equalities of actual image divisors. -/
theorem kochMap_itinerary [CharZero K] :
    kochMap (sixLines (K := K) 0) = sixLines 2 ∧
      kochMap (sixLines (K := K) 2) = sixLines 4 ∧
      kochMap (sixLines (K := K) 4) = sixLines 3 ∧
      kochMap (sixLines (K := K) 3) = sixLines 0 ∧
      kochMap (sixLines (K := K) 1) = sixLines 5 ∧
      kochMap (sixLines (K := K) 5) = sixLines 1 := by
  refine ⟨kochMap_sixLines 0 2 ?_, kochMap_sixLines 2 4 ?_, kochMap_sixLines 4 3 ?_,
    kochMap_sixLines 3 0 ?_, kochMap_sixLines 1 5 ?_, kochMap_sixLines 5 1 ?_⟩ <;>
    rw [Ideal.mem_span_singleton']
  · exact ⟨X ix, by simp [kochForms, sixForms]; ring⟩
  · exact ⟨-X iz, by simp [kochForms, sixForms]; ring⟩
  · exact ⟨-(X iy + X iz), by simp [kochForms, sixForms]; ring⟩
  · exact ⟨X ix + X iy, by simp [kochForms, sixForms]; ring⟩
  · exact ⟨-X iy, by simp [kochForms, sixForms]; ring⟩
  · exact ⟨X ix + X iz, by simp [kochForms, sixForms]; ring⟩

/-- Every one of the six lines is periodic for the Belk–Koch map. -/
theorem kochMap_sixLines_periodic [CharZero K] (i : Fin 6) :
    ∃ m, 0 < m ∧ (⇑(kochMap (K := K)))^[m] (sixLines i) = sixLines i := by
  obtain ⟨h02, h24, h43, h30, h15, h51⟩ := kochMap_itinerary (K := K)
  fin_cases i
  · exact ⟨4, by norm_num, by simp [h02, h24, h43, h30]⟩
  · exact ⟨2, by norm_num, by simp [h15, h51]⟩
  · exact ⟨4, by norm_num, by simp [h24, h43, h30, h02]⟩
  · exact ⟨4, by norm_num, by simp [h30, h02, h24, h43]⟩
  · exact ⟨4, by norm_num, by simp [h43, h30, h02, h24]⟩
  · exact ⟨2, by norm_num, by simp [h51, h15]⟩

/-! ## Dupont's map -/

/-- Dupont's linear forms `L = (x - y + z, x + y - z, -x + y + z)`. -/
noncomputable def dupontLinear : Fin 2 ⊕ Unit → Plane :=
  Sum.elim ![X ix - X iy + X iz, X ix + X iy - X iz] fun _ => -X ix + X iy + X iz

/-- The inverse linear substitution, using `2 ≠ 0`. -/
noncomputable def dupontLinearInv : Fin 2 ⊕ Unit → Plane :=
  Sum.elim ![C (1 / 2 : K) * (X ix + X iy), C (1 / 2 : K) * (X iy + X iz)]
    fun _ => C (1 / 2 : K) * (X ix + X iz)

/-- Dupont's forms `ψ ∘ L`. -/
noncomputable def dupontForms : Fin 2 ⊕ Unit → Plane := fun i => dupontLinear i ^ 2

/-- The forms are the renaming of `CharZeroPaperPlane.dupontPolynomial`. -/
theorem dupontForms_planeIdx (i : Fin 3) :
    dupontForms (K := K) (planeIdx i) =
      rename planeIdx (Pcf.Examples.CharZeroPaperPlane.dupontPolynomial (K := K) i) := by
  fin_cases i <;>
    simp [dupontForms, dupontLinear, planeIdx, Pcf.Examples.CharZeroPaperPlane.dupontPolynomial]

theorem dupontLinear_isHomogeneous (i : Fin 2 ⊕ Unit) :
    (dupontLinear (K := K) i).IsHomogeneous 1 := by
  have hx := isHomogeneous_X K ix
  have hy := isHomogeneous_X K iy
  have hz := isHomogeneous_X K iz
  rcases i with i | u
  · fin_cases i
    · exact (hx.sub hy).add hz
    · exact (hx.add hy).sub hz
  · exact (hx.neg.add hy).add hz

theorem dupontForms_isHomogeneous (i : Fin 2 ⊕ Unit) :
    (dupontForms (K := K) i).IsHomogeneous 2 := by
  simpa [dupontForms] using (dupontLinear_isHomogeneous (K := K) i).pow 2

theorem half_mul_two [CharZero K] : (C (1 / 2 : K) : Plane) * 2 = 1 := by
  rw [show (2 : Plane) = C 2 from (map_ofNat C 2).symm, ← C_mul]
  norm_num

/-- Each coordinate is half the sum of two of Dupont's linear forms. -/
theorem dupontLinear_coordinates [CharZero K] :
    (X ix : Plane) = C (1 / 2 : K) * (dupontLinear ix + dupontLinear iy) ∧
      (X iy : Plane) = C (1 / 2 : K) * (dupontLinear iy + dupontLinear iz) ∧
      (X iz : Plane) = C (1 / 2 : K) * (dupontLinear ix + dupontLinear iz) := by
  have h := half_mul_two (K := K)
  refine ⟨?_, ?_, ?_⟩ <;> simp only [dupontLinear, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  · linear_combination (-(X ix : Plane)) * h
  · linear_combination (-(X iy : Plane)) * h
  · linear_combination (-(X iz : Plane)) * h

/-- Each of Dupont's linear forms is integral over the substitution. -/
theorem dupontLinear_isIntegralElem (i : Fin 2 ⊕ Unit) :
    (aeval (R := K) (dupontForms (K := K))).toRingHom.IsIntegralElem (dupontLinear i) :=
  isIntegralElem_of_sq_eq _ (a := X i) (by simp [dupontForms])

theorem dupontLinear_mem_radical (i : Fin 2 ⊕ Unit) :
    dupontLinear (K := K) i ∈ (Ideal.span (Set.range (dupontForms (K := K)))).radical :=
  ⟨2, Ideal.subset_span ⟨i, rfl⟩⟩

/-- The Dupont forms have no common projective zero. -/
theorem dupontForms_cover [CharZero K] : FormsCoverProjective (dupontForms (K := K)) := by
  obtain ⟨hx, hy, hz⟩ := dupontLinear_coordinates (K := K)
  refine (projIrrelevant_le_coordinateIdeal (K := K) (n := 2)).trans ?_
  rw [Ideal.span_le, Set.range_subset_iff]
  intro i
  have hr := dupontLinear_mem_radical (K := K)
  rcases i with i | u
  · fin_cases i
    · change (X ix : Plane) ∈ _
      rw [hx]
      exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ (hr ix) (hr iy))
    · change (X iy : Plane) ∈ _
      rw [hy]
      exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ (hr iy) (hr iz))
  · change (X iz : Plane) ∈ _
    rw [hz]
    exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ (hr ix) (hr iz))

/-- The actual Dupont endomorphism `φ = ψ ∘ L` of `ℙ^2`. -/
noncomputable def dupontMap [CharZero K] :
    AlgebraicGeometry.Proj planeGrade ⟶ AlgebraicGeometry.Proj planeGrade :=
  projFormsProjectiveSchemeMap dupontForms 2 two_pos dupontForms_isHomogeneous dupontForms_cover

/-- `ex:dupont`: `ψ ∘ L` is a finite surjective endomorphism of `ℙ^2`. -/
theorem dupontMap_isFinite_surjective [CharZero K] :
    IsFinite (dupontMap (K := K)) ∧ Function.Surjective (dupontMap (K := K)) :=
  projFormsProjective_isFinite_surjective _ _ _ _ _

theorem dupontForms_aeval_injective [CharZero K] :
    Function.Injective (aeval (R := K) (dupontForms (K := K))) := by
  have h := half_mul_two (K := K)
  have hfac : aeval (R := K) (dupontForms (K := K)) =
      (aeval (R := K) (dupontLinear (K := K))).comp (aeval squaringForms) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [dupontForms, squaringForms]
  have hinv : (aeval (R := K) (dupontLinearInv (K := K))).comp (aeval dupontLinear) =
      AlgHom.id K Plane := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | u
    · fin_cases i
      · simp only [dupontLinear, dupontLinearInv, AlgHom.coe_comp, Function.comp_apply, aeval_X,
          Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_sub,
          AlgHom.coe_id, id_eq, Fin.zero_eta, Fin.isValue, Sum.elim_inr]
        linear_combination (X ix : Plane) * h
      · simp only [dupontLinear, dupontLinearInv, AlgHom.coe_comp, Function.comp_apply, aeval_X,
          Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_sub,
          AlgHom.coe_id, id_eq, Fin.mk_one, Fin.isValue, Sum.elim_inr]
        linear_combination (X iy : Plane) * h
    · simp only [dupontLinear, dupontLinearInv, AlgHom.coe_comp, Function.comp_apply, aeval_X,
        Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_neg,
        AlgHom.coe_id, id_eq, Fin.isValue, Sum.elim_inr]
      linear_combination (X iz : Plane) * h
  have hlin : Function.Injective (aeval (R := K) (dupontLinear (K := K))) :=
    Function.LeftInverse.injective (g := aeval (R := K) (dupontLinearInv (K := K))) fun P => by
      simpa using congrArg (fun φ => φ P) hinv
  rw [hfac]
  exact hlin.comp squaringForms_aeval_injective

theorem dupontForms_aeval_isIntegral [CharZero K] :
    (aeval (R := K) (dupontForms (K := K))).toRingHom.IsIntegral := by
  obtain ⟨hx, hy, hz⟩ := dupontLinear_coordinates (K := K)
  have hC (a : K) : (aeval (R := K) (dupontForms (K := K))).toRingHom.IsIntegralElem (C a) := by
    have : (C a : Plane) = (aeval (R := K) (dupontForms (K := K))).toRingHom (C a) := by simp
    rw [this]
    exact RingHom.isIntegralElem_map _
  have hL := dupontLinear_isIntegralElem (K := K)
  refine aeval_isIntegral_of_X _ fun i => ?_
  rcases i with i | u
  · fin_cases i
    · change RingHom.IsIntegralElem _ (X ix : Plane)
      rw [hx]
      exact (hC _).mul _ ((hL ix).add _ (hL iy))
    · change RingHom.IsIntegralElem _ (X iy : Plane)
      rw [hy]
      exact (hC _).mul _ ((hL iy).add _ (hL iz))
  · change RingHom.IsIntegralElem _ (X iz : Plane)
    rw [hz]
    exact (hC _).mul _ ((hL ix).add _ (hL iz))

/-- Image of one of the six lines under Dupont's map, from one divisibility. -/
theorem dupontMap_sixLines [CharZero K] (i j : Fin 6)
    (h : aeval (R := K) dupontForms (sixForms j) ∈ Ideal.span {sixForms (K := K) i}) :
    dupontMap (sixLines (K := K) i) = sixLines j :=
  projFormsProjectiveSchemeMap_projLinePoint _ _ _ _ _
    dupontForms_aeval_injective dupontForms_aeval_isIntegral _ _ _ _ _ _ _ _ _ _ h

/-- `ex:dupont`: `φ(H_0) = M_0`, `φ(H_1) = M_1`, `φ(H_2) = M_2`, and
`φ(M_0) = M_2`, `φ(M_2) = M_1`, `φ(M_1) = M_0`, as equalities of actual image
divisors. -/
theorem dupontMap_itinerary [CharZero K] :
    dupontMap (sixLines (K := K) 0) = sixLines 3 ∧
      dupontMap (sixLines (K := K) 1) = sixLines 4 ∧
      dupontMap (sixLines (K := K) 2) = sixLines 5 ∧
      dupontMap (sixLines (K := K) 3) = sixLines 5 ∧
      dupontMap (sixLines (K := K) 5) = sixLines 4 ∧
      dupontMap (sixLines (K := K) 4) = sixLines 3 := by
  refine ⟨dupontMap_sixLines 0 3 ?_, dupontMap_sixLines 1 4 ?_, dupontMap_sixLines 2 5 ?_,
    dupontMap_sixLines 3 5 ?_, dupontMap_sixLines 5 4 ?_, dupontMap_sixLines 4 3 ?_⟩ <;>
    rw [Ideal.mem_span_singleton']
  · exact ⟨4 * (X iz - X iy), by simp [dupontForms, dupontLinear, sixForms]; ring⟩
  · exact ⟨4 * (X ix - X iz), by simp [dupontForms, dupontLinear, sixForms]; ring⟩
  · exact ⟨4 * (X ix - X iy), by simp [dupontForms, dupontLinear, sixForms]; ring⟩
  · exact ⟨4 * X iz, by simp [dupontForms, dupontLinear, sixForms]; ring⟩
  · exact ⟨4 * X iy, by simp [dupontForms, dupontLinear, sixForms]; ring⟩
  · exact ⟨-(4 * X ix), by simp [dupontForms, dupontLinear, sixForms]; ring⟩

/-- A vector on `L⁻¹(H_i)` with nonzero `x`-coordinate. -/
def criticalVector : Fin 2 ⊕ Unit → Fin 2 ⊕ Unit → K :=
  Sum.elim ![vec 1 1 0, vec 1 0 1] fun _ => vec 1 1 0

theorem dupontLinear_ne_zero [CharZero K] (i : Fin 2 ⊕ Unit) : dupontLinear (K := K) i ≠ 0 := by
  intro h
  have := congrArg (eval (vec (1 : K) 0 0)) h
  rcases i with i | u
  · fin_cases i <;> simp [dupontLinear] at this
  · simp [dupontLinear] at this

theorem X_not_mem_span_dupontLinear [CharZero K] (i : Fin 2 ⊕ Unit) :
    (X ix : Plane) ∉ Ideal.span {dupontLinear (K := K) i} := by
  apply not_mem_span_of_eval (criticalVector i)
  · rcases i with i | u
    · fin_cases i <;> simp [criticalVector, dupontLinear]
    · simp [criticalVector, dupontLinear]
  · rcases i with i | u
    · fin_cases i <;> simp [criticalVector]
    · simp [criticalVector]

/-- The line `L⁻¹(H_i) = V(L_i)`, as a projective point. -/
noncomputable def criticalLine [CharZero K] (i : Fin 2 ⊕ Unit) :
    AlgebraicGeometry.Proj planeGrade :=
  projLinePoint (dupontLinear i) (dupontLinear_isHomogeneous i) (dupontLinear_ne_zero i) ix
    (X_not_mem_span_dupontLinear i)

/-- Each line `L⁻¹(H_i)` is an integral effective divisor. -/
theorem criticalLine_coheight [CharZero K] (i : Fin 2 ⊕ Unit) :
    Order.coheight (criticalLine (K := K) i) = 1 :=
  projLinePoint_coheight _ _ _ _ _

/-- `ex:dupont`: `φ(L⁻¹(H_i)) = H_i`, as actual image divisors. The coordinate
hyperplanes are those of `ex:squaring-PN` with `N = 2`. -/
theorem dupontMap_criticalLine [CharZero K] (i : Fin 2 ⊕ Unit) :
    dupontMap (criticalLine (K := K) i) = hyperplane i :=
  projFormsProjectiveSchemeMap_projLinePoint _ _ _ _ _
    dupontForms_aeval_injective dupontForms_aeval_isIntegral _ _ _ _ _ _ _ _ _ _
    (Ideal.mem_span_singleton'.mpr ⟨dupontLinear i, by simp [dupontForms, sq]⟩)

/-- The coordinate hyperplanes of `ex:squaring-PN` with `N = 2` are the first
three of the six lines. -/
theorem hyperplane_eq_sixLines [CharZero K] :
    hyperplane (K := K) ix = sixLines 0 ∧ hyperplane (K := K) iy = sixLines 1 ∧
      hyperplane (K := K) iz = sixLines 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    exact (projLinePoint_eq_iff _ _ _ _ _ _ _ _ _ _).mpr (by simp [sixForms])

/-- The forward orbit of `M_0, M_1, M_2` stays among them. -/
theorem dupontMap_iterate_mem_M [CharZero K] (k : Fin 6) (hk : 3 ≤ k) (m : ℕ) :
    ∃ l : Fin 6, 3 ≤ l ∧ (⇑(dupontMap (K := K)))^[m] (sixLines k) = sixLines l := by
  obtain ⟨-, -, -, h35, h54, h43⟩ := dupontMap_itinerary (K := K)
  induction m with
  | zero => exact ⟨k, hk, rfl⟩
  | succ m ih =>
    obtain ⟨l, hl, hm⟩ := ih
    rw [Function.iterate_succ_apply', hm]
    fin_cases l <;> simp at hl
    · exact ⟨5, by decide, h35⟩
    · exact ⟨3, by decide, h43⟩
    · exact ⟨4, by decide, h54⟩

/-- `ex:dupont`: the coordinate lines are strictly preperiodic: no positive
iterate returns `H_i` to itself. -/
theorem dupontMap_H_strictly_preperiodic [CharZero K] (i : Fin 6) (hi : i < 3)
    (m : ℕ) (hm : 0 < m) : (⇑(dupontMap (K := K)))^[m] (sixLines i) ≠ sixLines i := by
  obtain ⟨h03, h14, h25, -, -, -⟩ := dupontMap_itinerary (K := K)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hm
  rw [zero_add, Function.iterate_succ_apply]
  have hstart : ∃ k : Fin 6, 3 ≤ k ∧ dupontMap (sixLines (K := K) i) = sixLines k := by
    fin_cases i <;> simp at hi
    · exact ⟨3, by decide, h03⟩
    · exact ⟨4, by decide, h14⟩
    · exact ⟨5, by decide, h25⟩
  obtain ⟨k, hk, hik⟩ := hstart
  rw [hik]
  obtain ⟨l, hl, hkl⟩ := dupontMap_iterate_mem_M (K := K) k hk m
  rw [hkl]
  intro h
  have := sixLines_injective (K := K) h
  omega

/-- `ex:dupont`: `M_0, M_1, M_2` form a three-cycle: each has exact period three. -/
theorem dupontMap_M_threeCycle [CharZero K] :
    ((⇑(dupontMap (K := K)))^[3] (sixLines 3) = sixLines 3 ∧
      (⇑(dupontMap (K := K)))^[3] (sixLines 4) = sixLines 4 ∧
      (⇑(dupontMap (K := K)))^[3] (sixLines 5) = sixLines 5) ∧
    (dupontMap (sixLines (K := K) 3) ≠ sixLines 3 ∧
      dupontMap (sixLines (K := K) 4) ≠ sixLines 4 ∧
      dupontMap (sixLines (K := K) 5) ≠ sixLines 5) ∧
    ((⇑(dupontMap (K := K)))^[2] (sixLines 3) ≠ sixLines 3 ∧
      (⇑(dupontMap (K := K)))^[2] (sixLines 4) ≠ sixLines 4 ∧
      (⇑(dupontMap (K := K)))^[2] (sixLines 5) ≠ sixLines 5) := by
  obtain ⟨-, -, -, h35, h54, h43⟩ := dupontMap_itinerary (K := K)
  have hinj := sixLines_injective (K := K)
  have hne (a b : Fin 6) (hab : a ≠ b) : sixLines (K := K) a ≠ sixLines b :=
    fun h => hab (hinj h)
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
    h35, h54, h43]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨hne _ _ (by decide), hne _ _ (by decide), hne _ _ (by decide)⟩,
    ⟨hne _ _ (by decide), hne _ _ (by decide), hne _ _ (by decide)⟩⟩ <;> trivial

#print axioms sixLines_coheight
#print axioms sixLines_closure
#print axioms sixLines_injective
#print axioms kochForms_planeIdx
#print axioms kochMap
#print axioms kochMap_isFinite_surjective
#print axioms kochForms_aeval_injective
#print axioms kochForms_aeval_isIntegral
#print axioms kochMap_itinerary
#print axioms kochMap_sixLines_periodic
#print axioms dupontForms_planeIdx
#print axioms dupontLinear_coordinates
#print axioms dupontForms_cover
#print axioms dupontMap
#print axioms dupontMap_isFinite_surjective
#print axioms dupontForms_aeval_injective
#print axioms dupontForms_aeval_isIntegral
#print axioms dupontMap_itinerary
#print axioms criticalLine_coheight
#print axioms dupontMap_criticalLine
#print axioms hyperplane_eq_sixLines
#print axioms dupontMap_H_strictly_preperiodic
#print axioms dupontMap_M_threeCycle
end Pcf.Examples.CharZeroPaperPlaneProjective
