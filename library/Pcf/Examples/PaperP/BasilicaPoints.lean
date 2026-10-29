/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Rational-point dynamics of the basilica map

This file formalizes the projective map and the explicit point orbit in
`paper-p.tex`, Example `ex:basilica`. The points are actual `K`-rational
points of the projective line. The scheme morphism, critical locus, and
postcritical locus require additional geometric infrastructure and are
not claimed here.
-/

@[expose] public section

namespace Pcf.Examples.PaperP
open Projectivization
open scoped LinearAlgebra.Projectivization
universe u
variable (K : Type u) [Field K]

/-- The degree-two homogeneous coordinate map
`[x₀:x₁] ↦ [x₀²-x₁²:x₁²]` of Example `ex:basilica`. -/
def basilicaCoordinates (v : K × K) : K × K :=
  (v.1 ^ 2 - v.2 ^ 2, v.2 ^ 2)

theorem basilicaCoordinates_ne_zero {v : K × K} (hv : v ≠ 0) :
    basilicaCoordinates K v ≠ 0 := by
  intro h
  have h₂ : v.2 ^ 2 = 0 := congrArg Prod.snd h
  have hv₂ : v.2 = 0 := eq_zero_of_pow_eq_zero h₂
  have h₁ : v.1 ^ 2 - v.2 ^ 2 = 0 := congrArg Prod.fst h
  rw [hv₂, zero_pow (by decide), sub_zero] at h₁
  have hv₁ : v.1 = 0 := eq_zero_of_pow_eq_zero h₁
  exact hv (by cases v; simp_all)

theorem basilicaCoordinates_smul (t : K) (v : K × K) :
    basilicaCoordinates K (t • v) = t ^ 2 • basilicaCoordinates K v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [basilicaCoordinates, smul_eq_mul] <;> ring

/-- The basilica map on actual `K`-rational projective-line points.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
noncomputable def basilicaProjective : ℙ K (K × K) → ℙ K (K × K) :=
  Projectivization.lift
    (fun v => Projectivization.mk K (basilicaCoordinates K v.1)
      (basilicaCoordinates_ne_zero K v.2))
    (by
      intro a b t hab
      apply (Projectivization.mk_eq_mk_iff' K
        (basilicaCoordinates K a.1) (basilicaCoordinates K b.1)
        (basilicaCoordinates_ne_zero K a.2)
        (basilicaCoordinates_ne_zero K b.2)).2
      exact ⟨t ^ 2, by rw [← basilicaCoordinates_smul K, ← hab]⟩)

@[simp] theorem basilicaProjective_mk (v : K × K) (hv : v ≠ 0) :
    basilicaProjective K (Projectivization.mk K v hv) =
      Projectivization.mk K (basilicaCoordinates K v)
        (basilicaCoordinates_ne_zero K hv) :=
  Projectivization.lift_mk _ _ v hv

def basilicaZero : ℙ K (K × K) :=
  Projectivization.mk K (0, 1) (by simp)

def basilicaMinusOne : ℙ K (K × K) :=
  Projectivization.mk K (-1, 1) (by simp)

def basilicaInfinity : ℙ K (K × K) :=
  Projectivization.mk K (1, 0) (by simp)

/-- The finite point `0` maps to `-1`. -/
theorem basilica_zero_to_minusOne :
    basilicaProjective K (basilicaZero K) = basilicaMinusOne K := by
  simp [basilicaZero, basilicaMinusOne, basilicaCoordinates]

/-- The finite point `-1` maps back to `0`. -/
theorem basilica_minusOne_to_zero :
    basilicaProjective K (basilicaMinusOne K) = basilicaZero K := by
  simp [basilicaZero, basilicaMinusOne, basilicaCoordinates]

/-- The point at infinity is fixed.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem basilica_infinity_fixed :
    basilicaProjective K (basilicaInfinity K) = basilicaInfinity K := by
  simp [basilicaInfinity, basilicaCoordinates]

theorem basilica_zero_ne_minusOne : basilicaZero K ≠ basilicaMinusOne K := by
  intro h
  have h' := (Projectivization.mk_eq_mk_iff' K (0, 1) (-1, 1)
    (by simp) (by simp)).mp h
  obtain ⟨t, ht⟩ := h'
  have h₁ : t = 1 := by simpa using congrArg Prod.snd ht
  have h₀ : t * (-1) = (0 : K) := by simpa [smul_eq_mul] using congrArg Prod.fst ht
  simp [h₁] at h₀

/-- The finite critical-point candidate `0` has exact period two under
the projective rational-point map. Identification as critical requires
the scheme-level Jacobian criterion.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem basilica_zero_period_two :
    (basilicaProjective K)^[2] (basilicaZero K) = basilicaZero K ∧
      basilicaProjective K (basilicaZero K) ≠ basilicaZero K := by
  constructor
  · simp [Function.iterate_succ_apply, basilica_zero_to_minusOne,
      basilica_minusOne_to_zero]
  · rw [basilica_zero_to_minusOne]
    exact (basilica_zero_ne_minusOne K).symm

section Jacobian

open MvPolynomial

/-- The two homogeneous coordinate forms of the basilica map. -/
noncomputable def basilicaForm (i : Fin 2) : MvPolynomial (Fin 2) K :=
  if i = 0 then X 0 ^ 2 - X 1 ^ 2 else X 1 ^ 2

/-- The homogeneous Jacobian matrix, formed from the actual partial
derivatives of the two defining forms. -/
noncomputable def basilicaJacobian : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) K) :=
  fun i j => pderiv j (basilicaForm K i)

/-- The determinant calculation in Example `ex:basilica` of
`paper-p.tex`: `J = 4 x₀ x₁`. This is the polynomial calculation;
identifying its zero locus with the critical scheme locus is the
separate projective étaleness assertion in Lemma `lem:jacobian`.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem basilicaJacobian_det :
    (basilicaJacobian K).det =
      (4 : MvPolynomial (Fin 2) K) * X 0 * X 1 := by
  simp [basilicaJacobian, basilicaForm, Matrix.det_fin_two,
    MvPolynomial.pderiv_X]
  ring

/-- In characteristic zero the homogeneous Jacobian vanishes at a
coordinate vector exactly when one of its two coordinates vanishes. -/
theorem basilicaJacobian_eval_zero_iff [CharZero K] (x : Fin 2 → K) :
    eval x (basilicaJacobian K).det = 0 ↔ x 0 = 0 ∨ x 1 = 0 := by
  rw [basilicaJacobian_det]
  simp [mul_eq_zero]

/-- The zero locus of the homogeneous Jacobian on actual `K`-rational
projective-line points, expressed through a nonzero homogeneous
representative. -/
def basilicaJacobianZero (p : ℙ K (K × K)) : Prop :=
  ∃ (v : K × K) (hv : v ≠ 0),
    p = Projectivization.mk K v hv ∧
      eval (fun i : Fin 2 => if i = 0 then v.1 else v.2)
        (basilicaJacobian K).det = 0

/-- In characteristic zero, the rational-point zero locus of the
homogeneous Jacobian is exactly `{0, ∞}`. This identifies the points
of `V(J)`; the scheme-theoretic critical-locus identification still
requires `lem:jacobian`. -/
theorem basilicaJacobianZero_iff [CharZero K] (p : ℙ K (K × K)) :
    basilicaJacobianZero K p ↔
      p = basilicaZero K ∨ p = basilicaInfinity K := by
  constructor
  · rintro ⟨⟨a, b⟩, hv, rfl, hJ⟩
    have hab : a = 0 ∨ b = 0 := by
      simpa using (basilicaJacobian_eval_zero_iff K
        (fun i : Fin 2 => if i = 0 then a else b)).mp hJ
    rcases hab with ha | hb
    · left
      have hb' : b ≠ 0 := by
        intro hb0
        apply hv
        simp [ha, hb0]
      apply (Projectivization.mk_eq_mk_iff' K (a, b) (0, 1) hv (by simp)).2
      exact ⟨b, by simp [ha, smul_eq_mul]⟩
    · right
      have ha' : a ≠ 0 := by
        intro ha0
        apply hv
        simp [ha0, hb]
      apply (Projectivization.mk_eq_mk_iff' K (a, b) (1, 0) hv (by simp)).2
      exact ⟨a, by simp [hb, smul_eq_mul]⟩
  · rintro (rfl | rfl)
    · refine ⟨(0, 1), by simp, rfl, ?_⟩
      simp [basilicaJacobian_det]
    · refine ⟨(1, 0), by simp, rfl, ?_⟩
      simp [basilicaJacobian_det]

/-- Positive iterates of points in the Jacobian zero locus. This is
the rational-point postcritical set once the Jacobian criterion in
`lem:jacobian` has been supplied. -/
def basilicaJacobianPostorbit (q : ℙ K (K × K)) : Prop :=
  ∃ p, basilicaJacobianZero K p ∧
    ∃ k : ℕ, 0 < k ∧ q = (basilicaProjective K)^[k] p

private theorem basilica_three_points_forward (p : ℙ K (K × K))
    (hp : p = basilicaZero K ∨ p = basilicaMinusOne K ∨
      p = basilicaInfinity K) :
    basilicaProjective K p = basilicaZero K ∨
      basilicaProjective K p = basilicaMinusOne K ∨
      basilicaProjective K p = basilicaInfinity K := by
  rcases hp with rfl | rfl | rfl
  · exact Or.inr (Or.inl (basilica_zero_to_minusOne K))
  · exact Or.inl (basilica_minusOne_to_zero K)
  · exact Or.inr (Or.inr (basilica_infinity_fixed K))

/-- The positive orbit of the Jacobian zero locus on `K`-rational
projective points is precisely `{0, -1, ∞}`. -/
theorem basilicaJacobianPostorbit_iff [CharZero K] (q : ℙ K (K × K)) :
    basilicaJacobianPostorbit K q ↔
      q = basilicaZero K ∨ q = basilicaMinusOne K ∨
        q = basilicaInfinity K := by
  constructor
  · rintro ⟨p, hp, k, _, rfl⟩
    have hp' : p = basilicaZero K ∨ p = basilicaMinusOne K ∨
        p = basilicaInfinity K := by
      rcases (basilicaJacobianZero_iff K p).mp hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have hIter : ∀ m : ℕ,
        (basilicaProjective K)^[m] p = basilicaZero K ∨
        (basilicaProjective K)^[m] p = basilicaMinusOne K ∨
        (basilicaProjective K)^[m] p = basilicaInfinity K := by
      intro m
      induction m with
      | zero => simpa using hp'
      | succ m ih =>
        simpa only [Function.iterate_succ_apply'] using
          basilica_three_points_forward K ((basilicaProjective K)^[m] p) ih
    exact hIter k
  · rintro (rfl | rfl | rfl)
    · refine ⟨basilicaZero K, (basilicaJacobianZero_iff K _).2 (Or.inl rfl),
        2, by decide, ?_⟩
      simp [Function.iterate_succ_apply, basilica_zero_to_minusOne,
        basilica_minusOne_to_zero]
    · refine ⟨basilicaZero K, (basilicaJacobianZero_iff K _).2 (Or.inl rfl),
        1, by decide, ?_⟩
      simp [basilica_zero_to_minusOne]
    · refine ⟨basilicaInfinity K,
        (basilicaJacobianZero_iff K _).2 (Or.inr rfl),
        1, by decide, ?_⟩
      simp [basilica_infinity_fixed]

end Jacobian

#print axioms basilicaProjective
#print axioms basilica_zero_to_minusOne
#print axioms basilica_minusOne_to_zero
#print axioms basilica_infinity_fixed
#print axioms basilica_zero_period_two
#print axioms basilicaJacobian_det
#print axioms basilicaJacobian_eval_zero_iff
#print axioms basilicaJacobianZero_iff
#print axioms basilicaJacobianPostorbit_iff

end Pcf.Examples.PaperP
