/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Examples: the cuspidal cubic and the quadric cone

This file formalizes the computational content of Examples `ex:cusp` and `ex:branch-singular` of the
manuscript `latex/paper.tex`, "PCF All the Way Down".

## Example `ex:cusp` (`ex:cusp`)

For `f : 𝔸² → 𝔸²`, `f(u,v) = (u², u³ + v)`, restricted to `A = V(v)`, the image is
the cuspidal cubic `B = V(y² - x³)`, the Jacobian determinant of `f` is `2u`, and
`B ∩ Z = B ∩ V(x) = {(0,0)}`.  The point of the example is that the restriction
`g(u) = (u², u³)` is the *normalization* of the cusp, so that `Branch(g) = ∅` is a
proper subset of `B ∩ Z`.

## Example `ex:branch-singular` (`ex:branch-singular`)

For `f : 𝔸² → Y = Spec k[x,y,z]/(xz - y²)`, `f(u,v) = (u², uv, v²)`, the restriction
to `A = V(v)` is `g(u) = u²`, which ramifies at the origin even though `Z = ∅`.
-/

@[expose] public section

namespace Pcf.Examples.Cusp

/-! ### Example `ex:cusp`: the parametrisation of the cuspidal cubic -/

section Parametrisation

variable (k : Type*) [CommRing k]

/-- The ideal `(y² - x³)` of the cuspidal cubic `B` of Example `ex:cusp` of `paper.tex`,
inside `k[x, y] = MvPolynomial (Fin 2) k` (variable `0` is `x`, variable `1` is `y`). -/
noncomputable def cuspIdeal : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3}

/-- The parametrisation `g(u) = (u², u³)` of Example `ex:cusp` of `paper.tex`, as a `k`-algebra
map `k[x,y]/(y² - x³) → k[t]` sending `x ↦ t²` and `y ↦ t³`.  Its existence is exactly
the statement that the restriction of `f(u,v) = (u², u³ + v)` to `A = V(v)` lands on the
cuspidal cubic `B = V(y² - x³)`. -/
noncomputable def cuspParam :
    (MvPolynomial (Fin 2) k ⧸ cuspIdeal k) →ₐ[k] Polynomial k :=
  Ideal.Quotient.liftₐ _
    (MvPolynomial.aeval ![Polynomial.X ^ 2, Polynomial.X ^ 3]) <| by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      simp [mul_comm]
      ring

/-- Example `ex:cusp` of `paper.tex`: the parametrisation sends `x` to `t²`. -/
@[simp] theorem cuspParam_x :
    cuspParam k (Ideal.Quotient.mk _ (MvPolynomial.X 0)) = Polynomial.X ^ 2 := by
  change MvPolynomial.aeval ![Polynomial.X ^ 2, Polynomial.X ^ 3] _ = _
  simp

/-- Example `ex:cusp` of `paper.tex`: the parametrisation sends `y` to `t³`. -/
@[simp] theorem cuspParam_y :
    cuspParam k (Ideal.Quotient.mk _ (MvPolynomial.X 1)) = Polynomial.X ^ 3 := by
  change MvPolynomial.aeval ![Polynomial.X ^ 2, Polynomial.X ^ 3] _ = _
  simp

/-- Example `ex:cusp` of `paper.tex`: pointwise form of the previous statement, `g(u) = (u², u³)`
satisfies `y² = x³`. -/
theorem cusp_pointwise (u : k) : (u ^ 3) ^ 2 = (u ^ 2) ^ 3 := by ring

end Parametrisation

/-! ### Example `ex:cusp`: the Jacobian determinant -/

section Jacobian

variable (k : Type*) [CommRing k]

/-- The map `f(u,v) = (u², u³ + v)` of Example `ex:cusp` of `paper.tex`, as a pair of elements
of `k[u,v] = MvPolynomial (Fin 2) k` (variable `0` is `u`, variable `1` is `v`). -/
noncomputable def cuspSource : Fin 2 → MvPolynomial (Fin 2) k :=
  ![MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 ^ 3 + MvPolynomial.X 1]

/-- Example `ex:cusp` of `paper.tex`: the Jacobian determinant of `f(u,v) = (u², u³ + v)` is `2u`.
Over a field of characteristic `≠ 2` this vanishes exactly on `V(u)`, giving
`Crit(f) = V(u)`. -/
theorem jacobian_cuspSource :
    MvPolynomial.pderiv 0 (cuspSource k 0) * MvPolynomial.pderiv 1 (cuspSource k 1)
        - MvPolynomial.pderiv 1 (cuspSource k 0) * MvPolynomial.pderiv 0 (cuspSource k 1)
      = 2 * MvPolynomial.X 0 := by
  simp [cuspSource, MvPolynomial.pderiv_X]

end Jacobian

/-! ### Example `ex:cusp`: `B ∩ Z = {(0,0)}` -/

section Intersection

variable (k : Type*) [Field k]

/-- Example `ex:cusp` of `paper.tex`: `B ∩ Z = V(y² - x³) ∩ V(x) = {(0,0)}`.  In particular
`B ∩ Z` is nonempty; since the normalization statements below identify `g` with the
normalization map of `B`, whose branch locus is empty, this is the strict inclusion
`Branch(g) = ∅ ⊊ B ∩ Z` of the manuscript. -/
theorem cusp_inter_branch : {p : k × k | p.2 ^ 2 = p.1 ^ 3 ∧ p.1 = 0} = {(0, 0)} := by
  ext ⟨x, y⟩
  change (y ^ 2 = x ^ 3 ∧ x = 0) ↔ _
  simp only [Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨rfl, ?_⟩
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by simpa using h)
  · rintro ⟨rfl, rfl⟩
    simp

end Intersection

/-! ### Example `ex:cusp`: `k[t]` is the normalization of the cuspidal cubic -/

section Normalization

open Polynomial

variable (k : Type*) [Field k]

/-- The coordinate ring `k[t², t³]` of the cuspidal cubic `B = V(y² - x³)` of
Example `ex:cusp` of `paper.tex`, realised as the subalgebra of `k[t]` generated by `t²` and
`t³`; the inclusion `k[t², t³] ↪ k[t]` is the parametrisation `g(u) = (u², u³)`. -/
noncomputable def cuspAlg : Subalgebra k (Polynomial k) :=
  Algebra.adjoin k {(X : Polynomial k) ^ 2, (X : Polynomial k) ^ 3}

/-- `t² ∈ k[t², t³]` (Example `ex:cusp` of `paper.tex`). -/
theorem X_sq_mem : (X : Polynomial k) ^ 2 ∈ cuspAlg k := Algebra.subset_adjoin (by simp)

/-- `t³ ∈ k[t², t³]` (Example `ex:cusp` of `paper.tex`). -/
theorem X_cube_mem : (X : Polynomial k) ^ 3 ∈ cuspAlg k := Algebra.subset_adjoin (by simp)

/-- `tⁿ ∈ k[t², t³]` for every `n ≥ 2` (Example `ex:cusp` of `paper.tex`). -/
theorem X_pow_add_two_mem (n : ℕ) : (X : Polynomial k) ^ (n + 2) ∈ cuspAlg k := by
  have key : ∀ n : ℕ, (X : Polynomial k) ^ (n + 2) ∈ cuspAlg k ∧
      (X : Polynomial k) ^ (n + 3) ∈ cuspAlg k := by
    intro n
    induction n with
    | zero => exact ⟨X_sq_mem k, X_cube_mem k⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have h : (X : Polynomial k) ^ (m + 1 + 3) = X ^ 2 * X ^ (m + 2) := by ring
      rw [h]
      exact mul_mem (X_sq_mem k) ih.1
  exact (key n).1

/-- Every element of `k[t², t³]` has vanishing coefficient in degree `1`
(Example `ex:cusp` of `paper.tex`). -/
theorem coeff_one_eq_zero_of_mem {p : Polynomial k} (hp : p ∈ cuspAlg k) : p.coeff 1 = 0 := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx => rcases hx with rfl | rfl <;> simp
  | algebraMap r => simp [Polynomial.algebraMap_eq]
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | mul x y hx hy ihx ihy =>
      simp [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, ihx, ihy]

/-- Conversely, any polynomial with vanishing degree-`1` coefficient lies in `k[t², t³]`
(Example `ex:cusp` of `paper.tex`). -/
theorem mem_cuspAlg_of_coeff_one {p : Polynomial k} (hp : p.coeff 1 = 0) : p ∈ cuspAlg k := by
  have h : ∑ i ∈ p.support, C (p.coeff i) * X ^ i ∈ cuspAlg k := by
    refine Subalgebra.sum_mem _ fun i _ => ?_
    have hC : (C (p.coeff i) : Polynomial k) ∈ cuspAlg k := by
      rw [← Polynomial.algebraMap_eq]
      exact Subalgebra.algebraMap_mem _ _
    match i with
    | 0 => simpa using hC
    | 1 => simp [hp]
    | (n + 2) => exact mul_mem hC (X_pow_add_two_mem k n)
  rwa [← p.as_sum_support_C_mul_X_pow] at h

/-- Example `ex:cusp` of `paper.tex`: `k[t², t³]` is exactly the set of polynomials whose
degree-`1` coefficient vanishes. -/
theorem mem_cuspAlg_iff {p : Polynomial k} : p ∈ cuspAlg k ↔ p.coeff 1 = 0 :=
  ⟨coeff_one_eq_zero_of_mem k, mem_cuspAlg_of_coeff_one k⟩

/-- Example `ex:cusp` of `paper.tex`: `t ∉ k[t², t³]`, i.e. the cusp is not smooth — its
coordinate ring is a proper subring of its normalization. -/
theorem X_notMem_cuspAlg : (X : Polynomial k) ∉ cuspAlg k := by
  intro h
  simpa using coeff_one_eq_zero_of_mem k h

/-- Example `ex:cusp` of `paper.tex`: `t` is integral over `k[t², t³]`; it is a root of the monic
polynomial `T² - t²`.  This is the first step in showing that `k[t]` is the normalization
of the cusp. -/
theorem isIntegral_X : IsIntegral (cuspAlg k) (X : Polynomial k) := by
  refine ⟨X ^ 2 - C ⟨(X : Polynomial k) ^ 2, X_sq_mem k⟩, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  simp

/-- Example `ex:cusp` of `paper.tex`: `k[t]` is generated as a `k[t², t³]`-algebra by `t`. -/
theorem adjoin_X_eq_top : Algebra.adjoin (cuspAlg k) {(X : Polynomial k)} = ⊤ := by
  have hsub : ∀ q : Polynomial k, q ∈ cuspAlg k →
      q ∈ Algebra.adjoin (cuspAlg k) {(X : Polynomial k)} := fun q hq =>
    Subalgebra.algebraMap_mem _ (⟨q, hq⟩ : cuspAlg k)
  have hX : (X : Polynomial k) ∈ Algebra.adjoin (cuspAlg k) {(X : Polynomial k)} :=
    Algebra.subset_adjoin rfl
  refine eq_top_iff.mpr fun p _ => ?_
  have hq : p - C (p.coeff 1) * X ∈ cuspAlg k := by
    refine mem_cuspAlg_of_coeff_one k ?_
    simp
  have hC : (C (p.coeff 1) : Polynomial k) ∈ cuspAlg k := by
    refine mem_cuspAlg_of_coeff_one k ?_
    simp
  have hp : p = p - C (p.coeff 1) * X + C (p.coeff 1) * X := by ring
  rw [hp]
  exact add_mem (hsub _ hq) (mul_mem (hsub _ hC) hX)

/-- Example `ex:cusp` of `paper.tex`: `k[t]` is a finite module over `k[t², t³]`. -/
instance moduleFinite_cuspAlg : Module.Finite (cuspAlg k) (Polynomial k) := by
  have h := (isIntegral_X k).fg_adjoin_singleton
  rw [adjoin_X_eq_top] at h
  rw [Module.finite_def]
  simpa using h

/-- Example `ex:cusp` of `paper.tex`: `k[t]` is integral over the coordinate ring `k[t², t³]` of
the cusp. -/
instance isIntegral_cuspAlg : Algebra.IsIntegral (cuspAlg k) (Polynomial k) :=
  Algebra.IsIntegral.of_finite _ _

/-- Example `ex:cusp` of `paper.tex`: `k[t]` is the integral closure of the coordinate ring
`k[t², t³]` of the cusp inside the field `k(t)`. -/
theorem isIntegralClosure_cuspAlg :
    IsIntegralClosure (Polynomial k) (cuspAlg k) (FractionRing (Polynomial k)) where
  algebraMap_injective := IsFractionRing.injective _ _
  isIntegral_iff := by
    intro x
    refine ⟨fun hx => IsIntegrallyClosed.isIntegral_iff.mp hx.tower_top, ?_⟩
    rintro ⟨y, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := cuspAlg k) y).map
      (IsScalarTower.toAlgHom (cuspAlg k) (Polynomial k) (FractionRing (Polynomial k)))

/-- The inclusion `k[t², t³] ↪ k(t)` is injective. -/
theorem algebraMap_cuspAlg_injective :
    Function.Injective (algebraMap (cuspAlg k) (FractionRing (Polynomial k))) := by
  intro a b hab
  refine Subtype.ext (IsFractionRing.injective (Polynomial k) (FractionRing (Polynomial k)) ?_)
  simpa [IsScalarTower.algebraMap_apply (cuspAlg k) (Polynomial k)
    (FractionRing (Polynomial k))] using hab

/-- The inclusion `k[t², t³] ↪ k[t]` is the coercion of the subalgebra. -/
theorem algebraMap_cuspAlg_apply (a : cuspAlg k) :
    algebraMap (cuspAlg k) (Polynomial k) a = (a : Polynomial k) := rfl

/-- Example `ex:cusp` of `paper.tex`: the cusp and its normalization have the same function
field, `Frac(k[t², t³]) = k(t)`; concretely `t = t³ / t²`. -/
instance isFractionRing_cuspAlg :
    IsFractionRing (cuspAlg k) (FractionRing (Polynomial k)) := by
  have hinj := algebraMap_cuspAlg_injective k
  refine (isLocalization_iff (nonZeroDivisors (cuspAlg k))
    (FractionRing (Polynomial k))).mpr ?_
  refine ⟨fun y => isUnit_iff_ne_zero.mpr fun h => nonZeroDivisors.coe_ne_zero y ?_,
    fun z => ?_, fun {x y} h => ⟨1, by rw [hinj h]⟩⟩
  · exact hinj (h.trans (map_zero _).symm)
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial k) z
    have hmem : ∀ r : Polynomial k, r * X ^ 2 ∈ cuspAlg k := fun r =>
      mem_cuspAlg_of_coeff_one k (by simp [Polynomial.coeff_mul_X_pow'])
    have hq0 : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
    have hqX : (⟨q * X ^ 2, hmem q⟩ : cuspAlg k) ∈ nonZeroDivisors (cuspAlg k) := by
      refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
      simp only [ne_eq, Subtype.ext_iff]
      exact mul_ne_zero hq0 (pow_ne_zero _ Polynomial.X_ne_zero)
    refine ⟨(⟨p * X ^ 2, hmem p⟩, ⟨_, hqX⟩), ?_⟩
    have hq' : algebraMap (Polynomial k) (FractionRing (Polynomial k)) q ≠ 0 := fun hc =>
      hq0 (IsFractionRing.injective (Polynomial k) (FractionRing (Polynomial k))
        (by simpa using hc))
    simp only [IsScalarTower.algebraMap_apply (cuspAlg k) (Polynomial k)
      (FractionRing (Polynomial k)), algebraMap_cuspAlg_apply]
    field_simp
    simp only [map_mul]
    ring

/-- Example `ex:cusp` of `paper.tex`: the integral closure of the coordinate ring `k[t², t³]` of
the cusp inside `k[t]` is all of `k[t]`.  Combined with `isFractionRing_cuspAlg` and
`isIntegralClosure_cuspAlg` this says that the parametrisation `g(u) = (u², u³)` *is* the
normalization map of the cusp `B`. -/
theorem integralClosure_cuspAlg_eq_top :
    integralClosure (cuspAlg k) (Polynomial k) = ⊤ :=
  eq_top_iff.mpr fun x _ => Algebra.IsIntegral.isIntegral x

/-- Example `ex:cusp` of `paper.tex`: `A = 𝔸¹` is already normal, i.e. `Ã = A`.  Together with
`integralClosure_cuspAlg_eq_top` (which identifies `B̃` with `A`) this is the assertion of
the manuscript that the induced map `g̃ : Ã → B̃` on normalizations is the identity of
`𝔸¹`, whence `Branch(g) = ∅`. -/
theorem isIntegrallyClosed_polynomial : IsIntegrallyClosed (Polynomial k) := inferInstance

end Normalization

/-! ### Example `ex:branch-singular`: the quadric cone -/

section QuadricCone

variable (k : Type*) [CommRing k]

/-- The ideal `(xz - y²)` of the quadric cone `Y` of Example `ex:branch-singular` of `paper.tex`,
inside
`k[x, y, z] = MvPolynomial (Fin 3) k`. -/
noncomputable def coneIdeal : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2}

/-- The map `f(u,v) = (u², uv, v²)` of Example `ex:branch-singular` of `paper.tex`, as a triple of
elements
of `k[u,v] = MvPolynomial (Fin 2) k`. -/
noncomputable def coneMap : Fin 3 → MvPolynomial (Fin 2) k :=
  ![MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1, MvPolynomial.X 1 ^ 2]

/-- Example `ex:branch-singular` of `paper.tex`: `f(u,v) = (u², uv, v²)` lands on the quadric cone
`Y = Spec k[x,y,z]/(xz - y²)`, i.e. the `k`-algebra map `k[x,y,z]/(xz - y²) → k[u,v]`,
`x ↦ u²`, `y ↦ uv`, `z ↦ v²`, is well defined. -/
noncomputable def coneParam :
    (MvPolynomial (Fin 3) k ⧸ coneIdeal k) →ₐ[k] MvPolynomial (Fin 2) k :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (coneMap k)) <| by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simp [coneMap, mul_comm]
    ring

/-- Example `ex:branch-singular` of `paper.tex`: pointwise form, the image of `f(u,v) = (u², uv,
v²)` lies on
the quadric cone `xz = y²`. -/
theorem cone_pointwise (u v : k) : u ^ 2 * v ^ 2 = (u * v) ^ 2 := by ring

/-- Example `ex:branch-singular` of `paper.tex`: restricting `f(u,v) = (u², uv, v²)` to `A = V(v)` —
that is,
substituting `v = 0` — gives `u ↦ (u², 0, 0)`, so the restriction `g : A → B = V(y, z)` is
`g(u) = u²`. -/
theorem coneMap_restrict (i : Fin 3) :
    MvPolynomial.aeval ![(Polynomial.X : Polynomial k), 0] (coneMap k i)
      = ![Polynomial.X ^ 2, 0, 0] i := by
  fin_cases i <;> simp [coneMap]

end QuadricCone

section Ramification

variable (k : Type*) [Field k]

/-- Example `ex:branch-singular` of `paper.tex`: the restriction `g(u) = u²` ramifies exactly at the
origin:
`u² = 0` if and only if `u = 0`. -/
theorem sq_eq_zero_iff (u : k) : u ^ 2 = 0 ↔ u = 0 := pow_eq_zero_iff two_ne_zero

/-- Example `ex:branch-singular` of `paper.tex`: over an algebraically closed field the restriction
`g(u) = u²` is surjective, so `B` is the affine line and `g` is a degree-`2` cover
branched exactly at the vertex `o`. -/
theorem sq_surjective [IsAlgClosed k] (w : k) : ∃ u : k, u ^ 2 = w :=
  IsAlgClosed.exists_pow_nat_eq w two_pos

end Ramification

end Pcf.Examples.Cusp

#print axioms Pcf.Examples.Cusp.cuspParam
#print axioms Pcf.Examples.Cusp.cuspParam_x
#print axioms Pcf.Examples.Cusp.cuspParam_y
#print axioms Pcf.Examples.Cusp.jacobian_cuspSource
#print axioms Pcf.Examples.Cusp.cusp_inter_branch
#print axioms Pcf.Examples.Cusp.mem_cuspAlg_iff
#print axioms Pcf.Examples.Cusp.X_notMem_cuspAlg
#print axioms Pcf.Examples.Cusp.isIntegral_X
#print axioms Pcf.Examples.Cusp.isIntegral_cuspAlg
#print axioms Pcf.Examples.Cusp.isIntegralClosure_cuspAlg
#print axioms Pcf.Examples.Cusp.isFractionRing_cuspAlg
#print axioms Pcf.Examples.Cusp.integralClosure_cuspAlg_eq_top
#print axioms Pcf.Examples.Cusp.isIntegrallyClosed_polynomial
#print axioms Pcf.Examples.Cusp.coneParam
#print axioms Pcf.Examples.Cusp.coneMap_restrict
#print axioms Pcf.Examples.Cusp.sq_eq_zero_iff
#print axioms Pcf.Examples.Cusp.sq_surjective
