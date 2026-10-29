/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharP
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The actual affine morphism in Example `ex:frobenius-line`

The live `paper-p.tex` example is the affine endomorphism
`(u,v) ↦ (u^p+uv,v)`. It is not the subsequent projective wild example.
This module proves that its actual coordinate map is finite and injective,
hence its actual spectrum morphism is finite and surjective.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusLine

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ)

abbrev Plane := MvPolynomial (Fin 2) k
abbrev Coeff := MvPolynomial (Fin 1) k

noncomputable def u : Plane k := MvPolynomial.X 0
noncomputable def v : Plane k := MvPolynomial.X 1

noncomputable def coordinateMap : Plane k →ₐ[k] Plane k :=
  MvPolynomial.aeval ![u k ^ p + u k * v k, v k]

@[simp] theorem coordinateMap_u : coordinateMap k p (u k) = u k ^ p + u k * v k := by
  simp [coordinateMap, u]

@[simp] theorem coordinateMap_v : coordinateMap k p (v k) = v k := by
  simp [coordinateMap, v]

/-- The first source coordinate is integral over the target coordinate ring. -/
theorem u_isIntegral (hp : 2 ≤ p) :
    letI : Algebra (Plane k) (Plane k) := (coordinateMap k p).toRingHom.toAlgebra
    IsIntegral (Plane k) (u k) := by
  letI : Algebra (Plane k) (Plane k) := (coordinateMap k p).toRingHom.toAlgebra
  refine ⟨Polynomial.X ^ p + Polynomial.C (v k) * Polynomial.X - Polynomial.C (u k),
    Pcf.Examples.CharP.monic_charPoly hp _ _, ?_⟩
  change Polynomial.aeval (u k)
    (Polynomial.X ^ p + Polynomial.C (v k) * Polynomial.X - Polynomial.C (u k)) = 0
  simp only [map_sub, map_add, map_pow, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
  change u k ^ p + coordinateMap k p (v k) * u k - coordinateMap k p (u k) = 0
  rw [coordinateMap_v, coordinateMap_u]
  ring

/-- Adjoining the first source coordinate already generates the source ring,
since the second coordinate is fixed by the map. -/
theorem adjoin_u_eq_top :
    letI : Algebra (Plane k) (Plane k) := (coordinateMap k p).toRingHom.toAlgebra
    Algebra.adjoin (Plane k) {u k} = ⊤ := by
  letI : Algebra (Plane k) (Plane k) := (coordinateMap k p).toRingHom.toAlgebra
  let A := Algebra.adjoin (Plane k) {u k}
  apply eq_top_iff.mpr
  intro q _
  change q ∈ A
  induction q using MvPolynomial.induction_on with
  | C a =>
      have h := A.algebraMap_mem (algebraMap k (Plane k) a)
      have heq : algebraMap (Plane k) (Plane k) (algebraMap k (Plane k) a) =
          MvPolynomial.C a := (coordinateMap k p).commutes a
      rwa [heq] at h
  | add a b ha hb => exact add_mem (ha trivial) (hb trivial)
  | mul_X q i hq =>
      fin_cases i
      · exact mul_mem (hq trivial) (Algebra.subset_adjoin rfl)
      · have hv : v k ∈ A := by
          have h := A.algebraMap_mem (v k)
          change coordinateMap k p (v k) ∈ A at h
          rwa [coordinateMap_v] at h
        exact mul_mem (hq trivial) hv

private theorem finite_of_integral_adjoin_eq_top {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : S)
    (hx : letI := f.toAlgebra; IsIntegral R x)
    (hgen : letI := f.toAlgebra; Algebra.adjoin R {x} = ⊤) : f.Finite := by
  letI := f.toAlgebra
  have h := hx.fg_adjoin_singleton
  rw [hgen] at h
  haveI : Module.Finite R S := by
    rw [Module.finite_def]
    simpa using h
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The actual coordinate map is finite. -/
theorem coordinateMap_finite (hp : 2 ≤ p) : (coordinateMap k p).toRingHom.Finite :=
  finite_of_integral_adjoin_eq_top _ (u k) (u_isIntegral k p hp) (adjoin_u_eq_top k p)

/-- View the first-coordinate substitution as a polynomial over `k[v]`. -/
noncomputable def substitutionPolynomial : Polynomial (Coeff k) :=
  Polynomial.X ^ p + Polynomial.C (MvPolynomial.X 0) * Polynomial.X

noncomputable def substitution : Polynomial (Coeff k) →ₐ[Coeff k] Polynomial (Coeff k) :=
  Polynomial.aeval (substitutionPolynomial k p)

theorem substitution_natDegree (hp : 2 ≤ p) : (substitutionPolynomial k p).natDegree = p := by
  unfold substitutionPolynomial
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
  rw [Polynomial.natDegree_X_pow]
  have hle : (Polynomial.C (MvPolynomial.X (0 : Fin 1) : Coeff k) * Polynomial.X).natDegree ≤ 1 :=
    (Polynomial.natDegree_mul_le).trans (by simp)
  omega

theorem substitution_injective (hp : 2 ≤ p) : Function.Injective (substitution k p) := by
  intro a b hab
  have hz : (a - b).comp (substitutionPolynomial k p) = 0 := by
    change a.comp (substitutionPolynomial k p) = b.comp (substitutionPolynomial k p) at hab
    simpa only [Polynomial.sub_comp, sub_eq_zero] using hab
  rcases Polynomial.comp_eq_zero_iff.mp hz with h | ⟨_, h⟩
  · exact sub_eq_zero.mp h
  · have hd := congrArg Polynomial.natDegree h
    rw [substitution_natDegree k p hp, Polynomial.natDegree_C] at hd
    omega

/-- The polynomial-coordinate conjugation is an equality of actual algebra maps. -/
theorem coordinateMap_conjugation :
    (MvPolynomial.finSuccEquiv k 1).toAlgHom.comp (coordinateMap k p) =
      ((substitution k p).restrictScalars k).comp (MvPolynomial.finSuccEquiv k 1).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · have h1 := MvPolynomial.finSuccEquiv_X_succ (R := k) (n := 1) (j := (0 : Fin 1))
    simp only [show (0 : Fin 1).succ = (1 : Fin 2) by rfl] at h1
    simp [coordinateMap, u, v, substitution, substitutionPolynomial, h1,
      MvPolynomial.finSuccEquiv_X_zero]
  · have h1 := MvPolynomial.finSuccEquiv_X_succ (R := k) (n := 1) (j := (0 : Fin 1))
    simp only [show (0 : Fin 1).succ = (1 : Fin 2) by rfl] at h1
    simp [coordinateMap, u, v, substitution, h1]

theorem coordinateMap_injective (hp : 2 ≤ p) : Function.Injective (coordinateMap k p) := by
  intro a b hab
  apply (MvPolynomial.finSuccEquiv k 1).injective
  apply substitution_injective k p hp
  have h (q : Plane k) := congrArg (fun f : Plane k →ₐ[k] Polynomial (Coeff k) => f q)
    (coordinateMap_conjugation k p)
  exact (h a).symm.trans ((congrArg (MvPolynomial.finSuccEquiv k 1) hab).trans (h b))

noncomputable def schemeMap : Spec (.of (Plane k)) ⟶ Spec (.of (Plane k)) :=
  Spec.map (CommRingCat.ofHom (coordinateMap k p).toRingHom)

/-- `paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_finite (hp : 2 ≤ p) : IsFinite (schemeMap k p) :=
  (IsFinite.SpecMap_iff _).mpr (coordinateMap_finite k p hp)

/-- `paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_surjective (hp : 2 ≤ p) : Surjective (schemeMap k p) := by
  rw [surjective_iff]
  exact (coordinateMap_finite k p hp).to_isIntegral.comap_surjective
    (coordinateMap_injective k p hp)

#print axioms u_isIntegral
#print axioms coordinateMap_finite
#print axioms coordinateMap_injective
#print axioms schemeMap_finite
#print axioms schemeMap_surjective

end Pcf.Examples.PaperP.FrobeniusLine
