/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusLineMap
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.ComputeDegree

/-!
# A degree-`p+1` map with an inseparable divisorial residue extension

`paper-p.tex`, `sec:prime-to-p` (the sentence after the section title):
"A condition only on the degree of the original map would not control residue
fields."  The counterexample is the affine map
`F : 𝔸²_{x,w} → 𝔸²_{u,v}`, `F^*(u) = x^p + x w`, `F^*(v) = w (x - 1)`.

Both planes are the ring `Plane k = k[X₀, X₁]` of the Frobenius-line example;
on the source `X₀ = x`, `X₁ = w`, on the target `X₀ = u`, `X₁ = v`.

Since `u - v = x^p + w`, the source ring is generated over `k[u,v]` by `x`, which
is a root of the monic polynomial `T^{p+1} - T^p - (u - v) T + u`. The source is
in fact isomorphic to `AdjoinRoot` of that polynomial, hence free of rank `p+1`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.DegreeOnlyResidue

open AlgebraicGeometry CategoryTheory Polynomial
open Pcf.Examples.PaperP.FrobeniusLine (Plane u v)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ)

/-- The coordinate pullback `u ↦ x^p + x w`, `v ↦ w (x - 1)`. -/
noncomputable def coordinateMap : Plane k →ₐ[k] Plane k :=
  MvPolynomial.aeval ![u k ^ p + u k * v k, v k * (u k - 1)]

@[simp] theorem coordinateMap_u : coordinateMap k p (u k) = u k ^ p + u k * v k := by
  simp [coordinateMap, u]

@[simp] theorem coordinateMap_v : coordinateMap k p (v k) = v k * (u k - 1) := by
  simp [coordinateMap, v]

/-- The source coordinate ring, carrying the `k[u,v]`-algebra structure of `F^*`.
It is a type synonym to keep this structure apart from `Algebra.id`. -/
def Source (k : Type*) [Field k] (_p : ℕ) : Type _ := MvPolynomial (Fin 2) k

noncomputable instance : CommRing (Source k p) := inferInstanceAs (CommRing (Plane k))
instance : IsDomain (Source k p) := inferInstanceAs (IsDomain (Plane k))
noncomputable instance : Algebra (Plane k) (Source k p) := (coordinateMap k p).toRingHom.toAlgebra

/-- The identity of the underlying ring. -/
noncomputable def toSource : Plane k ≃+* Source k p := RingEquiv.refl _

theorem algebraMap_source (b : Plane k) :
    algebraMap (Plane k) (Source k p) b = toSource k p (coordinateMap k p b) := rfl

/-- The monic polynomial of `x` over `k[u,v]`. -/
noncomputable def minPoly : (Plane k)[X] :=
  X ^ (p + 1) - X ^ p - C (u k - v k) * X + C (u k)

theorem minPoly_eq : minPoly k p = X ^ (p + 1) + (-(X ^ p) - C (u k - v k) * X + C (u k)) := by
  unfold minPoly; ring

theorem minPoly_monic (hp : 0 < p) : (minPoly k p).Monic := by
  rw [minPoly_eq]
  apply Polynomial.monic_X_pow_add
  refine (degree_add_le _ _).trans_lt (max_lt ((degree_sub_le _ _).trans_lt
    (max_lt ?_ ?_)) ?_)
  · rw [degree_neg, degree_X_pow]
    exact_mod_cast Nat.lt_succ_self p
  · refine (degree_C_mul_X_le _).trans_lt ?_
    exact_mod_cast (by omega : 1 < p + 1)
  · exact (degree_C_le).trans_lt (by exact_mod_cast Nat.succ_pos p)

theorem minPoly_natDegree (hp : 0 < p) : (minPoly k p).natDegree = p + 1 := by
  rw [minPoly_eq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  refine (degree_add_le _ _).trans_lt (max_lt ((degree_sub_le _ _).trans_lt
    (max_lt ?_ ?_)) ?_)
  · rw [degree_neg, degree_X_pow]
    exact_mod_cast Nat.lt_succ_self p
  · refine (degree_C_mul_X_le _).trans_lt ?_
    exact_mod_cast (by omega : 1 < p + 1)
  · exact (degree_C_le).trans_lt (by exact_mod_cast Nat.succ_pos p)

variable {p}

/-- The source coordinate `x`. -/
noncomputable def xs : Source k p := toSource k p (u k)

/-- `x` is a root of `T^{p+1} - T^p - (u - v) T + u`. -/
theorem aeval_xs : aeval (xs k (p := p)) (minPoly k p) = 0 := by
  simp only [minPoly, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, algebraMap_source, xs]
  change (u k) ^ (p + 1) - (u k) ^ p -
    (coordinateMap k p (u k) - coordinateMap k p (v k)) * u k +
    coordinateMap k p (u k) = (0 : Plane k)
  rw [coordinateMap_u, coordinateMap_v]
  ring

/-- The candidate inverse, sending `x ↦ root` and `w ↦ (u - v) - root^p`. -/
noncomputable def fromSourceRing : Plane k →+* AdjoinRoot (minPoly k p) :=
  MvPolynomial.eval₂Hom ((AdjoinRoot.of (minPoly k p)).comp (algebraMap k (Plane k)))
    ![AdjoinRoot.root (minPoly k p),
      AdjoinRoot.of (minPoly k p) (u k) - AdjoinRoot.of (minPoly k p) (v k) -
        AdjoinRoot.root (minPoly k p) ^ p]

theorem root_relation :
    AdjoinRoot.root (minPoly k p) ^ (p + 1) - AdjoinRoot.root (minPoly k p) ^ p -
      (AdjoinRoot.of (minPoly k p) (u k) - AdjoinRoot.of (minPoly k p) (v k)) *
        AdjoinRoot.root (minPoly k p) + AdjoinRoot.of (minPoly k p) (u k) = 0 := by
  have h := AdjoinRoot.eval₂_root (minPoly k p)
  simpa [minPoly, eval₂_sub, eval₂_add, eval₂_mul] using h

theorem fromSourceRing_comp :
    (fromSourceRing k).comp (coordinateMap k p).toRingHom = AdjoinRoot.of (minPoly k p) := by
  have h := root_relation k (p := p)
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [fromSourceRing, MvPolynomial.algebraMap_eq]
  · intro i
    fin_cases i
    · change fromSourceRing k (coordinateMap k p (u k)) = AdjoinRoot.of _ (u k)
      rw [coordinateMap_u]
      simp only [fromSourceRing, map_add, map_mul, map_pow, u, v, MvPolynomial.eval₂Hom_X']
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [u, v] at h
      linear_combination (-1 : AdjoinRoot (minPoly k p)) * h
    · change fromSourceRing k (coordinateMap k p (v k)) = AdjoinRoot.of _ (v k)
      rw [coordinateMap_v]
      simp only [fromSourceRing, map_sub, map_mul, map_one, u, v, MvPolynomial.eval₂Hom_X']
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [u, v] at h
      linear_combination (-1 : AdjoinRoot (minPoly k p)) * h

/-- The inverse as a `k[u,v]`-algebra map. -/
noncomputable def fromSource : Source k p →ₐ[Plane k] AdjoinRoot (minPoly k p) where
  toRingHom := (fromSourceRing k).comp (toSource k p).symm.toRingHom
  commutes' b := congrArg (fun f : Plane k →+* AdjoinRoot (minPoly k p) => f b)
    (fromSourceRing_comp k)

/-- `x` generates the source over `k[u,v]`. -/
noncomputable def toSourceAlg : AdjoinRoot (minPoly k p) →ₐ[Plane k] Source k p :=
  AdjoinRoot.liftAlgHom (minPoly k p) (Algebra.ofId (Plane k) (Source k p)) (xs k)
    (aeval_xs k)

theorem toSourceAlg_comp_fromSource :
    (toSourceAlg k).toRingHom.comp (fromSourceRing k) = (toSource k p).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [fromSourceRing, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
    change toSourceAlg k (AdjoinRoot.of _ (algebraMap k (Plane k) c)) = _
    rw [toSourceAlg, AdjoinRoot.liftAlgHom_of]
    change toSource k p (coordinateMap k p (algebraMap k (Plane k) c)) = _
    rw [AlgHom.commutes]
    rfl
  · intro i
    fin_cases i
    · simp only [fromSourceRing, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      change toSourceAlg k (AdjoinRoot.root _) = _
      rw [toSourceAlg, AdjoinRoot.liftAlgHom_root]
      rfl
    · simp only [fromSourceRing, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
      change toSourceAlg k (AdjoinRoot.of _ (u k) - AdjoinRoot.of _ (v k) -
        AdjoinRoot.root _ ^ p) = _
      rw [map_sub, map_sub, map_pow, toSourceAlg, AdjoinRoot.liftAlgHom_of,
        AdjoinRoot.liftAlgHom_of, AdjoinRoot.liftAlgHom_root, ← map_sub]
      change coordinateMap k p (u k - v k) - (u k) ^ p = (MvPolynomial.X 1 : Plane k)
      rw [map_sub, coordinateMap_u, coordinateMap_v]
      change _ = v k
      ring

/-- The source ring is `AdjoinRoot` of the monic polynomial of `x`. -/
noncomputable def adjoinRootEquiv : AdjoinRoot (minPoly k p) ≃ₐ[Plane k] Source k p :=
  AlgEquiv.ofAlgHom (toSourceAlg k) (fromSource k)
    (by
      apply AlgHom.toRingHom_injective
      apply RingHom.ext
      intro a
      have h := congrArg (fun f : Plane k →+* Source k p => f ((toSource k p).symm a))
        (toSourceAlg_comp_fromSource k)
      exact h)
    (by
      apply AdjoinRoot.algHom_ext
      change fromSource k (toSourceAlg k (AdjoinRoot.root _)) = AdjoinRoot.root _
      rw [toSourceAlg, AdjoinRoot.liftAlgHom_root]
      change fromSourceRing k (u k) = _
      simp [fromSourceRing, u])

variable (p)

/-- A power basis `1, x, …, x^p` of the source over `k[u,v]`. -/
noncomputable def powerBasis (hp : 0 < p) : PowerBasis (Plane k) (Source k p) :=
  (AdjoinRoot.powerBasis' (minPoly_monic k p hp)).map (adjoinRootEquiv k)

theorem powerBasis_dim (hp : 0 < p) : (powerBasis k p hp).dim = p + 1 := by
  simp [powerBasis, minPoly_natDegree k p hp]

/-- **The source is free of rank `p + 1` over the target.** -/
theorem finrank_source (hp : 0 < p) : Module.finrank (Plane k) (Source k p) = p + 1 := by
  rw [(powerBasis k p hp).finrank, powerBasis_dim]

theorem source_free (hp : 0 < p) : Module.Free (Plane k) (Source k p) :=
  .of_basis (powerBasis k p hp).basis

theorem source_finite (hp : 0 < p) : Module.Finite (Plane k) (Source k p) :=
  .of_basis (powerBasis k p hp).basis

/-- The actual coordinate map is finite. -/
theorem coordinateMap_finite (hp : 0 < p) : (coordinateMap k p).toRingHom.Finite :=
  source_finite k p hp

/-- The actual coordinate map is injective. -/
theorem coordinateMap_injective (hp : 0 < p) : Function.Injective (coordinateMap k p) := by
  haveI := source_free k p hp
  exact FaithfulSMul.algebraMap_injective (Plane k) (Source k p)

/-- The actual morphism `F : 𝔸²_{x,w} → 𝔸²_{u,v}`. -/
noncomputable def schemeMap : Spec (.of (Plane k)) ⟶ Spec (.of (Plane k)) :=
  Spec.map (CommRingCat.ofHom (coordinateMap k p).toRingHom)

theorem schemeMap_finite (hp : 0 < p) : IsFinite (schemeMap k p) :=
  (IsFinite.SpecMap_iff _).mpr (coordinateMap_finite k p hp)

theorem schemeMap_surjective (hp : 0 < p) : Surjective (schemeMap k p) := by
  rw [surjective_iff]
  exact (coordinateMap_finite k p hp).to_isIntegral.comap_surjective
    (coordinateMap_injective k p hp)

#print axioms adjoinRootEquiv
#print axioms finrank_source
#print axioms coordinateMap_finite
#print axioms coordinateMap_injective
#print axioms schemeMap_finite
#print axioms schemeMap_surjective

end Pcf.Examples.PaperP.DegreeOnlyResidue
