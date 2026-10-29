/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperCuspCanonical

/-!
# The normalization of the cusp is a homeomorphism

`paper.tex`, Remark `rem:why-normalized`, algebraic part: the normalization of
a cuspidal curve is a homeomorphism and is not branched.

For the cusp `y² = x³`, represented by the actual monomial subalgebra
`k[t², t³] ⊆ k[t]` (identified with `k[x,y]/(y² - x³)` in
`CharZeroPaperCuspBranch.cuspQuotientEquiv`), we prove that the project's
canonical normalization map `Palomar.normalizationMap (cusp k)` is a
homeomorphism of underlying topological spaces, and that its normalized branch
support is empty.

The proof of injectivity is direct commutative algebra: every `t² f` lies in
`k[t², t³]`, so primes of `k[t]` not containing `t` are determined by their
contractions, while `(t)` is the only prime containing `t`. Finiteness gives a
closed map, and surjectivity is already known. The complex-analytic local-degree
sentence of the remark is not formalized here.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperCuspHomeomorph

open CategoryTheory AlgebraicGeometry Polynomial
open CharZeroPaperCuspGeometry CharZeroPaperCuspCanonical Pcf.PaperCharZero

universe u
variable (k : Type u) [Field k]

/-- `t² f ∈ k[t², t³]` for every polynomial `f`. -/
theorem X_sq_mul_mem (f : Polynomial k) :
    (X : Polynomial k) ^ 2 * f ∈ Cusp.cuspAlg k := by
  rw [Cusp.mem_cuspAlg_iff]
  rw [Polynomial.coeff_X_pow_mul']
  simp

/-- The parametrization `Spec k[t] → Spec k[t², t³]` is injective on points. -/
theorem parametrization_injective :
    Function.Injective (parametrization k) := by
  intro p q hpq
  have hcomap : ∀ a : CuspRing k, (a : Polynomial k) ∈ p.asIdeal ↔
      (a : Polynomial k) ∈ q.asIdeal := by
    intro a
    have h : (parametrization k p).asIdeal = (parametrization k q).asIdeal := by rw [hpq]
    exact SetLike.ext_iff.mp h a
  have hsq : (X : Polynomial k) ^ 2 ∈ Cusp.cuspAlg k := Cusp.X_sq_mem k
  have hX : (X : Polynomial k) ∈ p.asIdeal ↔ (X : Polynomial k) ∈ q.asIdeal := by
    have h := hcomap ⟨_, hsq⟩
    simp only at h
    constructor
    · intro hp
      exact q.isPrime.mem_of_pow_mem 2 (h.mp (p.asIdeal.pow_mem_of_mem hp 2 two_pos))
    · intro hq
      exact p.isPrime.mem_of_pow_mem 2 (h.mpr (q.asIdeal.pow_mem_of_mem hq 2 two_pos))
  apply PrimeSpectrum.ext
  by_cases hp : (X : Polynomial k) ∈ p.asIdeal
  · have hq := hX.mp hp
    have hmax : (Ideal.span {(X : Polynomial k)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
    have hp' := hmax.eq_of_le p.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hp)
    have hq' := hmax.eq_of_le q.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hq)
    rw [← hp', ← hq']
  · have hq : (X : Polynomial k) ∉ q.asIdeal := fun h => hp (hX.mpr h)
    have key : ∀ (r s : PrimeSpectrum (ParameterRing k)),
        (X : Polynomial k) ∉ s.asIdeal →
        (∀ a : CuspRing k, (a : Polynomial k) ∈ r.asIdeal ↔ (a : Polynomial k) ∈ s.asIdeal) →
        r.asIdeal ≤ s.asIdeal := by
      intro r s hs hrs f hf
      have hmem : (X : Polynomial k) ^ 2 * f ∈ s.asIdeal :=
        (hrs ⟨_, X_sq_mul_mem k f⟩).mp (r.asIdeal.mul_mem_left _ hf)
      rcases s.isPrime.mem_or_mem hmem with h | h
      · exact absurd (s.isPrime.mem_of_pow_mem 2 h) hs
      · exact h
    exact le_antisymm (key p q hq hcomap) (key q p hp fun a => (hcomap a).symm)

/-- The parametrization `t ↦ (t², t³)` is a homeomorphism of underlying spaces. -/
theorem parametrization_isHomeomorph : IsHomeomorph (parametrization k) :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨(parametrization k).continuous, (parametrization k).isClosedMap,
      parametrization_injective k, (parametrization k).surjective⟩

/-- The canonical normalization map of the cusp is the inverse of the canonical
identification followed by the parametrization. -/
theorem normalizationMap_eq :
    Palomar.normalizationMap (cusp k) =
      (parameterLineNormalizationIso k).inv ≫ parametrization k := by
  rw [← parameterLineNormalizationIso_comm, Iso.inv_hom_id_assoc]

/-- `rem:why-normalized`: the canonical normalization map of the cusp
`y² = x³` is a homeomorphism of underlying topological spaces. -/
theorem normalizationMap_isHomeomorph :
    IsHomeomorph (Palomar.normalizationMap (cusp k)) := by
  rw [normalizationMap_eq]
  have hiso : IsHomeomorph (parameterLineNormalizationIso k).inv :=
    (Scheme.homeoOfIso (parameterLineNormalizationIso k).symm).isHomeomorph
  simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp] using
    (parametrization_isHomeomorph k).comp hiso

instance normalizationMap_isFinite : IsFinite (Palomar.normalizationMap (cusp k)) := by
  rw [normalizationMap_eq]; infer_instance

instance normalizationMap_surjective : Surjective (Palomar.normalizationMap (cusp k)) := by
  rw [normalizationMap_eq]; infer_instance

/-- `rem:why-normalized`: the canonical normalization map of the cusp is not
branched; its normalized branch support is empty. -/
theorem normalizationMap_branch_empty :
    normalizedMorphismBranchSupport (Palomar.normalizationMap (cusp k)) = ∅ :=
  normalizedMorphismBranchSupport_empty_of_factor _ _ (𝟙 _) (Category.id_comp _)

#print axioms X_sq_mul_mem
#print axioms parametrization_injective
#print axioms parametrization_isHomeomorph
#print axioms normalizationMap_eq
#print axioms normalizationMap_isHomeomorph
#print axioms normalizationMap_isFinite
#print axioms normalizationMap_surjective
#print axioms normalizationMap_branch_empty

end Pcf.Examples.CharZeroPaperCuspHomeomorph
