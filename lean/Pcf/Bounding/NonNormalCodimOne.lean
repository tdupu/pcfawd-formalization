/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.Divisors
public import Pcf.Bounding.GlobalNormalizationFinite
public import Mathlib.RingTheory.Localization.Integer

/-!
# Finitely many non-normal codimension-one points

On an integral scheme locally of finite type over a field with Noetherian
underlying space, only finitely many codimension-one points have non-normal
local rings. On an affine chart `Spec B`, the integral closure of `B` is a
finite `B`-module, so one nonzero `c ∈ B` (a conductor element) clears its
denominators; every stalk off `V(c)` is integrally closed, and the height-one
primes containing `c` are minimal over `(c)`. This replaces closedness of the
singular locus of a codimension-one subvariety in the proof of
`latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory

universe u v

set_option linter.style.haveILetI false

section Algebra

variable (B : Type u) [CommRing B] [IsDomain B] (K : Type v) [Field K] [Algebra B K]
  [IsFractionRing B K]

/-- A finite integral closure has a nonzero conductor element. -/
theorem exists_conductor_of_finite [Module.Finite B (integralClosure B K)] :
    ∃ c : B, c ≠ 0 ∧ ∀ x : K, IsIntegral B x → IsLocalization.IsInteger B (c • x) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := integralClosure B K)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors B)
    (s.image (fun y : integralClosure B K => (y : K)))
  refine ⟨b, nonZeroDivisors.ne_zero b.2, fun x hx => ?_⟩
  have hmem : (⟨x, hx⟩ : integralClosure B K) ∈
      Submodule.span B (s : Set (integralClosure B K)) := by
    rw [hs]
    trivial
  let Pr : integralClosure B K → Prop := fun y => IsLocalization.IsInteger B ((b : B) • (y : K))
  change Pr ⟨x, hx⟩
  refine Submodule.span_induction (p := fun y _ => Pr y) ?_ ?_ ?_ ?_ hmem
  · intro y hy
    exact hb _ (Finset.mem_image_of_mem _ hy)
  · change IsLocalization.IsInteger B ((b : B) • (0 : K))
    rw [smul_zero]
    exact ⟨0, map_zero _⟩
  · intro y z _ _ hy hz
    change IsLocalization.IsInteger B ((b : B) • ((y : K) + (z : K)))
    rw [smul_add]
    obtain ⟨u, hu⟩ := hy
    obtain ⟨v, hv⟩ := hz
    exact ⟨u + v, by rw [map_add, hu, hv]⟩
  · intro r y _ hy
    change IsLocalization.IsInteger B ((b : B) • (r • (y : K)))
    rw [smul_comm]
    obtain ⟨u, hu⟩ := hy
    exact ⟨r * u, by rw [map_mul, hu, Algebra.smul_def r]⟩

/-- Off the conductor, the localization is integrally closed. -/
theorem isIntegrallyClosed_localization_of_conductor (c : B)
    (hc : ∀ x : K, IsIntegral B x → IsLocalization.IsInteger B (c • x))
    (P : Ideal B) [P.IsPrime] (hcP : c ∉ P) :
    IsIntegrallyClosed (Localization.AtPrime P) := by
  let L := Localization.AtPrime P
  have hM : P.primeCompl ≤ nonZeroDivisors B := P.primeCompl_le_nonZeroDivisors
  let g : L →+* K := IsLocalization.map _ (T := nonZeroDivisors B) (RingHom.id B) hM
  letI := g.toAlgebra
  have : IsScalarTower B L K := IsScalarTower.of_algebraMap_eq'
    (by
      rw [RingHom.algebraMap_toAlgebra]
      exact (IsLocalization.map_comp (M := P.primeCompl) (S := L) (T := nonZeroDivisors B)
        (Q := K) (g := RingHom.id B) hM).symm)
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl L K
  refine (isIntegrallyClosed_iff_isIntegralClosure (K := K)).mpr
    ⟨IsFractionRing.injective _ _,
      fun {x} ↦ ⟨?_, fun e ↦ e.choose_spec ▸ isIntegral_algebraMap⟩⟩
  intro hx
  obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization P.primeCompl _
  obtain ⟨z, hz⟩ := hc _ hy
  have hcy : c * y ∈ P.primeCompl := P.primeCompl.mul_mem hcP y_mem
  refine ⟨IsLocalization.mk' L z ⟨c * y, hcy⟩,
    (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_⟩
  rw [RingHom.comp_id, hz, Submonoid.mk_smul, smul_smul, Algebra.smul_def]

/-- A height-one prime containing a nonzero element is minimal over it. -/
theorem mem_minimalPrimes_span_of_height_eq_one {c : B} (hc : c ≠ 0)
    (P : Ideal B) [P.IsPrime] (hP : P.height = 1) (hcP : c ∈ P) :
    P ∈ (Ideal.span {c}).minimalPrimes := by
  have hle : Ideal.span {c} ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hcP
  refine ⟨⟨‹_›, hle⟩, fun Q ⟨hQ, hQc⟩ hQP => ?_⟩
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hQP (fun h => hne (h ▸ le_refl _))
  have hh := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hP] at hh
  have h0 : Q.height = 0 := by
    by_contra h0
    have h1 : 1 ≤ Q.height := Order.one_le_iff_ne_zero.mpr h0
    have h3 : (1 : ℕ∞) + 1 ≤ Q.height + 1 := by gcongr
    have h2 : (1 : ℕ∞) + 1 ≤ 1 := h3.trans hh
    norm_num at h2
  rw [Ideal.height_eq_zero_iff_eq_bot] at h0
  apply hc
  have : c ∈ Q := hQc (Ideal.mem_span_singleton_self c)
  rw [h0] at this
  exact this

end Algebra

section Scheme

/-- On one affine chart, only finitely many codimension-one points are non-normal. -/
theorem finite_nonNormal_schemeDivisorPoint_affine
    (k : Type u) [Field k] {D : Scheme.{u}} [IsIntegral D]
    (s : D ⟶ Spec (.of k)) [LocallyOfFiniteType s] (U : D.affineOpens) :
    {d : SchemeDivisorPoint D | d.1 ∈ (U : D.Opens) ∧
      ¬ IsIntegrallyClosed (D.presheaf.stalk d.1)}.Finite := by
  by_cases hne : Nonempty (U : D.Opens)
  swap
  · convert Set.finite_empty
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hd
    exact (hne ⟨⟨d.1, hd⟩⟩).elim
  have hU : IsAffineOpen (U : D.Opens) := U.2
  let B := Γ(D, U)
  let φ : k →+* B := (s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  letI : Algebra k B := φ.toAlgebra
  have hft : Algebra.FiniteType k B := by
    apply RingHom.finiteType_algebraMap.mp
    change φ.FiniteType
    exact (s.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  haveI : Module.Finite B (integralClosure B (FractionRing B)) :=
    finite_integralClosure_of_finiteType k B (FractionRing B)
  obtain ⟨c, hc0, hc⟩ := exists_conductor_of_finite B (FractionRing B)
  let S : Set (PrimeSpectrum B) := {P | P.asIdeal ∈ (Ideal.span {c}).minimalPrimes}
  have hS : S.Finite :=
    ((Ideal.span {c}).finite_minimalPrimes_of_isNoetherianRing B).preimage
      (fun _ _ _ _ h => PrimeSpectrum.ext h)
  apply Set.Finite.of_finite_image (f := fun d : SchemeDivisorPoint D => d.1)
    _ (fun _ _ _ _ h => Subtype.ext h)
  apply (hS.image hU.fromSpec).subset
  rintro _ ⟨d, ⟨hdU, hnn⟩, rfl⟩
  let P := hU.primeIdealOf ⟨d.1, hdU⟩
  refine ⟨P, ?_, hU.fromSpec_primeIdealOf ⟨d.1, hdU⟩⟩
  have hheight : P.asIdeal.height = 1 := by
    have h1 := idealHeight_eq_coheight Γ(D, U) P
    have h2 := coheight_eq_of_isOpenImmersion (x := P) hU.fromSpec
    rw [IsAffineOpen.fromSpec_primeIdealOf] at h2
    exact h1.trans (h2.symm.trans d.2)
  have hcP : c ∈ P.asIdeal := by
    by_contra hcP
    apply hnn
    haveI := isIntegrallyClosed_localization_of_conductor B (FractionRing B) c hc P.asIdeal hcP
    letI : Algebra Γ(D, U) (D.presheaf.stalk d.1) :=
      TopCat.Presheaf.algebra_section_stalk D.presheaf ⟨d.1, hdU⟩
    haveI : IsLocalization.AtPrime (D.presheaf.stalk d.1) P.asIdeal :=
      hU.isLocalization_stalk ⟨d.1, hdU⟩
    exact IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv P.asIdeal.primeCompl (Localization.AtPrime P.asIdeal)
        (D.presheaf.stalk d.1)).toRingEquiv
  exact mem_minimalPrimes_span_of_height_eq_one B hc0 P.asIdeal hheight hcP

/-- **Finitely many non-normal codimension-one points.** -/
theorem finite_nonNormal_schemeDivisorPoint
    (k : Type u) [Field k] {D : Scheme.{u}} [IsIntegral D]
    (s : D ⟶ Spec (.of k)) [LocallyOfFiniteType s] [TopologicalSpace.NoetherianSpace D] :
    {d : SchemeDivisorPoint D | ¬ IsIntegrallyClosed (D.presheaf.stalk d.1)}.Finite := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : D.affineOpens => ((U : D.Opens) : Set D)) (fun U => (U : D.Opens).isOpen)
    (by
      intro x _
      obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : D.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  apply (t.finite_toSet.biUnion
    (fun U _ => finite_nonNormal_schemeDivisorPoint_affine k s U)).subset
  intro d hd
  obtain ⟨U, hUt, hdU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ d.1))
  exact Set.mem_iUnion₂.mpr ⟨U, hUt,
    show d ∈ {d : SchemeDivisorPoint D | d.1 ∈ (U : D.Opens) ∧
      ¬ IsIntegrallyClosed (D.presheaf.stalk d.1)} from ⟨hdU, hd⟩⟩

end Scheme

#print axioms exists_conductor_of_finite
#print axioms isIntegrallyClosed_localization_of_conductor
#print axioms mem_minimalPrimes_span_of_height_eq_one
#print axioms finite_nonNormal_schemeDivisorPoint_affine
#print axioms finite_nonNormal_schemeDivisorPoint

end Pcf
