/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.SchemeExtraction
import Mathlib.RingTheory.Finiteness.Quotient

/-!
# Codimension of a divisor on an integral divisor

Noether normalization reduces the affine codimension calculation to a polynomial
ring. Height preservation for finite extensions applies both before and after
quotienting by the first prime. Its contraction to the polynomial ring has height
one and is therefore principal, so Krull's height theorem supplies the upper bound.
-/

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

/-- A prime strictly above a height-one prime has height at least two. -/
theorem two_le_height_of_height_one_lt
    {R : Type*} [CommRing R] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (hp : p.height = 1) (hpq : p < q) : 2 ≤ q.height := by
  simpa only [hp, show (1 : ℕ∞) + 1 = 2 by norm_num] using
    Ideal.height_add_one_le_of_lt_of_isPrime hpq

/-- A two-step divisor flag in a domain of finite type over a field has height two.
The ambient ring need not be normal or factorial. -/
theorem height_eq_two_of_divisorFlag_finiteType
    (k : Type u) [Field k] {R : Type v} [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    (hpq : p ≤ q) (hp : p.height = 1)
    (hq : (q.map (Ideal.Quotient.mk p)).height = 1) : q.height = 2 := by
  have hpq' : p < q := by
    refine lt_of_le_of_ne hpq ?_
    intro heq
    subst q
    simp at hq
  refine le_antisymm ?_ (two_le_height_of_height_one_lt hp hpq')
  obtain ⟨n, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let P := MvPolynomial (Fin n) k
  let : Algebra P R := φ.toRingHom.toAlgebra
  have : Module.Finite P R := hfin
  have : FaithfulSMul P R := (faithfulSMul_iff_algebraMap_injective P R).mpr hinj
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let p₀ : Ideal P := p.under P
  let q₀ : Ideal P := q.under P
  have : p₀.IsPrime := Ideal.IsPrime.under P p
  have : q₀.IsPrime := Ideal.IsPrime.under P q
  have hp₀ : p₀.height = 1 := (height_under_eq_of_finite_of_normal p).trans hp
  have hq₀ : q₀.height = q.height := height_under_eq_of_finite_of_normal q
  have hle₀ : p₀ ≤ q₀ := Ideal.comap_mono hpq
  have : FaithfulSMul (P ⧸ p₀) (R ⧸ p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  let qbar : Ideal (R ⧸ p) := q.map (Ideal.Quotient.mk p)
  have : qbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have hcontract : qbar.under (P ⧸ p₀) = q₀.map (Ideal.Quotient.mk p₀) := by
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [Ideal.comap_map_mk hle₀]
    change (qbar.comap (algebraMap (P ⧸ p₀) (R ⧸ p))).comap
      (Ideal.Quotient.mk p₀) = q₀
    rw [Ideal.comap_comap]
    change (qbar.comap (Ideal.Quotient.mk p)).comap (algebraMap P R) = q₀
    rw [Ideal.comap_map_mk hpq]
  have hquot : (q₀.map (Ideal.Quotient.mk p₀)).height = 1 := by
    rw [← hcontract]
    exact (height_under_eq_of_finite_of_finiteType k qbar).trans hq
  obtain ⟨a, ha⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hp₀
  change p₀ = Ideal.span {a} at ha
  have hamem : a ∈ q₀ := hle₀ (ha ▸ Ideal.subset_span (Set.mem_singleton a))
  have hbound := Ideal.height_le_height_add_one_of_mem hamem
  rw [← ha, hquot, hq₀] at hbound
  simpa only [show (1 : ℕ∞) + 1 = 2 by norm_num] using hbound

/-- The height of a prime in a quotient chart is the codimension of its actual
closed-subscheme point. -/
theorem Scheme.IdealSheafData.quotientPoint_height
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (U : X.Opens)) :
    (I.quotientPoint U x hx).asIdeal.height = Order.coheight x := by
  let : Algebra (Γ(X, U) ⧸ I.ideal U) (I.subscheme.presheaf.stalk x) :=
    I.quotientStalkAlgebra U x hx
  have : IsLocalization.AtPrime (I.subscheme.presheaf.stalk x)
      (I.quotientPoint U x hx).asIdeal := I.quotientStalk_isLocalization U x hx
  exact WithBot.coe_eq_coe.mp
    ((IsLocalization.AtPrime.ringKrullDim_eq_height
      (I.quotientPoint U x hx).asIdeal (I.subscheme.presheaf.stalk x)).symm.trans
      (AlgebraicGeometry.ringKrullDim_stalk_eq_coheight x))

/-- A divisor on the reduced closure of an ambient divisor has codimension two
in an integral scheme whenever an ambient affine chart is of finite type over a
field. -/
theorem SchemeDivisorPoint.closureDivisor_coheight_of_mem_affine_finiteType
    {X : Scheme.{u}} [IsIntegral X] (k : Type v) [Field k]
    (A : SchemeDivisorPoint X)
    (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (U : X.affineOpens) [Algebra k Γ(X, U)] [Algebra.FiniteType k Γ(X, U)]
    (hQU : (pointClosureIdealSheaf A.1).subschemeι Q.1 ∈ (U : X.Opens)) :
    Order.coheight ((pointClosureIdealSheaf A.1).subschemeι Q.1) = 2 := by
  let I := pointClosureIdealSheaf A.1
  have hclosure : I.subschemeι Q.1 ∈ closure ({A.1} : Set X) := by
    have h := Set.mem_range_self (f := I.subschemeι) Q.1
    rw [Scheme.IdealSheafData.range_subschemeι] at h
    simpa [I, pointClosureIdealSheaf] using h
  have hAU : A.1 ∈ (U : X.Opens) :=
    (specializes_iff_mem_closure.mpr hclosure).mem_open U.1.isOpen hQU
  have : Nonempty (U : X.Opens) := ⟨⟨A.1, hAU⟩⟩
  have : (I.ideal U).IsPrime := pointClosureIdealSheaf_ideal_isPrime A.1 U hAU
  have : (ambientPrimeOfQuotientPoint I U Q.1 hQU).IsPrime :=
    ambientPrimeOfQuotientPoint_isPrime I U Q.1 hQU
  have hheight : (ambientPrimeOfQuotientPoint I U Q.1 hQU).height = 2 := by
    apply height_eq_two_of_divisorFlag_finiteType k (I.ideal U)
      (ambientPrimeOfQuotientPoint I U Q.1 hQU)
      (ideal_le_ambientPrimeOfQuotientPoint I U Q.1 hQU)
      (pointClosureIdealSheaf_ideal_height A U hAU)
    exact (congrArg Ideal.height (map_ambientPrimeOfQuotientPoint I U Q.1 hQU)).trans
      ((Scheme.IdealSheafData.quotientPoint_height I U Q.1 hQU).trans Q.2)
  have hdim := ringKrullDim_ambientPrimeLocalization I U Q.1 hQU
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (ambientPrimeOfQuotientPoint I U Q.1 hQU), hheight] at hdim
  exact WithBot.coe_eq_coe.mp hdim.symm

/-- In an integral scheme locally of finite type over a field, a divisor on the
reduced closure of an ambient divisor has codimension two in the ambient scheme. -/
theorem SchemeDivisorPoint.closureDivisor_coheight_of_finiteType
    {X : Scheme.{u}} [IsIntegral X] (k : Type u) [Field k]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (A : SchemeDivisorPoint X)
    (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme) :
    Order.coheight ((pointClosureIdealSheaf A.1).subschemeι Q.1) = 2 := by
  obtain ⟨V, hV, hQV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show (pointClosureIdealSheaf A.1).subschemeι Q.1 ∈ (⊤ : X.Opens) by trivial)
  let U : X.affineOpens := ⟨V, hV⟩
  let φ : k →+* Γ(X, U) :=
    (s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Algebra k Γ(X, U) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := by
    apply RingHom.finiteType_algebraMap.mp
    change φ.FiniteType
    exact (s.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType
  exact A.closureDivisor_coheight_of_mem_affine_finiteType k Q U hQV

#print axioms two_le_height_of_height_one_lt
#print axioms height_eq_two_of_divisorFlag_finiteType
#print axioms Scheme.IdealSheafData.quotientPoint_height
#print axioms SchemeDivisorPoint.closureDivisor_coheight_of_mem_affine_finiteType
#print axioms SchemeDivisorPoint.closureDivisor_coheight_of_finiteType

end

end Pcf
