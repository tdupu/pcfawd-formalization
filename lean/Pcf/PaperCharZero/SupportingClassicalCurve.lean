/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveFormsCritical
public import Pcf.Bounding.DimensionTermination
public import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# Divisorial PCF on curves is the classical condition

`paper.tex`, Introduction: "For a rational map of `ℙ¹` this is the classical
condition that every critical point has finite forward orbit."

* `scheme_isNormalizedPCF_iff_critical_orbit_finite`: for every finite dominant
  endomorphism in the standing characteristic-zero setting, the paper's
  normalized PCF predicate holds exactly when every normalized critical divisor
  has finite forward orbit under the actual morphism.
* `normalScheme_mem_criticalDivisors_iff_one_lt_ramificationIdx`: on a normal
  scheme a critical divisor is a divisor of ramification index `> 1` of the
  actual morphism.
* `curve_isClosed_singleton_iff_coheight_eq_one`: on an integral scheme of
  dimension one the integral effective divisors are exactly the closed points.
* `normalCurve_isNormalizedPCF_iff`: for a normal integral curve, PCF holds
  exactly when every closed point of ramification index `> 1` has finite
  forward orbit.
* `projLine_isNormalizedPCF_iff` and `projLine_isNormalizedPCF_iff_jacobian`:
  the specialization to `ℙ¹ = Proj K[x₀, x₁]` and a pair of binary forms, where
  the critical closed points are the zeros of the Jacobian determinant
  `det (∂F_i/∂x_j)` (`projLine_mem_criticalDivisors_iff`).
* `projLine_ratPoint_critical_iff_derivative`: at a rational point `[t : 1]`
  with `F₁(t, 1) ≠ 0`, criticality is the vanishing of the quotient-rule
  derivative of `F₀/F₁` at `t`, via the Euler identity
  (`projHomogeneousJacobian_chart_det_ne_zero_iff`) and the fact that a
  homogeneous binary form lies in `(x₀ - t x₁)` iff it vanishes at `(t, 1)`.

The surjectivity of the manuscript is represented by the project's standing
hypotheses `IsFinite` and `IsDominant` (a finite dominant morphism is surjective).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial

namespace Pcf.PaperCharZero

/-! ### Forward orbits -/

/-- The union of the positive forward images of a finite set is finite exactly
when each element of the set has finite forward orbit. -/
theorem iUnion_iterate_image_step_finite_iff {α : Type*} (step : α → α) (S : Set α)
    (hS : S.Finite) :
    (⋃ n : ℕ, step^[n] '' (step '' S)).Finite ↔
      ∀ Q ∈ S, (Set.range fun n : ℕ => step^[n] Q).Finite := by
  constructor
  · intro h Q hQ
    apply (h.insert Q).subset
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => exact Set.mem_insert _ _
    | succ n =>
      refine Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨n, step Q, ⟨Q, hQ, rfl⟩, ?_⟩)
      exact (Function.iterate_succ_apply step n Q).symm
  · intro h
    apply (hS.biUnion h).subset
    intro x hx
    obtain ⟨n, _, ⟨Q, hQ, rfl⟩, rfl⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_biUnion hQ ⟨n + 1, Function.iterate_succ_apply step n Q⟩

/-- The divisor orbit and the underlying point orbit are the same. -/
theorem schemeDivisorMap_iterate_val {X : Scheme.{u}} (g : X ⟶ X)
    (hcodim : ∀ x : SchemeDivisorPoint X, Order.coheight (g x.1) = 1)
    (P : SchemeDivisorPoint X) (n : ℕ) :
    ((schemeDivisorMap g hcodim)^[n] P).1 = (fun x : X => g x)^[n] P.1 := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, schemeDivisorMap_val]

/-- Finiteness of a divisor orbit is finiteness of the orbit of its generic point. -/
theorem divisor_orbit_finite_iff {X : Scheme.{u}} (g : X ⟶ X)
    (hcodim : ∀ x : SchemeDivisorPoint X, Order.coheight (g x.1) = 1)
    (P : SchemeDivisorPoint X) :
    (Set.range fun n : ℕ => (schemeDivisorMap g hcodim)^[n] P).Finite ↔
      (Set.range fun n : ℕ => (fun x : X => g x)^[n] P.1).Finite := by
  have himage : (Set.range fun n : ℕ => (fun x : X => g x)^[n] P.1) =
      Subtype.val '' (Set.range fun n : ℕ => (schemeDivisorMap g hcodim)^[n] P) := by
    ext y
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, schemeDivisorMap_iterate_val g hcodim P n⟩
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (schemeDivisorMap_iterate_val g hcodim P n).symm⟩
  rw [himage, Set.finite_image_iff Subtype.val_injective.injOn]
  exact Iff.rfl

/-! ### The general characterization -/

section General

variable (k : Type u) [Field k] [CharZero k]
  {A : Scheme.{u}} (g : A ⟶ A)
  [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
  [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A]
  [CharZero (A.presheaf.stalk (genericPoint A))]
  [∀ U : A.affineOpens, Algebra k Γ(A, U)]
  [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]

/-- Divisorial PCF (`def:pcf`) holds exactly when every normalized critical
integral effective divisor has finite forward orbit under the actual morphism. -/
theorem scheme_isNormalizedPCF_iff_critical_orbit_finite :
    IsNormalizedPCF k g ↔ ∀ P ∈ schemeNormalizedCriticalDivisors k g,
      (Set.range fun n : ℕ => (fun x : A => g x)^[n] P.1).Finite := by
  rw [IsNormalizedPCF, schemeNormalizedPostcriticalSet_eq_iUnion]
  change (⋃ n : ℕ, (schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k))^[n] ''
      ((schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k)) ''
        schemeNormalizedCriticalDivisors k g)).Finite ↔ _
  rw [iUnion_iterate_image_step_finite_iff _ _ (schemeNormalizedCriticalDivisors_finite k g)]
  simp only [divisor_orbit_finite_iff]

end General

section Normal

variable (k : Type u) [Field k] [CharZero k]
  {A : Scheme.{u}} (s : A ⟶ Spec (.of k)) (g : A ⟶ A)
  [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
  [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A] [IsNormalScheme A]
  [CharZero (A.presheaf.stalk (genericPoint A))]
  [∀ U : A.affineOpens, Algebra k Γ(A, U)]
  [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]

include s in
/-- On a normal scheme, the normalized critical divisors are exactly the
divisors at which the actual morphism has ramification index greater than one. -/
theorem normalScheme_mem_criticalDivisors_iff_one_lt_ramificationIdx
    (P : SchemeDivisorPoint A) :
    P ∈ schemeNormalizedCriticalDivisors k g ↔ 1 < schemeDivisorRamificationIdx g P := by
  rw [normalScheme_mem_criticalDivisors_iff k s g P,
    ← ramificationIdx_eq_one_iff_formallyEtale_charZero k s g P]
  have hpos := schemeDivisorRamificationIdx_pos g P
  omega

include s in
/-- On a normal scheme, PCF holds exactly when every divisor of ramification
index greater than one has finite forward orbit. -/
theorem normalScheme_isNormalizedPCF_iff :
    IsNormalizedPCF k g ↔ ∀ P : SchemeDivisorPoint A, 1 < schemeDivisorRamificationIdx g P →
      (Set.range fun n : ℕ => (fun x : A => g x)^[n] P.1).Finite := by
  rw [scheme_isNormalizedPCF_iff_critical_orbit_finite]
  simp only [normalScheme_mem_criticalDivisors_iff_one_lt_ramificationIdx k s g]

end Normal

/-! ### Curves: integral effective divisors are closed points -/

section Curve

variable {A : Scheme.{u}} [IsIntegral A]

/-- On an integral scheme all of whose points have codimension at most one and
which has some codimension-one point, the codimension-one points are exactly
the closed points. -/
theorem isClosed_singleton_iff_coheight_eq_one_of_le_one
    (hdim : ∀ x : A, Order.coheight x ≤ 1) (hne : Nonempty (SchemeDivisorPoint A)) (x : A) :
    IsClosed ({x} : Set A) ↔ Order.coheight x = 1 := by
  constructor
  · intro hx
    refine le_antisymm (hdim x) ?_
    rw [Order.one_le_iff_pos, Order.coheight_pos]
    intro hmax
    obtain ⟨P⟩ := hne
    have hgen : genericPoint A ≤ x := hmax (genericPoint_specializes x)
    have hP : P.1 ≤ x := le_trans (genericPoint_specializes P.1) hgen
    have hPx : P.1 ∈ closure ({x} : Set A) :=
      specializes_iff_mem_closure.mp hP
    rw [hx.closure_eq, Set.mem_singleton_iff] at hPx
    have hc := Order.coheight_eq_zero.mpr hmax
    rw [← hPx, P.2] at hc
    exact one_ne_zero hc
  · intro hx
    rw [← closure_subset_iff_isClosed]
    intro y hy
    by_contra hne'
    have hle : y ≤ x := specializes_iff_mem_closure.mpr hy
    have hlt : y < x := lt_iff_le_not_ge.mpr ⟨hle, fun hge =>
      hne' (Set.mem_singleton_iff.mpr (Specializes.antisymm hge hle).eq)⟩
    have h := Order.coheight_add_one_le hlt
    rw [hx] at h
    have := (h.trans (hdim y))
    exact absurd this (by norm_num)

/-- On an integral scheme of dimension one the codimension-one points are
exactly the closed points. -/
theorem curve_isClosed_singleton_iff_coheight_eq_one
    (hdim : topologicalKrullDim A = 1) (x : A) :
    IsClosed ({x} : Set A) ↔ Order.coheight x = 1 := by
  have hk : Order.krullDim A = 1 :=
    (Pcf.scheme_orderKrullDim_eq_topologicalKrullDim (X := A)).trans hdim
  have hle : ∀ y : A, Order.coheight y ≤ 1 := by
    intro y
    have h := Order.coheight_le_krullDim y
    rw [hk] at h
    exact_mod_cast h
  refine isClosed_singleton_iff_coheight_eq_one_of_le_one hle ?_ x
  by_contra hempty
  have hzero : ∀ y : A, Order.coheight y = 0 := by
    intro y
    have h1 := hle y
    have h2 : Order.coheight y ≠ 1 := fun h => hempty ⟨⟨y, h⟩⟩
    rcases Order.le_one_iff.mp h1 with h | h
    · exact h
    · exact absurd h h2
  have : Order.krullDim A = 0 := by
    rw [Order.krullDim_eq_iSup_coheight]
    simp [hzero]
  rw [hk] at this
  exact one_ne_zero this

end Curve

section NormalCurve

variable (k : Type u) [Field k] [CharZero k]
  {A : Scheme.{u}} (s : A ⟶ Spec (.of k)) (g : A ⟶ A)
  [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
  [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A] [IsNormalScheme A]
  [CharZero (A.presheaf.stalk (genericPoint A))]
  [∀ U : A.affineOpens, Algebra k Γ(A, U)]
  [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]

include s in
/-- Divisorial PCF on a normal integral curve, phrased with closed points: under
the pointwise curve hypothesis (`coheight ≤ 1` everywhere, with some divisor),
PCF holds exactly when every closed point of ramification index greater than one
has finite forward orbit under the actual morphism. -/
theorem normalCurve_isNormalizedPCF_iff_of_le_one
    (hdim : ∀ x : A, Order.coheight x ≤ 1) (hne : Nonempty (SchemeDivisorPoint A)) :
    IsNormalizedPCF k g ↔ ∀ (x : A) (hx : IsClosed ({x} : Set A)),
      1 < schemeDivisorRamificationIdx g
        ⟨x, (isClosed_singleton_iff_coheight_eq_one_of_le_one hdim hne x).mp hx⟩ →
      (Set.range fun n : ℕ => (fun y : A => g y)^[n] x).Finite := by
  rw [normalScheme_isNormalizedPCF_iff k s g]
  constructor
  · intro h x hx hram
    exact h _ hram
  · intro h P hP
    exact h P.1 ((isClosed_singleton_iff_coheight_eq_one_of_le_one hdim hne P.1).mpr P.2) hP

include s in
/-- **Introduction of `paper.tex`, curve form.** For a finite surjective
endomorphism of a normal integral curve in characteristic zero, divisorial PCF
holds exactly when every critical point (closed point of ramification index
greater than one) has finite forward orbit. -/
theorem normalCurve_isNormalizedPCF_iff (hdim : topologicalKrullDim A = 1) :
    IsNormalizedPCF k g ↔ ∀ (x : A) (hx : IsClosed ({x} : Set A)),
      1 < schemeDivisorRamificationIdx g
        ⟨x, (curve_isClosed_singleton_iff_coheight_eq_one hdim x).mp hx⟩ →
      (Set.range fun n : ℕ => (fun y : A => g y)^[n] x).Finite := by
  rw [normalScheme_isNormalizedPCF_iff k s g]
  constructor
  · intro h x hx hram
    exact h _ hram
  · intro h P hP
    exact h P.1 ((curve_isClosed_singleton_iff_coheight_eq_one hdim P.1).mpr P.2) hP

end NormalCurve

/-! ### The projective line -/

section ProjectiveLine

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "lineGrade" => MvPolynomial.homogeneousSubmodule (Fin 1 ⊕ Unit) K

/-- The irrelevant maximal ideal `(x₀, x₁)` of `K[x₀, x₁]`, as a prime. -/
noncomputable def projLineIrrelevantPrime : PrimeSpectrum (MvPolynomial (Fin 1 ⊕ Unit) K) :=
  ⟨RingHom.ker (constantCoeff (σ := Fin 1 ⊕ Unit) (R := K)),
    RingHom.ker_isPrime _⟩

/-- Every relevant homogeneous prime of `K[x₀, x₁]` lies strictly inside the
irrelevant maximal ideal. -/
theorem projLine_prime_lt_irrelevant (x : AlgebraicGeometry.Proj lineGrade) :
    (⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩ : PrimeSpectrum (MvPolynomial (Fin 1 ⊕ Unit) K)) <
      projLineIrrelevantPrime := by
  have hdeg0 : ∀ f ∈ x.asHomogeneousIdeal, homogeneousComponent 0 f ∈ x.asHomogeneousIdeal := by
    intro f hf
    have h := x.asHomogeneousIdeal.isHomogeneous 0 hf
    rwa [show ((DirectSum.decompose lineGrade f 0 : _) : MvPolynomial (Fin 1 ⊕ Unit) K) =
      homogeneousComponent 0 f from decomposition.decompose'_apply f 0] at h
  have hle : x.asHomogeneousIdeal.toIdeal ≤ projLineIrrelevantPrime.asIdeal := by
    intro f hf
    change constantCoeff f = 0
    by_contra hc
    have hC := hdeg0 f hf
    rw [homogeneousComponent_zero] at hC
    have hunit : IsUnit (C (f.coeff 0) : MvPolynomial (Fin 1 ⊕ Unit) K) :=
      (isUnit_iff_ne_zero.mpr (by simpa [constantCoeff_eq] using hc)).map C
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hC hunit)
  refine lt_of_le_not_ge hle ?_
  intro hge
  apply x.not_irrelevant_le
  intro f hf
  apply hge
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hf
  change constantCoeff f = 0
  rw [show ((DirectSum.decompose lineGrade f 0 : _) : MvPolynomial (Fin 1 ⊕ Unit) K) =
      homogeneousComponent 0 f from decomposition.decompose'_apply f 0,
    homogeneousComponent_zero, C_eq_zero] at hf
  simpa [constantCoeff_eq] using hf

/-- `ℙ¹` has dimension at most one at every point. -/
theorem projLine_coheight_le_one (x : AlgebraicGeometry.Proj lineGrade) :
    Order.coheight x ≤ 1 := by
  have h := Order.coheight_le_coheight_apply_of_strictMono _
    (projPrimeOrderEmbedding (K := K) (n := 1)).strictMono x
  refine h.trans ?_
  change Order.height (⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩ :
    PrimeSpectrum (MvPolynomial (Fin 1 ⊕ Unit) K)) ≤ 1
  have hlt := Order.height_add_one_le (projLine_prime_lt_irrelevant x)
  have hm := Order.height_le_krullDim (projLineIrrelevantPrime (K := K))
  have hdim : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin 1 ⊕ Unit) K)) = 2 := by
    change ringKrullDim (MvPolynomial (Fin 1 ⊕ Unit) K) = 2
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [hdim] at hm
  have hm' : Order.height (projLineIrrelevantPrime (K := K)) ≤ 2 := WithBot.coe_le_coe.mp hm
  have h2 := hlt.trans hm'
  rw [show (2 : ℕ∞) = 1 + 1 from rfl] at h2
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h2

/-- `ℙ¹` has an integral effective divisor, the hyperplane `x₁ = 0`. -/
theorem projLine_divisor_nonempty :
    Nonempty (SchemeDivisorPoint (AlgebraicGeometry.Proj lineGrade)) := by
  have hj : (X (Sum.inl 0) : MvPolynomial (Fin 1 ⊕ Unit) K) ∉ Ideal.span {X (Sum.inr ())} :=
    not_mem_span_of_eval (Sum.elim (fun _ => 1) (fun _ => 0)) (by simp) (by simp)
  exact ⟨projLineDivisor (X (Sum.inr ())) (isHomogeneous_X K _) (X_ne_zero _) (Sum.inl 0) hj⟩

/-- On `ℙ¹`, the closed points are exactly the codimension-one points. -/
theorem projLine_isClosed_singleton_iff (x : AlgebraicGeometry.Proj lineGrade) :
    IsClosed ({x} : Set (AlgebraicGeometry.Proj lineGrade)) ↔ Order.coheight x = 1 :=
  isClosed_singleton_iff_coheight_eq_one_of_le_one projLine_coheight_le_one
    projLine_divisor_nonempty x

variable [CharZero K] (F : Fin 1 ⊕ Unit → MvPolynomial (Fin 1 ⊕ Unit) K)
  (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
  (hcover : FormsCoverProjective F)

/-- **Introduction of `paper.tex`, `ℙ¹` form, ramification version.** For the
endomorphism of `ℙ¹ = Proj K[x₀, x₁]` given by a basepoint-free pair of binary
forms of degree `d > 0`, divisorial PCF holds exactly when every closed point of
ramification index greater than one has finite forward orbit. -/
theorem projLine_isNormalizedPCF_iff :
    IsNormalizedPCF K (projFormsProjectiveSchemeMap F d hd hF hcover) ↔
      ∀ (x : AlgebraicGeometry.Proj lineGrade) (hx : IsClosed ({x} : Set _)),
        1 < schemeDivisorRamificationIdx (projFormsProjectiveSchemeMap F d hd hF hcover)
          ⟨x, (projLine_isClosed_singleton_iff x).mp hx⟩ →
        (Set.range fun n : ℕ =>
          (fun y => projFormsProjectiveSchemeMap F d hd hF hcover y)^[n] x).Finite :=
  normalCurve_isNormalizedPCF_iff_of_le_one K projStructureMap _ projLine_coheight_le_one
    projLine_divisor_nonempty

/-- **Introduction of `paper.tex`, `ℙ¹` form, Jacobian version.** Divisorial PCF
for the endomorphism of `ℙ¹` given by binary forms `(F₀, F₁)` holds exactly when
every closed point at which the Jacobian determinant `det (∂F_i/∂x_j)` vanishes
(the classical critical points) has finite forward orbit. -/
theorem projLine_isNormalizedPCF_iff_jacobian :
    IsNormalizedPCF K (projFormsProjectiveSchemeMap F d hd hF hcover) ↔
      ∀ x : AlgebraicGeometry.Proj lineGrade, IsClosed ({x} : Set _) →
        Matrix.det (fun i j => pderiv j (F i)) ∈ x.asHomogeneousIdeal →
        (Set.range fun n : ℕ =>
          (fun y => projFormsProjectiveSchemeMap F d hd hF hcover y)^[n] x).Finite := by
  rw [projLine_isNormalizedPCF_iff]
  refine forall_congr' fun x => ?_
  constructor
  · intro h hx hjac
    exact h hx ((projForms_one_lt_ramificationIdx_iff F d hd hF hcover _).mpr hjac)
  · intro h hx hram
    exact h hx ((projForms_one_lt_ramificationIdx_iff F d hd hF hcover _).mp hram)

/-- On `ℙ¹`, a closed point is a normalized critical divisor exactly when the
Jacobian determinant of the binary forms lies in its homogeneous prime. -/
theorem projLine_mem_criticalDivisors_iff (x : AlgebraicGeometry.Proj lineGrade)
    (hx : IsClosed ({x} : Set (AlgebraicGeometry.Proj lineGrade))) :
    (⟨x, (projLine_isClosed_singleton_iff x).mp hx⟩ : SchemeDivisorPoint _) ∈
        schemeNormalizedCriticalDivisors K (projFormsProjectiveSchemeMap F d hd hF hcover) ↔
      Matrix.det (fun i j => pderiv j (F i)) ∈ x.asHomogeneousIdeal :=
  projForms_mem_criticalDivisors_iff F d hd hF hcover _

/-! ### Rational points and the classical derivative -/

omit [CharZero K] in
/-- Partial derivatives of homogeneous polynomials are homogeneous. -/
theorem isHomogeneous_pderiv {σ : Type*} {p : MvPolynomial σ K} {e : ℕ}
    (hp : p.IsHomogeneous e) (i : σ) : (pderiv i p).IsHomogeneous (e - 1) := by
  classical
  rw [p.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  rw [pderiv_monomial]
  by_cases hmi : m i = 0
  · rw [hmi, Nat.cast_zero, mul_zero, monomial_zero]
    exact isHomogeneous_zero _ _ _
  · apply isHomogeneous_monomial
    have hle : Finsupp.single i 1 ≤ m :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hmi)
    have hdeg : m.degree = e := by
      have := hp (mem_support_iff.mp hm)
      rw [Finsupp.degree_eq_weight_one]
      exact this
    have hsum := map_add Finsupp.degree (m - Finsupp.single i 1) (Finsupp.single i 1)
    rw [tsub_add_cancel_of_le hle, Finsupp.degree_single] at hsum
    omega

omit [CharZero K] in
/-- The Jacobian determinant of homogeneous forms of degree `d` is homogeneous. -/
theorem isHomogeneous_jacobian_det {σ : Type*} [Fintype σ] [DecidableEq σ]
    (G : σ → MvPolynomial σ K) {e : ℕ} (hG : ∀ i, (G i).IsHomogeneous e) :
    (Matrix.det (fun i j => pderiv j (G i))).IsHomogeneous
      (∑ _i : σ, (e - 1)) := by
  change (Matrix.det (Matrix.of fun i j => pderiv j (G i))).IsHomogeneous _
  rw [Matrix.det_apply]
  simp only [Matrix.of_apply]
  refine IsHomogeneous.sum _ _ _ fun τ _ => ?_
  rw [Units.smul_def]
  apply (mem_homogeneousSubmodule _ _).mp
  apply zsmul_mem
  apply (mem_homogeneousSubmodule _ _).mpr
  exact IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_pderiv (hG _) i

omit [CharZero K] in
/-- The linear form `x₀ - t x₁` cutting out the rational point `[t : 1]`. -/
theorem projLine_ratLine_isHomogeneous (t : K) :
    ((X (Sum.inl 0) - C t * X (Sum.inr ())) : MvPolynomial (Fin 1 ⊕ Unit) K).IsHomogeneous 1 :=
  (isHomogeneous_X K _).sub (by
    have := (isHomogeneous_C (Fin 1 ⊕ Unit) t).mul (isHomogeneous_X K (Sum.inr ()))
    rwa [zero_add] at this)

/-- The affine coordinate vector `(t, 1)`. -/
def projLineChartVector (t : K) : Fin 1 ⊕ Unit → K := Sum.elim (fun _ => t) (fun _ => 1)

omit [CharZero K] in
theorem projLine_ratLine_ne_zero (t : K) :
    ((X (Sum.inl 0) - C t * X (Sum.inr ())) : MvPolynomial (Fin 1 ⊕ Unit) K) ≠ 0 := by
  intro h
  have := congrArg (eval (Sum.elim (fun _ => (1 : K)) (fun _ => 0))) h
  simp at this

omit [CharZero K] in
theorem projLine_ratLine_X_notMem (t : K) :
    (X (Sum.inr ()) : MvPolynomial (Fin 1 ⊕ Unit) K) ∉
      Ideal.span {X (Sum.inl 0) - C t * X (Sum.inr ())} :=
  not_mem_span_of_eval (projLineChartVector t) (by simp [projLineChartVector])
    (by simp [projLineChartVector])

/-- The rational point `[t : 1]` of `ℙ¹`, as the homogeneous prime `(x₀ - t x₁)`. -/
noncomputable def projLineRatPoint (t : K) : AlgebraicGeometry.Proj lineGrade :=
  projLinePoint _ (projLine_ratLine_isHomogeneous t) (projLine_ratLine_ne_zero t) (Sum.inr ())
    (projLine_ratLine_X_notMem t)

omit [CharZero K] in
theorem projLineRatPoint_coheight (t : K) : Order.coheight (projLineRatPoint t) = 1 :=
  projLinePoint_coheight _ _ _ _ _

omit [CharZero K] in
/-- The rational point `[t : 1]` is a closed point. -/
theorem projLineRatPoint_isClosed (t : K) :
    IsClosed ({projLineRatPoint t} : Set (AlgebraicGeometry.Proj lineGrade)) :=
  (projLine_isClosed_singleton_iff _).mpr (projLineRatPoint_coheight t)

omit [CharZero K] in
/-- A homogeneous binary form lies in the prime of `[t : 1]` exactly when it
vanishes at `(t, 1)`. -/
theorem mem_projLineRatPoint_iff (t : K) {P : MvPolynomial (Fin 1 ⊕ Unit) K} {e : ℕ}
    (hP : P.IsHomogeneous e) :
    P ∈ (projLineRatPoint t).asHomogeneousIdeal ↔ eval (projLineChartVector t) P = 0 := by
  let v := projLineChartVector t
  constructor
  · intro h
    obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton'.mp h
    simp [projLineChartVector]
  · intro h
    let I : Ideal (MvPolynomial (Fin 1 ⊕ Unit) K) := RingHom.ker (eval v)
    have hI : I.IsPrime := RingHom.ker_isPrime _
    have hcorePrime := Ideal.IsPrime.homogeneousCore (𝒜 := lineGrade) hI
    have hXr : (X (Sum.inr ()) : MvPolynomial (Fin 1 ⊕ Unit) K) ∉ I.homogeneousCore lineGrade := by
      intro hx
      have := Ideal.toIdeal_homogeneousCore_le lineGrade I hx
      simp [I, v, projLineChartVector] at this
    let y : ProjectiveSpectrum lineGrade :=
      ⟨I.homogeneousCore lineGrade, hcorePrime, fun hle => hXr (hle
        (HomogeneousIdeal.mem_irrelevant_of_mem lineGrade Nat.zero_lt_one
          (isHomogeneous_X K (Sum.inr ()))))⟩
    have hℓ : (X (Sum.inl 0) - C t * X (Sum.inr ()) : MvPolynomial (Fin 1 ⊕ Unit) K) ∈
        I.homogeneousCore lineGrade :=
      Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨1, projLine_ratLine_isHomogeneous t⟩
        (by simp [I, v, projLineChartVector])
    let z : ProjectiveSpectrum lineGrade := projLineRatPoint t
    have hy : y ∈ closure ({z} : Set (ProjectiveSpectrum lineGrade)) := by
      rw [← ProjectiveSpectrum.le_iff_mem_closure]
      change Ideal.span {_} ≤ (I.homogeneousCore lineGrade).toIdeal
      exact (Ideal.span_singleton_le_iff_mem _).mpr hℓ
    have hclosed : IsClosed ({z} : Set (ProjectiveSpectrum lineGrade)) :=
      projLineRatPoint_isClosed (K := K) t
    rw [hclosed.closure_eq] at hy
    have hyz : y = z := hy
    have hPcore : P ∈ y.asHomogeneousIdeal :=
      Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨e, hP⟩ h
    rw [hyz] at hPcore
    exact hPcore


/-- **The classical derivative criterion on `ℙ¹`.** In the affine chart
`x₁ = 1`, at a rational point `[t : 1]` with `F₁(t, 1) ≠ 0`, the point is
critical (ramification index greater than one) exactly when the derivative of
`f = F₀/F₁` vanishes at `t`, written by the quotient rule
`(∂₀F₀ · F₁ - F₀ · ∂₀F₁) / F₁²` evaluated at `(t, 1)`. -/
theorem projLine_ratPoint_critical_iff_derivative (t : K)
    (hF1 : eval (projLineChartVector t) (F (Sum.inr ())) ≠ 0) :
    1 < schemeDivisorRamificationIdx (projFormsProjectiveSchemeMap F d hd hF hcover)
        ⟨projLineRatPoint t, projLineRatPoint_coheight t⟩ ↔
      (eval (projLineChartVector t) (pderiv (Sum.inl 0) (F (Sum.inl 0))) *
          eval (projLineChartVector t) (F (Sum.inr ())) -
        eval (projLineChartVector t) (F (Sum.inl 0)) *
          eval (projLineChartVector t) (pderiv (Sum.inl 0) (F (Sum.inr ())))) /
        (eval (projLineChartVector t) (F (Sum.inr ()))) ^ 2 = 0 := by
  refine (projForms_one_lt_ramificationIdx_iff F d hd hF hcover
    ⟨projLineRatPoint t, projLineRatPoint_coheight t⟩).trans ?_
  rw [mem_projLineRatPoint_iff t (isHomogeneous_jacobian_det F hF)]
  have h := projHomogeneousJacobian_chart_det_ne_zero_iff F d hF
    (Nat.cast_ne_zero.mpr hd.ne') (projLineChartVector t) rfl hF1
  rw [← not_iff_not]
  refine h.trans ?_
  exact Iff.of_eq (congrArg (· ≠ 0) (Matrix.det_fin_one _))

end ProjectiveLine

#print axioms iUnion_iterate_image_step_finite_iff
#print axioms schemeDivisorMap_iterate_val
#print axioms divisor_orbit_finite_iff
#print axioms scheme_isNormalizedPCF_iff_critical_orbit_finite
#print axioms normalScheme_mem_criticalDivisors_iff_one_lt_ramificationIdx
#print axioms normalScheme_isNormalizedPCF_iff
#print axioms isClosed_singleton_iff_coheight_eq_one_of_le_one
#print axioms curve_isClosed_singleton_iff_coheight_eq_one
#print axioms normalCurve_isNormalizedPCF_iff_of_le_one
#print axioms normalCurve_isNormalizedPCF_iff
#print axioms projLineIrrelevantPrime
#print axioms projLine_prime_lt_irrelevant
#print axioms projLine_coheight_le_one
#print axioms projLine_divisor_nonempty
#print axioms projLine_isClosed_singleton_iff
#print axioms projLine_isNormalizedPCF_iff
#print axioms projLine_isNormalizedPCF_iff_jacobian
#print axioms projLine_mem_criticalDivisors_iff
#print axioms isHomogeneous_pderiv
#print axioms isHomogeneous_jacobian_det
#print axioms projLine_ratLine_isHomogeneous
#print axioms projLineChartVector
#print axioms projLine_ratLine_ne_zero
#print axioms projLine_ratLine_X_notMem
#print axioms projLineRatPoint
#print axioms projLineRatPoint_coheight
#print axioms projLineRatPoint_isClosed
#print axioms mem_projLineRatPoint_iff
#print axioms projLine_ratPoint_critical_iff_derivative

end Pcf.PaperCharZero
