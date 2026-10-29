/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.BasilicaProjectiveWeightedPCF
public import Pcf.Bounding.PaperPJacobianGlobalEtale
public import Pcf.Bounding.PaperPProjectiveFinite
public import Pcf.Bounding.PaperPProjectiveDominant

/-!
# The return of `paper-p.tex`, Example `ex:monodromy-loss`, as a scheme morphism

The displayed return `g(y) = -i (y⁴ + 1) / y³` homogenizes, in the coordinate
`y = u/v`, to the degree-four forms `[-i (u⁴ + v⁴) : u³ v]`. These have no
common projective zero, so they define an actual morphism `g : ℙ¹ ⟶ ℙ¹` of
the projective-line scheme `Proj k[u,v]`.

The projective line, its rational scheme points `[a:b]`, the points `0 = [0:1]`
and `∞ = [1:0]` and their coordinate characterizations are the map-independent
declarations of `BasilicaProjectiveScheme`, reused here.

This module proves the scheme-point formula, finiteness, dominance and
surjectivity, and the exact all-point étale locus in characteristic `3`:
the homogeneous Jacobian determinant is `-i u⁶`, so `g` is étale exactly away
from the single scheme point `0`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
namespace Pcf.Examples.PaperP.MonodromyLossReturn
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Index := BasilicaProjectiveScheme.Index
abbrev Coordinates (k : Type*) [Field k] := BasilicaProjectiveScheme.Coordinates k
abbrev grading (k : Type*) [Field k] := BasilicaProjectiveScheme.grading k

variable (k : Type*) [Field k] (i : k)
local notation "u" => (X (Sum.inl 0) : Coordinates k)
local notation "v" => (X (Sum.inr ()) : Coordinates k)

/-- The homogenized return `[-i (u⁴ + v⁴) : u³ v]`. -/
noncomputable def forms : Index → Coordinates k
  | Sum.inl _ => C (-i) * (u ^ 4 + v ^ 4)
  | Sum.inr _ => u ^ 3 * v

theorem forms_inl : forms k i (Sum.inl 0) = C (-i) * (u ^ 4 + v ^ 4) := rfl
theorem forms_inr : forms k i (Sum.inr ()) = u ^ 3 * v := rfl

theorem forms_homogeneous (j : Index) : (forms k i j).IsHomogeneous 4 := by
  have hu : (u).IsHomogeneous 1 := isHomogeneous_X k _
  have hv : (v).IsHomogeneous 1 := isHomogeneous_X k _
  rcases j with _ | _
  · have h := (isHomogeneous_C Index (-i)).mul ((hu.pow 4).add (hv.pow 4))
    simpa [forms] using h
  · have h := (hu.pow 3).mul hv
    simpa [forms] using h

variable {k i}

theorem neg_i_mul_i (hi : i ^ 2 = -1) : -i * i = 1 := by
  rw [neg_mul, ← pow_two, hi, neg_neg]

theorem i_ne_zero (hi : i ^ 2 = -1) : i ≠ 0 := by
  intro h
  have := neg_i_mul_i hi
  rw [h, mul_zero] at this
  exact zero_ne_one this

variable (k)

/-- The two forms have no common projective zero. -/
theorem forms_cover (hi : i ^ 2 = -1) : Pcf.PaperPFormsCoverProjective (forms k i) := by
  apply (Pcf.paperPIrrelevant_le_coordinateIdeal (K := k) (n := 1)).trans
  change Ideal.span (Set.range (X : Index → Coordinates k)) ≤
    (Ideal.span (Set.range (forms k i))).radical
  rw [Ideal.span_le, Set.range_subset_iff]
  intro j
  apply Ideal.mem_radical_iff.mpr
  refine ⟨7, ?_⟩
  have h0 : forms k i (Sum.inl 0) ∈ Ideal.span (Set.range (forms k i)) :=
    Ideal.subset_span ⟨Sum.inl 0, rfl⟩
  have h1 : forms k i (Sum.inr ()) ∈ Ideal.span (Set.range (forms k i)) :=
    Ideal.subset_span ⟨Sum.inr (), rfl⟩
  have hsum : u ^ 4 + v ^ 4 ∈ Ideal.span (Set.range (forms k i)) := by
    have h := Ideal.mul_mem_left _ (C i) h0
    rw [forms_inl, ← mul_assoc, ← map_mul, mul_comm i, neg_i_mul_i hi, map_one, one_mul] at h
    exact h
  rw [forms_inr] at h1
  rcases j with j | j
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have h := Ideal.sub_mem _ (Ideal.mul_mem_left _ (u ^ 3) hsum)
      (Ideal.mul_mem_left _ (v ^ 3) h1)
    convert h using 1
    ring
  · have h := Ideal.sub_mem _ (Ideal.mul_mem_left _ (v ^ 3) hsum)
      (Ideal.mul_mem_left _ (u * v ^ 2) h1)
    convert h using 1
    ring

variable (i)

/-- **The actual degree-four return `g : ℙ¹ ⟶ ℙ¹`** of `ex:monodromy-loss`. -/
noncomputable def schemeMap (hi : i ^ 2 = -1) :
    Proj (grading k) ⟶ Proj (grading k) :=
  Pcf.paperPFormsProjectiveSchemeMap (forms k i) 4 (by decide) (forms_homogeneous k i)
    (forms_cover k hi)

variable {i} (hi : i ^ 2 = -1)
include hi

/-! ### Scheme points -/

open BasilicaProjectiveScheme in
theorem output_nonzero (a b : k) (h : a ≠ 0 ∨ b ≠ 0) :
    -i * (a ^ 4 + b ^ 4) ≠ 0 ∨ a ^ 3 * b ≠ 0 := by
  have hi0 := neg_ne_zero.mpr (i_ne_zero hi)
  by_cases ha : a = 0
  · left
    have hb : b ≠ 0 := h.resolve_left (not_not.mpr ha)
    simpa [ha] using mul_ne_zero hi0 (pow_ne_zero 4 hb)
  · by_cases hb : b = 0
    · left
      simpa [hb] using mul_ne_zero hi0 (pow_ne_zero 4 ha)
    · exact Or.inr (mul_ne_zero (pow_ne_zero 3 ha) hb)

omit hi in
theorem pointForms_comp_forms (a b : k) :
    (aeval (BasilicaProjectiveScheme.pointForms k a b)).comp (aeval (forms k i)) =
      (MvPolynomial.expand 4).comp
        (aeval (BasilicaProjectiveScheme.pointForms k (-i * (a ^ 4 + b ^ 4)) (a ^ 3 * b))) := by
  apply MvPolynomial.algHom_ext
  intro j
  rcases j with j | j <;>
    simp [BasilicaProjectiveScheme.pointForms, forms, MvPolynomial.expand_X] <;> ring

/-- The global scheme map obeys the displayed homogeneous coordinate formula. -/
theorem schemeMap_point (a b : k) (h : a ≠ 0 ∨ b ≠ 0) :
    schemeMap k i hi (BasilicaProjectiveScheme.point k a b h) =
      BasilicaProjectiveScheme.point k (-i * (a ^ 4 + b ^ 4)) (a ^ 3 * b)
        (output_nonzero k hi a b h) := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro P
  change aeval (BasilicaProjectiveScheme.pointForms k a b) (aeval (forms k i) P) = 0 ↔
    aeval (BasilicaProjectiveScheme.pointForms k (-i * (a ^ 4 + b ^ 4)) (a ^ 3 * b)) P = 0
  rw [← AlgHom.comp_apply, pointForms_comp_forms, AlgHom.comp_apply]
  exact MvPolynomial.expand_eq_zero (by decide : 0 < 4)

omit hi in
theorem point_congr {k : Type*} [Field k] {a b a' b' : k} (ha : a = a') (hb : b = b')
    (h : a ≠ 0 ∨ b ≠ 0) (h' : a' ≠ 0 ∨ b' ≠ 0) :
    BasilicaProjectiveScheme.point k a b h = BasilicaProjectiveScheme.point k a' b' h' := by
  subst ha hb
  rfl

omit hi in
/-- Rational projective scheme points are invariant under nonzero scaling. -/
theorem point_smul (c a b : k) (hc : c ≠ 0) (h : a ≠ 0 ∨ b ≠ 0)
    (h' : c * a ≠ 0 ∨ c * b ≠ 0) :
    BasilicaProjectiveScheme.point k (c * a) (c * b) h' =
      BasilicaProjectiveScheme.point k a b h := by
  let σ : Coordinates k →ₐ[k] Coordinates k := aeval fun j => C c * X j
  let τ : Coordinates k →ₐ[k] Coordinates k := aeval fun j => C c⁻¹ * X j
  have hστ : τ.comp σ = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [σ, τ, AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
    rw [map_mul, aeval_X, aeval_C, MvPolynomial.algebraMap_eq, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hc, map_one, one_mul]
  have hσinj : Function.Injective σ := by
    intro x y hxy
    have := congrArg τ hxy
    simpa only [← AlgHom.comp_apply, hστ, AlgHom.id_apply] using this
  have hcomp : σ.comp (aeval (BasilicaProjectiveScheme.pointForms k a b)) =
      aeval (BasilicaProjectiveScheme.pointForms k (c * a) (c * b)) := by
    apply MvPolynomial.algHom_ext
    intro j
    rcases j with j | j <;>
      simp [σ, BasilicaProjectiveScheme.pointForms] <;> ring
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro P
  change aeval (BasilicaProjectiveScheme.pointForms k (c * a) (c * b)) P = 0 ↔
    aeval (BasilicaProjectiveScheme.pointForms k a b) P = 0
  rw [← hcomp, AlgHom.comp_apply]
  constructor
  · intro h0
    exact hσinj (h0.trans (map_zero σ).symm)
  · intro h0
    rw [h0, map_zero]

/-- The scheme point `0 = [0:1]` maps to `∞`. -/
theorem zero_to_infinity :
    schemeMap k i hi (BasilicaProjectiveScheme.zero k) = BasilicaProjectiveScheme.infinity k := by
  unfold BasilicaProjectiveScheme.zero BasilicaProjectiveScheme.infinity
  rw [schemeMap_point]
  have hi0 : -i ≠ 0 := neg_ne_zero.mpr (i_ne_zero hi)
  rw [point_congr (a' := -i * 1) (b' := -i * 0) (by ring) (by ring) _
    (Or.inl (by simpa using hi0))]
  exact point_smul k (-i) 1 0 hi0 _ _

/-- The scheme point `∞ = [1:0]` is fixed. -/
theorem infinity_fixed :
    schemeMap k i hi (BasilicaProjectiveScheme.infinity k) =
      BasilicaProjectiveScheme.infinity k := by
  unfold BasilicaProjectiveScheme.infinity
  rw [schemeMap_point]
  have hi0 : -i ≠ 0 := neg_ne_zero.mpr (i_ne_zero hi)
  rw [point_congr (a' := -i * 1) (b' := -i * 0) (by ring) (by ring) _
    (Or.inl (by simpa using hi0))]
  exact point_smul k (-i) 1 0 hi0 _ _

/-- Positive iterates of the actual non-étale locus. -/
def nonEtalePostorbit : Set (Proj (grading k)) :=
  {q | ∃ p ∈ Pcf.schemeNonEtaleLocus (schemeMap k i hi),
    ∃ n : ℕ, 0 < n ∧ q = (schemeMap k i hi)^[n] p}

theorem iterate_infinity (n : ℕ) :
    (schemeMap k i hi)^[n] (BasilicaProjectiveScheme.infinity k) =
      BasilicaProjectiveScheme.infinity k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, infinity_fixed]

/-! ### Finiteness, dominance and surjectivity -/

instance schemeMap_finite : IsFinite (schemeMap k i hi) := by
  unfold schemeMap
  infer_instance

instance schemeMap_dominant : IsDominant (schemeMap k i hi) := by
  unfold schemeMap
  infer_instance

/-- The actual return is surjective on all scheme points. -/
instance schemeMap_surjective : Surjective (schemeMap k i hi) := by
  rw [surjective_iff, ← Set.range_eq_univ]
  rw [← (schemeMap k i hi).isClosedMap.isClosed_range.closure_eq]
  exact (schemeMap k i hi).denseRange.closure_range

/-! ### The Jacobian and the étale locus in characteristic three -/

variable [CharP k 3]

omit hi in
theorem three_eq_zero : (3 : Coordinates k) = 0 := by
  have : C (3 : k) = (0 : Coordinates k) := by
    rw [show (3 : k) = ((3 : ℕ) : k) by norm_num, CharP.cast_eq_zero, map_zero]
  rwa [map_ofNat] at this

omit hi in
theorem four_eq_one : (4 : Coordinates k) = 1 := by
  have h := three_eq_zero k
  calc (4 : Coordinates k) = 3 + 1 := by norm_num
    _ = 1 := by rw [h, zero_add]

omit hi in
/-- The homogeneous Jacobian determinant is `-i u⁶` in characteristic three. -/
theorem jacobian_det :
    Matrix.det (fun a b => pderiv b (forms k i a)) = C (-i) * u ^ 6 := by
  have h3 := three_eq_zero k
  have h4 := four_eq_one k
  have hM : (fun a b => pderiv b (forms k i a)) =
      Matrix.fromBlocks (fun _ _ : Fin 1 => C (-i) * u ^ 3)
        (fun (_ : Fin 1) (_ : Unit) => C (-i) * v ^ 3) 0 (fun _ _ : Unit => u ^ 3) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · have ha : a = 0 := Subsingleton.elim _ _
      have hb : b = 0 := Subsingleton.elim _ _
      subst ha hb
      simp [forms, pderiv_X, Matrix.fromBlocks, h4]
    · have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      simp [forms, pderiv_X, Matrix.fromBlocks, h4]
    · have hb : b = 0 := Subsingleton.elim _ _
      subst hb
      simp [forms, pderiv_X, Matrix.fromBlocks, h3]
    · simp [forms, pderiv_X, Matrix.fromBlocks]
  rw [hM, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique, Matrix.det_unique]
  ring

theorem jacobian_mem_iff (p : Proj (grading k)) :
    Matrix.det (fun a b => pderiv b (forms k i a)) ∈ p.asHomogeneousIdeal ↔
      p = BasilicaProjectiveScheme.zero k := by
  let : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
  have hc : C (-i) ∉ p.asHomogeneousIdeal.toIdeal := by
    apply Ideal.notMem_of_isUnit
    exact (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (i_ne_zero hi))).map
      (C : k →+* Coordinates k)
  rw [jacobian_det]
  change C (-i) * u ^ 6 ∈ p.asHomogeneousIdeal.toIdeal ↔ _
  rw [p.isPrime.mul_mem_iff_mem_or_mem]
  simp only [hc, false_or]
  rw [p.isPrime.pow_mem_iff_mem 6 (by decide)]
  exact BasilicaProjectiveScheme.firstCoordinate_mem_iff k p

omit hi in
theorem four_ne_zero : ((4 : ℕ) : k) ≠ 0 := by
  have h : ((4 : ℕ) : k) = 1 := by
    rw [show (4 : ℕ) = 3 + 1 by rfl, Nat.cast_add, CharP.cast_eq_zero, zero_add, Nat.cast_one]
  rw [h]
  exact one_ne_zero

/-- **The actual global étale locus.** In characteristic three `g` is étale at
every scheme point except `0`; in particular it is étale at `∞`. -/
theorem etaleAt_iff (p : Proj (grading k)) :
    Pcf.Stacks.IsStacksEtaleAt (schemeMap k i hi) p ↔ p ≠ BasilicaProjectiveScheme.zero k := by
  unfold schemeMap
  rw [Pcf.paperPFormsProjective_etaleAt_iff (forms k i) 4 (by decide)
    (forms_homogeneous k i) (forms_cover k hi) (four_ne_zero k), jacobian_mem_iff k hi p]

/-- The actual full non-étale stalk locus is the single scheme point `0`. -/
theorem nonEtaleLocus_eq :
    Pcf.schemeNonEtaleLocus (schemeMap k i hi) = {BasilicaProjectiveScheme.zero k} := by
  unfold schemeMap
  rw [Pcf.paperPFormsProjective_nonEtaleLocus_eq_zeroLocus (forms k i) 4 (by decide)
    (forms_homogeneous k i) (forms_cover k hi) (four_ne_zero k)]
  ext p
  change ({Matrix.det (fun a b => pderiv b (forms k i a))} : Set (Coordinates k)) ⊆
    (p.asHomogeneousIdeal : Set (Coordinates k)) ↔ p = BasilicaProjectiveScheme.zero k
  rw [Set.singleton_subset_iff]
  exact jacobian_mem_iff k hi p

/-- The stalk map at every point other than `0` is formally étale. -/
theorem stalk_formallyEtale_of_ne (p : Proj (grading k))
    (hp : p ≠ BasilicaProjectiveScheme.zero k) :
    ((schemeMap k i hi).stalkMap p).hom.FormallyEtale :=
  (Pcf.paperPFormsProjective_stalk_formallyEtale_iff (forms k i) 4 (by decide)
    (forms_homogeneous k i) (forms_cover k hi) (four_ne_zero k) p).mpr
    (by rw [jacobian_mem_iff k hi p]; exact hp)

/-- **The orbit `0 ↦ ∞ ↦ ∞`.** The positive orbit of the non-étale locus is `{∞}`. -/
theorem nonEtalePostorbit_eq :
    nonEtalePostorbit k hi = {BasilicaProjectiveScheme.infinity k} := by
  unfold nonEtalePostorbit
  rw [nonEtaleLocus_eq k hi]
  ext q
  constructor
  · rintro ⟨p, rfl, n, hn, rfl⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
    rw [Nat.zero_add, Function.iterate_succ_apply, zero_to_infinity, iterate_infinity]
    rfl
  · rintro rfl
    exact ⟨_, rfl, 1, Nat.one_pos, (zero_to_infinity k hi).symm⟩

theorem nonEtalePostorbit_finite : (nonEtalePostorbit k hi).Finite := by
  rw [nonEtalePostorbit_eq]
  exact Set.finite_singleton _

#print axioms forms_cover
#print axioms schemeMap_point
#print axioms zero_to_infinity
#print axioms infinity_fixed
#print axioms schemeMap_finite
#print axioms schemeMap_surjective
#print axioms jacobian_det
#print axioms etaleAt_iff
#print axioms nonEtaleLocus_eq
#print axioms nonEtalePostorbit_eq

end Pcf.Examples.PaperP.MonodromyLossReturn
