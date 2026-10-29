/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.WildGlobalEtale
public import Pcf.Bounding.PaperPIteration
public import Pcf.Bounding.PaperPProjectiveNormal
public import Pcf.Bounding.TheoremADivisors
public import Mathlib.Algebra.MvPolynomial.Expand

/-!
# Ambient generic separability and normalized weighted PCF for the wild example

For `latex/paper-p.tex`, Example `ex:wild`, in characteristic `p` the actual
global projective-plane morphism is generically separable. The generic points
of the lines `H₀ = V(x)` and `H₂ = V(z)` are actual codimension-one scheme
points; they are exactly the normalized weighted critical generic points, and
each is fixed by the map. Consequently the normalized weighted critical,
branch and postcritical generic-point sets all equal `{H₀, H₂}`, the closed
critical and branch loci equal `H₀ ∪ H₂`, and the manuscript's normalized
PCF predicates hold for the actual map over `k`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace Pcf.Examples.PaperP.Wild
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type*) [Field k] (p : ℕ) (c : k)

/-- The scheme specialization order on projective points is reverse ideal inclusion. -/
theorem point_le_iff (a b : Proj (grading k)) :
    a ≤ b ↔ b.asHomogeneousIdeal ≤ a.asHomogeneousIdeal := by
  rw [Scheme.le_iff_specializes, specializes_iff_mem_closure]
  exact (ProjectiveSpectrum.le_iff_mem_closure (𝒜 := grading k) b a).symm

/-- The homogeneous principal ideal of one coordinate. -/
noncomputable def coordinateIdeal (i : Index) : HomogeneousIdeal (grading k) :=
  ⟨Ideal.span {X i}, Ideal.homogeneous_span _ _ (by
    rintro _ rfl
    exact ⟨1, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)⟩)⟩

/-- The generic point of a coordinate line other than `V(y)`, as an actual scheme point. -/
noncomputable def coordinatePoint (i : Index) (hi : i ≠ Sum.inl 1) : Proj (grading k) where
  asHomogeneousIdeal := coordinateIdeal k i
  isPrime := by
    change (Ideal.span {(X i : Coordinates k)}).IsPrime
    exact (Ideal.span_singleton_prime (X_ne_zero i)).mpr X_prime
  not_irrelevant_le h := by
    have hy := h (HomogeneousIdeal.mem_irrelevant_of_mem (grading k) Nat.zero_lt_one
      (isHomogeneous_X k (Sum.inl 1)))
    change (X (Sum.inl 1) : Coordinates k) ∈ Ideal.span {X i} at hy
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hy
    have he := congrArg (aeval (fun l : Index => if l = i then (0 : k) else 1)) ha
    simp [hi.symm] at he

theorem mem_coordinatePoint_iff (i : Index) (hi : i ≠ Sum.inl 1) (P : Coordinates k) :
    P ∈ (coordinatePoint k i hi).asHomogeneousIdeal ↔ P ∈ Ideal.span {(X i : Coordinates k)} :=
  Iff.rfl

/-- A point lies on a coordinate line exactly when it specializes the line's generic point. -/
theorem X_mem_iff_le_coordinatePoint (i : Index) (hi : i ≠ Sum.inl 1) (q : Proj (grading k)) :
    X i ∈ q.asHomogeneousIdeal ↔ q ≤ coordinatePoint k i hi := by
  rw [point_le_iff]
  change _ ↔ Ideal.span {(X i : Coordinates k)} ≤ q.asHomogeneousIdeal.toIdeal
  rw [Ideal.span_singleton_le_iff_mem]
  rfl

/-- A prime strictly inside a principal coordinate prime is zero. -/
theorem eq_bot_of_lt_span_X (P : Ideal (Coordinates k)) [hP : P.IsPrime] (i : Index)
    (h : P < Ideal.span {(X i : Coordinates k)}) : P = ⊥ := by
  have hX : (X i : Coordinates k) ∉ P := fun hx =>
    h.not_ge ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  suffices H : ∀ n : ℕ, ∀ f ∈ P, f.totalDegree ≤ n → f = 0 from
    (Submodule.eq_bot_iff _).mpr fun f hf => H _ f hf le_rfl
  intro n
  induction n with
  | zero =>
    intro f hf hdeg
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (h.le hf)
    by_contra hne
    have ha : a ≠ 0 := left_ne_zero_of_mul hne
    rw [totalDegree_mul_of_isDomain ha (X_ne_zero i), totalDegree_X] at hdeg
    omega
  | succ n ih =>
    intro f hf hdeg
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (h.le hf)
    have haP : a ∈ P := (hP.mem_or_mem hf).resolve_right hX
    by_cases ha : a = 0
    · simp [ha]
    · rw [totalDegree_mul_of_isDomain ha (X_ne_zero i), totalDegree_X] at hdeg
      exact absurd (ih a haP (by omega)) ha

/-- The canonical generic point of the projective plane is the zero homogeneous prime. -/
theorem genericPoint_eq : genericPoint (Proj (grading k)) =
    Pcf.paperPProjectiveGenericPoint (K := k) (n := 2) := by
  apply (genericPoint_spec (Proj (grading k))).eq
  exact Pcf.paperPProjectiveGenericPoint_closure (K := k) (n := 2)

theorem genericPoint_ideal :
    (genericPoint (Proj (grading k))).asHomogeneousIdeal = ⊥ := by
  rw [genericPoint_eq]
  rfl

/-- The generic point of a coordinate line has codimension one. -/
theorem coordinatePoint_coheight (i : Index) (hi : i ≠ Sum.inl 1) :
    Order.coheight (coordinatePoint k i hi) = 1 := by
  apply le_antisymm
  · rw [Order.coheight_eq_iSup_gt_coheight]
    refine iSup₂_le fun y hy => ?_
    have hle := (point_le_iff k _ _).mp hy.le
    have hnot : ¬ (coordinatePoint k i hi).asHomogeneousIdeal ≤ y.asHomogeneousIdeal :=
      fun h => hy.not_ge ((point_le_iff k _ _).mpr h)
    have hlt : y.asHomogeneousIdeal.toIdeal < Ideal.span {(X i : Coordinates k)} :=
      lt_of_le_not_ge hle hnot
    haveI := y.isPrime
    have hbot := eq_bot_of_lt_span_X k _ i hlt
    have hmax : IsMax y := by
      intro z hz
      rw [point_le_iff] at hz ⊢
      intro P hP
      have : P ∈ y.asHomogeneousIdeal.toIdeal := hP
      rw [hbot] at this
      rw [(Submodule.mem_bot _).mp this]
      exact zero_mem _
    rw [Order.coheight_eq_zero.mpr hmax]
    simp
  · have hlt : coordinatePoint k i hi < genericPoint (Proj (grading k)) := by
      refine lt_of_le_not_ge ?_ ?_
      · rw [point_le_iff, genericPoint_ideal]
        exact bot_le
      · intro h
        rw [point_le_iff, genericPoint_ideal] at h
        have hx : (X i : Coordinates k) ∈ (coordinatePoint k i hi).asHomogeneousIdeal :=
          Ideal.subset_span rfl
        have := h hx
        change (X i : Coordinates k) ∈ (⊥ : Ideal (Coordinates k)) at this
        exact X_ne_zero i ((Submodule.mem_bot _).mp this)
    have := Order.coheight_add_one_le hlt
    exact le_add_self.trans this

/-- A codimension-one point on a coordinate line is that line's generic point. -/
theorem eq_coordinatePoint_of_coheight (i : Index) (hi : i ≠ Sum.inl 1)
    (q : Proj (grading k)) (hq : Order.coheight q = 1) (hX : X i ∈ q.asHomogeneousIdeal) :
    q = coordinatePoint k i hi := by
  have hle := (X_mem_iff_le_coordinatePoint k i hi q).mp hX
  have hge : coordinatePoint k i hi ≤ q := by
    by_contra hn
    have := Order.coheight_add_one_le (lt_of_le_not_ge hle hn)
    rw [hq, coordinatePoint_coheight] at this
    norm_num at this
  apply ProjectiveSpectrum.ext
  exact le_antisymm ((point_le_iff k _ _).mp hge) ((point_le_iff k _ _).mp hle)

/-- The actual generic point of `H₀ = V(x)`. -/
noncomputable def H0gen : Proj (grading k) := coordinatePoint k (Sum.inl 0) (by decide)
/-- The actual generic point of `H₂ = V(z)`. -/
noncomputable def H2gen : Proj (grading k) := coordinatePoint k (Sum.inr ()) (by decide)

theorem H0gen_coheight : Order.coheight (H0gen k) = 1 := coordinatePoint_coheight k _ _
theorem H2gen_coheight : Order.coheight (H2gen k) = 1 := coordinatePoint_coheight k _ _

/-- The actual integral effective divisor `H₀`. -/
noncomputable def H0divisor : Pcf.SchemeDivisorPoint (Proj (grading k)) :=
  ⟨H0gen k, H0gen_coheight k⟩
/-- The actual integral effective divisor `H₂`. -/
noncomputable def H2divisor : Pcf.SchemeDivisorPoint (Proj (grading k)) :=
  ⟨H2gen k, H2gen_coheight k⟩

/-- The closure of the generic point of `H₀` is exactly `H₀`. -/
theorem closure_H0gen : closure ({H0gen k} : Set (Proj (grading k))) = H0 k := by
  ext q
  rw [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
  exact (X_mem_iff_le_coordinatePoint k (Sum.inl 0) (by decide) q).symm

/-- The closure of the generic point of `H₂` is exactly `H₂`. -/
theorem closure_H2gen : closure ({H2gen k} : Set (Proj (grading k))) = H2 k := by
  ext q
  rw [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
  exact (X_mem_iff_le_coordinatePoint k (Sum.inr ()) (by decide) q).symm

/-! ### Fixedness of the two line generic points -/

/-- Specialization `x ↦ 0` as an endomorphism of the homogeneous coordinate ring. -/
noncomputable def killX : Coordinates k →ₐ[k] Coordinates k :=
  aeval (fun i => match i with
    | Sum.inl j => if j = 0 then 0 else y k
    | Sum.inr _ => z k)

/-- The translation `y ↦ y + c z`, `x ↦ 0`. -/
noncomputable def shiftY (a : k) : Coordinates k →ₐ[k] Coordinates k :=
  aeval (fun i => match i with
    | Sum.inl j => if j = 0 then 0 else y k + C a * z k
    | Sum.inr _ => z k)

@[simp] theorem killX_x : killX k (x k) = 0 := by simp [killX, x]
@[simp] theorem killX_y : killX k (y k) = y k := by simp [killX, y]
@[simp] theorem killX_z : killX k (z k) = z k := by simp [killX, z]
@[simp] theorem shiftY_x (a : k) : shiftY k a (x k) = 0 := by simp [shiftY, x]
@[simp] theorem shiftY_y (a : k) : shiftY k a (y k) = y k + C a * z k := by simp [shiftY, y]
@[simp] theorem shiftY_z (a : k) : shiftY k a (z k) = z k := by simp [shiftY, z]

/-- Two algebra endomorphisms agreeing on `x, y, z` are equal. -/
theorem algHom_ext_xyz {f g : Coordinates k →ₐ[k] Coordinates k}
    (hx : f (x k) = g (x k)) (hy : f (y k) = g (y k)) (hz : f (z k) = g (z k)) : f = g := by
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with j | u
  · fin_cases j
    · exact hx
    · exact hy
  · exact hz

theorem sub_killX_mem (P : Coordinates k) : P - killX k P ∈ Ideal.span {x k} := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    rw [map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hP hQ
  | mul_X P i hP =>
    rw [map_mul]
    rcases i with j | u
    · fin_cases j
      · have hx : (X (Sum.inl 0) : Coordinates k) = x k := rfl
        simp only [Fin.zero_eta, hx, killX_x, mul_zero, sub_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      · have hy : (X (Sum.inl 1) : Coordinates k) = y k := rfl
        simp only [Fin.mk_one, hy, killX_y, ← sub_mul]
        exact Ideal.mul_mem_right _ _ hP
    · have hz : (X (Sum.inr u) : Coordinates k) = z k := rfl
      simp only [hz, killX_z, ← sub_mul]
      exact Ideal.mul_mem_right _ _ hP

theorem killX_comp_forms (hp : 0 < p) :
    (killX k).comp (aeval (forms k p c)) =
      (MvPolynomial.expand (p + 1)).comp ((shiftY k c).comp (killX k)) := by
  have ex : MvPolynomial.expand (p + 1) (x k) = x k ^ (p + 1) := by simp [x]
  have ey : MvPolynomial.expand (p + 1) (y k) = y k ^ (p + 1) := by simp [y]
  have ez : MvPolynomial.expand (p + 1) (z k) = z k ^ (p + 1) := by simp [z]
  apply algHom_ext_xyz
  · have : aeval (forms k p c) (x k) = forms k p c (Sum.inl 0) := by simp [x]
    rw [AlgHom.comp_apply, this, forms_zero]
    simp [zero_pow (by omega : p ≠ 0)]
  · have : aeval (forms k p c) (y k) = forms k p c (Sum.inl 1) := by simp [y]
    rw [AlgHom.comp_apply, this, forms_one]
    simp [ey, ez, zero_pow (by omega : p ≠ 0), zero_pow (by omega : p + 1 ≠ 0)]
  · have : aeval (forms k p c) (z k) = forms k p c (Sum.inr ()) := by simp [z]
    rw [AlgHom.comp_apply, this, forms_two]
    simp [ez]

theorem shiftY_neg_comp (a : k) :
    (shiftY k (-a)).comp ((shiftY k a).comp (killX k)) = killX k := by
  apply algHom_ext_xyz <;> simp

theorem killX_idem : (killX k).comp (killX k) = killX k := by
  apply algHom_ext_xyz <;> simp

/-- The exact pullback of the prime `(x)` under the displayed forms is `(x)`. -/
theorem comap_span_x (hp : 0 < p) (P : Coordinates k) :
    aeval (forms k p c) P ∈ Ideal.span {x k} ↔ P ∈ Ideal.span {x k} := by
  have hker : ∀ Q : Coordinates k, Q ∈ Ideal.span {x k} → killX k Q = 0 := by
    intro Q hQ
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hQ
    simp
  constructor
  · intro h
    have h0 := hker _ h
    have h1 : MvPolynomial.expand (p + 1) (shiftY k c (killX k P)) = 0 := by
      have := congrArg (fun f : Coordinates k →ₐ[k] Coordinates k => f P)
        (killX_comp_forms k p c hp)
      simp only [AlgHom.comp_apply] at this
      rw [← this, h0]
    have h2 : shiftY k c (killX k P) = 0 := by
      have hinj := MvPolynomial.expand_injective (σ := Index) (R := k) (by omega : 0 < p + 1)
      exact hinj (by rw [h1, map_zero])
    have h3 : killX k P = 0 := by
      have := congrArg (fun f : Coordinates k →ₐ[k] Coordinates k => f P) (shiftY_neg_comp k c)
      simp only [AlgHom.comp_apply] at this
      rw [← this, h2, map_zero]
    simpa [h3] using sub_killX_mem k P
  · intro h
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp h
    have hx : aeval (forms k p c) (x k) = x k ^ p * (x k + y k) := by
      rw [← forms_zero k p c]
      simp [x]
    rw [map_mul, hx]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) p hp))

/-- The generic point of `H₀` is fixed by the actual map. -/
theorem schemeMap_H0gen (hp : 0 < p) : schemeMap k p c hp (H0gen k) = H0gen k := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro P
  change aeval (forms k p c) P ∈ Ideal.span {x k} ↔ P ∈ Ideal.span {x k}
  exact comap_span_x k p c hp P

/-- The generic point of `H₂` is fixed by the actual map. -/
theorem schemeMap_H2gen (hp : 0 < p) : schemeMap k p c hp (H2gen k) = H2gen k := by
  letI := schemeMap_finite k p c hp
  letI := schemeMap_dominant k p c hp
  haveI := schemeMap_surjective k p c hp
  obtain ⟨u, hu⟩ := (schemeMap k p c hp).surjective (H2gen k)
  have hH2 : ∀ q, q ∈ H2 k ↔ q ≤ H2gen k := fun q =>
    X_mem_iff_le_coordinatePoint k (Sum.inr ()) (by decide) q
  have hu2 : u ∈ H2 k := by
    rw [← H2_preimage k p c hp]
    change schemeMap k p c hp u ∈ H2 k
    rw [hu, hH2]
  have hspec : H2gen k ⤳ u := Scheme.le_iff_specializes.mp ((hH2 u).mp hu2)
  have h1 : H2gen k ≤ schemeMap k p c hp (H2gen k) := by
    rw [Scheme.le_iff_specializes]
    have := hspec.map (schemeMap k p c hp).continuous
    rwa [hu] at this
  have h2 : schemeMap k p c hp (H2gen k) ≤ H2gen k := by
    rw [← hH2]
    exact (H2_preimage k p c hp ▸ ((hH2 _).mpr le_rfl) :)
  apply ProjectiveSpectrum.ext
  exact le_antisymm ((point_le_iff k _ _).mp h1) ((point_le_iff k _ _).mp h2)

/-! ### The normalized weighted loci -/

variable [Fact p.Prime] [CharP k p]

local instance normalizationIso : IsIso (Pcf.Palomar.normalizationMap (Proj (grading k))) :=
  Pcf.normalScheme_normalizationMap_isIso _
local instance finite : IsFinite (schemeMap k p c (Fact.out : p.Prime).pos) :=
  schemeMap_finite k p c _
local instance dominant : IsDominant (schemeMap k p c (Fact.out : p.Prime).pos) :=
  schemeMap_dominant k p c _

/-- The normalized weighted critical generic points are exactly those of `H₀` and `H₂`.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem weightedCriticalPointSet_eq :
    Pcf.weightedCriticalPointSet (schemeMap k p c (Fact.out : p.Prime).pos) =
      {H0gen k, H2gen k} := by
  have hd : ((p + 1 : ℕ) : k) ≠ 0 := by simp [CharP.cast_eq_zero]
  have h := Pcf.paperPFormsProjective_normalizedCriticalPointSet_eq (forms k p c) (p + 1)
    (by omega) (forms_homogeneous k p c) (forms_cover k p c (Fact.out : p.Prime).pos) hd
  change Pcf.weightedCriticalPointSet (schemeMap k p c (Fact.out : p.Prime).pos) = _ at h
  rw [h]
  ext q
  change (Order.coheight q = 1 ∧ (jacobianMatrix k p c).det ∈ q.asHomogeneousIdeal) ↔ _
  rw [jacobian_zero_iff]
  constructor
  · rintro ⟨hq, hx | hz⟩
    · exact Or.inl (eq_coordinatePoint_of_coheight k _ _ q hq hx)
    · exact Or.inr (eq_coordinatePoint_of_coheight k _ _ q hq hz)
  · rintro (rfl | hq)
    · exact ⟨H0gen_coheight k, Or.inl (Ideal.subset_span rfl)⟩
    · obtain rfl := Set.mem_singleton_iff.mp hq
      exact ⟨H2gen_coheight k, Or.inr (Ideal.subset_span rfl)⟩

/-- The normalized weighted branch generic points are exactly those of `H₀` and `H₂`.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem weightedBranchPointSet_eq :
    Pcf.weightedBranchPointSet (schemeMap k p c (Fact.out : p.Prime).pos) =
      {H0gen k, H2gen k} := by
  rw [Pcf.weightedBranchPointSet_eq_image_criticalPointSet, weightedCriticalPointSet_eq,
    Set.image_pair, schemeMap_H0gen, schemeMap_H2gen]

/-- The normalized weighted postcritical generic points are exactly those of `H₀` and `H₂`.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem weightedPostcriticalPointSet_eq :
    Pcf.weightedPostcriticalPointSet (schemeMap k p c (Fact.out : p.Prime).pos) =
      {H0gen k, H2gen k} := by
  have hfix : ∀ n q, q ∈ ({H0gen k, H2gen k} : Set (Proj (grading k))) →
      (schemeMap k p c (Fact.out : p.Prime).pos)^[n] q = q := by
    intro n q hq
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rcases hq with rfl | hq
      · exact schemeMap_H0gen k p c _
      · obtain rfl := Set.mem_singleton_iff.mp hq
        exact schemeMap_H2gen k p c _
  rw [Pcf.weightedPostcriticalPointSet, weightedBranchPointSet_eq]
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨n, r, hr, rfl⟩ := Set.mem_iUnion.mp hq
    rw [hfix n r hr]
    exact hr
  · intro q hq
    exact Set.mem_iUnion.mpr ⟨0, q, hq, rfl⟩

/-- The manuscript's closed normalized weighted critical locus is `H₀ ∪ H₂`.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem weightedCriticalLocus_eq :
    Pcf.weightedCriticalLocus (schemeMap k p c (Fact.out : p.Prime).pos) = H0 k ∪ H2 k := by
  rw [Pcf.weightedCriticalLocus, weightedCriticalPointSet_eq, Set.insert_eq, closure_union,
    closure_H0gen, closure_H2gen]

/-- The manuscript's closed normalized weighted branch locus is `H₀ ∪ H₂`.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem weightedBranchLocus_eq :
    Pcf.weightedBranchLocus (schemeMap k p c (Fact.out : p.Prime).pos) = H0 k ∪ H2 k := by
  rw [Pcf.weightedBranchLocus, weightedBranchPointSet_eq, Set.insert_eq, closure_union,
    closure_H0gen, closure_H2gen]

/-- The actual global wild-example map is generically separable.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem isGenericallySeparable :
    Pcf.IsGenericallySeparable (schemeMap k p c (Fact.out : p.Prime).pos) := by
  apply Pcf.isGenericallySeparable_of_formallyEtale_generic
  have hd : ((p + 1 : ℕ) : k) ≠ 0 := by simp [CharP.cast_eq_zero]
  apply (Pcf.paperPFormsProjective_stalk_formallyEtale_iff (forms k p c) (p + 1) (by omega)
    (forms_homogeneous k p c) (forms_cover k p c (Fact.out : p.Prime).pos) hd _).mpr
  change (jacobianMatrix k p c).det ∉ _
  rw [jacobian_zero_iff, genericPoint_ideal]
  rintro (h | h) <;>
  · change (X _ : Coordinates k) ∈ (⊥ : Ideal (Coordinates k)) at h
    exact X_ne_zero _ ((Submodule.mem_bot _).mp h)

/-! ### The structure morphism and the paper-facing PCF predicates -/

omit [Fact p.Prime] [CharP k p] in
theorem algebraMap_degreeZero_surjective :
    Function.Surjective (algebraMap k (grading k 0)) := by
  intro a
  refine ⟨(a.1 : MvPolynomial Index k).coeff 0, Subtype.ext ?_⟩
  have h0 : a.1.totalDegree = 0 :=
    Nat.le_zero.mp (((mem_homogeneousSubmodule _ _).mp a.2).totalDegree_le)
  exact ((totalDegree_eq_zero_iff_eq_C).mp h0).symm

/-- The actual projective-plane structure morphism over the ground field. -/
noncomputable def structureMap : Proj (grading k) ⟶ Spec (.of k) :=
  AlgebraicGeometry.Proj.toSpecZero (grading k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (grading k 0)))

instance structureMap_locallyOfFiniteType : LocallyOfFiniteType (structureMap k) := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (grading k 0)))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.FiniteType.of_surjective _ (algebraMap_degreeZero_surjective k))
  unfold structureMap
  infer_instance

/-- The manuscript's normalized weighted PCF predicate holds for the actual map. -/
theorem isWeightedNormalizedPCF :
    Pcf.IsWeightedNormalizedPCFDownstairs k (structureMap k)
      (schemeMap k p c (Fact.out : p.Prime).pos) := by
  apply (Pcf.isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite
    k (structureMap k) _).mpr
  rw [weightedPostcriticalPointSet_eq]
  exact (Set.finite_singleton _).insert _

/-- The ambient separable normalized PCF predicate, the root of `def:pcfawd`.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem isSeparableNormalizedPCF :
    Pcf.IsSeparableNormalizedPCF k (structureMap k)
      (schemeMap k p c (Fact.out : p.Prime).pos) :=
  (Pcf.isSeparableNormalizedPCF_iff_downstairs k (structureMap k) _).mpr
    ⟨isGenericallySeparable k p c, isWeightedNormalizedPCF k p c⟩

#print axioms coordinatePoint_coheight
#print axioms schemeMap_H0gen
#print axioms schemeMap_H2gen
#print axioms weightedCriticalPointSet_eq
#print axioms weightedBranchPointSet_eq
#print axioms weightedPostcriticalPointSet_eq
#print axioms weightedCriticalLocus_eq
#print axioms weightedBranchLocus_eq
#print axioms isGenericallySeparable
#print axioms isWeightedNormalizedPCF
#print axioms isSeparableNormalizedPCF
end Pcf.Examples.PaperP.Wild
