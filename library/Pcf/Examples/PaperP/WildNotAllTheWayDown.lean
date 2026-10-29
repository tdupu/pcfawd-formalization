/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.WildLineReturn
public import Pcf.Examples.PaperP.WildProjectiveOrbit
public import Pcf.Examples.PaperP.BasilicaProjectiveWeightedPCF

/-!
# The wild example is PCF but not PCF all the way down

For `latex/paper-p.tex`, Example `ex:wild`, the canonical reduced closed
subscheme of the invariant line `H₀` is identified, compatibly with the actual
returns, with the actual projective-line morphism
`[u : v] ↦ [u^(p+1) + c v^(p+1) : v^(p+1)]`, i.e. `h(t) = t^(p+1) + c` in the
coordinate `t = y/z`. The point `t = 0` is a normalized weighted critical
point of this return, and for `c` transcendental over `𝔽_p` its forward orbit
is infinite. Hence the canonical return is not PCF, and the actual ambient map,
which is PCF, satisfies neither `Pcf.IsPCFAllDivisors` (Definition `def:pcfawd`)
nor `Pcf.IsPCFAllSubvarieties`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
namespace Pcf.Examples.PaperP.Wild
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type*) [Field k] (p : ℕ) (c : k)

/-! ### The image of the linear embedding -/

theorem mem_lineEmbedding_apply (q : Proj (lineGrading k)) (P : Coordinates k) :
    P ∈ (lineEmbedding k q).asHomogeneousIdeal ↔ lineGradedHom k P ∈ q.asHomogeneousIdeal :=
  Iff.rfl

@[simp] theorem lineSpecialization_x : lineSpecialization k (x k) = 0 := by
  simp [lineSpecialization, lineValues, x]
@[simp] theorem lineSpecialization_y : lineSpecialization k (y k) = lu k := by
  simp [lineSpecialization, lineValues, y]
@[simp] theorem lineSpecialization_z : lineSpecialization k (z k) = lv k := by
  simp [lineSpecialization, lineValues, z]
@[simp] theorem lineSection_lu : lineSection k (lu k) = y k := by simp [lineSection, lu]
@[simp] theorem lineSection_lv : lineSection k (lv k) = z k := by simp [lineSection, lv]

theorem killX_eq_lineSection (P : Coordinates k) :
    killX k P = lineSection k (lineSpecialization k P) := by
  have h : killX k = (lineSection k).comp (lineSpecialization k) := by
    apply algHom_ext_xyz <;> simp
  exact congrArg (fun f : Coordinates k →ₐ[k] Coordinates k => f P) h

/-- The kernel of the specialization to `H₀` is `(x)`. -/
theorem lineSpecialization_eq_zero_iff (P : Coordinates k) :
    lineSpecialization k P = 0 ↔ P ∈ Ideal.span {x k} := by
  constructor
  · intro h
    have h0 : killX k P = 0 := by rw [killX_eq_lineSection, h, map_zero]
    simpa [h0] using sub_killX_mem k P
  · intro h
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp h
    simp [lineSpecialization, lineValues, x]

/-- The generic point of the projective line maps to the generic point of `H₀`. -/
theorem lineEmbedding_genericPoint :
    lineEmbedding k (Pcf.paperPProjectiveGenericPoint (K := k) (n := 1)) = H0gen k := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro P
  change lineGradedHom k P ∈ (⊥ : Ideal (LineCoords k)) ↔ P ∈ Ideal.span {x k}
  rw [Submodule.mem_bot]
  exact lineSpecialization_eq_zero_iff k P

local instance lineClosed : IsClosedImmersion (lineEmbedding k) :=
  lineEmbedding_isClosedImmersion k

/-- The actual image of the closed immersion is exactly `H₀`. -/
theorem lineEmbedding_range : Set.range (lineEmbedding k) = H0 k := by
  apply Set.Subset.antisymm
  · rintro _ ⟨q, rfl⟩
    change lineSpecialization k (x k) ∈ q.asHomogeneousIdeal.toIdeal
    rw [lineSpecialization_x]
    exact zero_mem _
  · rw [← closure_H0gen]
    apply closure_minimal _ (lineEmbedding k).isClosedEmbedding.isClosed_range
    rintro _ rfl
    exact ⟨_, lineEmbedding_genericPoint k⟩

private theorem lineEmbedding_ker_radical :
    (lineEmbedding k).ker.radical = (lineEmbedding k).ker := by
  ext U : 2
  simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  apply le_antisymm
  · intro r hr
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hr
    change (lineEmbedding k).app U r = 0
    apply IsReduced.eq_zero
    refine ⟨n, ?_⟩
    rw [← map_pow]
    exact hn
  · exact Ideal.le_radical

/-- The linear embedding and the canonical reduced divisor `H₀` have the same ideal sheaf. -/
theorem lineEmbedding_ker_eq_pointClosure :
    (lineEmbedding k).ker = Pcf.pointClosureIdealSheaf (H0gen k) := by
  rw [← lineEmbedding_ker_radical k, ← Scheme.IdealSheafData.vanishingIdeal_support]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply TopologicalSpace.Closeds.ext
  rw [Scheme.Hom.support_ker, lineEmbedding_range]
  change closure (H0 k) = closure {H0gen k}
  rw [closure_H0gen, ← closure_H0gen, closure_closure]

/-- The canonical reduced subscheme of `H₀` identified with the projective line. -/
noncomputable def canonicalH0ToLine :
    (Pcf.pointClosureIdealSheaf (H0gen k)).subscheme ⟶ Proj (lineGrading k) :=
  IsClosedImmersion.lift (lineEmbedding k)
    (Pcf.pointClosureIdealSheaf (H0gen k)).subschemeι (by
      rw [Scheme.IdealSheafData.ker_subschemeι, lineEmbedding_ker_eq_pointClosure])

instance canonicalH0ToLine_isIso : IsIso (canonicalH0ToLine k) := by
  apply IsClosedImmersion.isIso_lift
  rw [Scheme.IdealSheafData.ker_subschemeι, lineEmbedding_ker_eq_pointClosure]

@[reassoc (attr := simp)] theorem canonicalH0ToLine_embedding :
    canonicalH0ToLine k ≫ lineEmbedding k = (Pcf.pointClosureIdealSheaf (H0gen k)).subschemeι :=
  IsClosedImmersion.lift_fac ..

/-- The canonical reduced return on `H₀` is conjugate to the actual line return.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem canonicalH0Return_square (hp : 0 < p) :
    Pcf.pointClosureReturnMap (schemeMap k p c hp) (H0gen k) (schemeMap_H0gen k p c hp) ≫
        canonicalH0ToLine k =
      canonicalH0ToLine k ≫ lineReturnMap k p c := by
  rw [← cancel_mono (lineEmbedding k), Category.assoc, canonicalH0ToLine_embedding,
    Pcf.pointClosureReturnMap, Pcf.pointClosureSubschemeMap_subschemeι, Category.assoc,
    ← lineEmbedding_comp_schemeMap, canonicalH0ToLine_embedding_assoc]

/-! ### The line return is not PCF -/

local notation "LP" => Pcf.Examples.PaperP.BasilicaProjectiveScheme.point k

/-- The actual scheme point `[t : 1]` of the projective line. -/
noncomputable def finitePoint (t : k) : Proj (lineGrading k) := LP t 1 (Or.inr one_ne_zero)

theorem finitePoint_zero :
    finitePoint k 0 = Pcf.Examples.PaperP.BasilicaProjectiveScheme.zero k := rfl

theorem finitePoint_injective : Function.Injective (finitePoint k) := by
  intro a b h
  have ha : lu k - C a * lv k ∈ (finitePoint k a).asHomogeneousIdeal := by
    change aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k a 1)
      (lu k - C a * lv k) = 0
    simp [Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms, lu, lv]
  rw [h] at ha
  change aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k b 1)
    (lu k - C a * lv k) = 0 at ha
  have hh : C (b - a) * (X (Sum.inl 0) : LineCoords k) = 0 := by
    simpa [Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms, lu, lv, map_sub, sub_mul]
      using ha
  have hC : C (b - a) = (0 : LineCoords k) :=
    (mul_eq_zero.mp hh).resolve_right (X_ne_zero _)
  exact (sub_eq_zero.mp ((C_injective LineIndex k) (by simpa using hC))).symm

theorem finitePointForms_comp_lineForms (t : k) :
    (aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k t 1)).comp
        (aeval (lineForms k p c)) =
      (MvPolynomial.expand (p + 1)).comp
        (aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k
          (returnFunction k p c t) 1)) := by
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with j | u
  · simp [Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms, lineForms, lu, lv,
      returnFunction, MvPolynomial.expand_X, mul_pow]
    ring
  · simp [Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms, lineForms, lv,
      MvPolynomial.expand_X]

/-- The actual line return acts on `[t : 1]` by `t ↦ t^(p+1) + c`.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem lineReturnMap_finitePoint (t : k) :
    lineReturnMap k p c (finitePoint k t) = finitePoint k (returnFunction k p c t) := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro P
  change aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k t 1)
      (aeval (lineForms k p c) P) = 0 ↔
    aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k (returnFunction k p c t) 1)
      P = 0
  rw [← AlgHom.comp_apply, finitePointForms_comp_lineForms, AlgHom.comp_apply]
  exact MvPolynomial.expand_eq_zero (by omega : 0 < p + 1)

theorem lineReturnMap_iterate_finitePoint (t : k) (n : ℕ) :
    (lineReturnMap k p c)^[n] (finitePoint k t) =
      finitePoint k ((returnFunction k p c)^[n] t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, lineReturnMap_finitePoint,
      Function.iterate_succ_apply']

/-- The homogeneous Jacobian of the line return. -/
theorem lineJacobian_det :
    Matrix.det (fun i j => pderiv j (lineForms k p c i)) =
      ((p + 1 : k) • lu k ^ p) * ((p + 1 : k) • lv k ^ p) := by
  have hM : (fun i j => pderiv j (lineForms k p c i)) =
      Matrix.fromBlocks (fun _ _ : Fin 1 => (p + 1 : k) • lu k ^ p)
        (fun (_ : Fin 1) (_ : Unit) => C c * ((p + 1 : k) • lv k ^ p)) 0
        (fun _ _ : Unit => (p + 1 : k) • lv k ^ p) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lineForms, lu, lv, pderiv_X, Matrix.fromBlocks, smul_eq_C_mul]
  rw [hM, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique, Matrix.det_unique]

local instance lineNormalizationIso : IsIso (Pcf.Palomar.normalizationMap (Proj (lineGrading k))) :=
  Pcf.normalScheme_normalizationMap_isIso _

local instance lineReturnFinite : IsFinite (lineReturnMap k p c) :=
  Pcf.paperPFormsProjective_isFinite _ _ _ _ _
local instance lineReturnDominant : IsDominant (lineReturnMap k p c) := by
  unfold lineReturnMap
  infer_instance

/-- The origin `t = 0` of `H₀` is a normalized weighted critical point of the return. -/
theorem zero_mem_lineWeightedCriticalPointSet [Fact p.Prime] [CharP k p] :
    finitePoint k 0 ∈ Pcf.weightedCriticalPointSet (lineReturnMap k p c) := by
  have hd : ((p + 1 : ℕ) : k) ≠ 0 := by simp [CharP.cast_eq_zero]
  have h := Pcf.paperPFormsProjective_normalizedCriticalPointSet_eq (lineForms k p c) (p + 1)
    (by omega) (lineForms_homogeneous k p c) (lineForms_cover k p c) hd
  change Pcf.weightedCriticalPointSet (lineReturnMap k p c) = _ at h
  rw [h]
  refine ⟨Pcf.Examples.PaperP.BasilicaProjectiveScheme.zero_coheight k, ?_⟩
  rw [lineJacobian_det]
  have hu : lu k ∈ (finitePoint k 0).asHomogeneousIdeal :=
    (Pcf.Examples.PaperP.BasilicaProjectiveScheme.firstCoordinate_mem_iff k _).mpr rfl
  apply Ideal.mul_mem_right
  rw [smul_eq_C_mul]
  exact Ideal.mul_mem_left _ _
    (Ideal.pow_mem_of_mem _ hu p (Fact.out : p.Prime).pos)


/-- The point `∞ = [1 : 0]` is fixed by the actual line return. -/
theorem lineReturnMap_infinity :
    lineReturnMap k p c (Pcf.Examples.PaperP.BasilicaProjectiveScheme.infinity k) =
      Pcf.Examples.PaperP.BasilicaProjectiveScheme.infinity k := by
  have hcomp : (aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k 1 0)).comp
        (aeval (lineForms k p c)) =
      (MvPolynomial.expand (p + 1)).comp
        (aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k 1 0)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with j | u
    · simp [Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms, lineForms, lu, lv,
        MvPolynomial.expand_X]
    · simp [Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms, lineForms, lv,
        MvPolynomial.expand_X]
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro P
  change aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k 1 0)
      (aeval (lineForms k p c) P) = 0 ↔
    aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k 1 0) P = 0
  rw [← AlgHom.comp_apply, hcomp, AlgHom.comp_apply]
  exact MvPolynomial.expand_eq_zero (by omega : 0 < p + 1)

/-- The exact normalized weighted critical points of the line return are `0` and `∞`.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem lineWeightedCriticalPointSet_eq [Fact p.Prime] [CharP k p] :
    Pcf.weightedCriticalPointSet (lineReturnMap k p c) =
      {finitePoint k 0, Pcf.Examples.PaperP.BasilicaProjectiveScheme.infinity k} := by
  have hd : ((p + 1 : ℕ) : k) ≠ 0 := by simp [CharP.cast_eq_zero]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h := Pcf.paperPFormsProjective_normalizedCriticalPointSet_eq (lineForms k p c) (p + 1)
    (by omega) (lineForms_homogeneous k p c) (lineForms_cover k p c) hd
  change Pcf.weightedCriticalPointSet (lineReturnMap k p c) = _ at h
  rw [h]
  have hunit : ((p + 1 : k)) = 1 := by
    have : ((p : ℕ) : k) = 0 := CharP.cast_eq_zero k p
    simp [this]
  ext q
  rw [lineJacobian_det, hunit, one_smul, one_smul]
  change (Order.coheight q = 1 ∧ lu k ^ p * lv k ^ p ∈ q.asHomogeneousIdeal.toIdeal) ↔ _
  rw [q.isPrime.mul_mem_iff_mem_or_mem, q.isPrime.pow_mem_iff_mem p hp,
    q.isPrime.pow_mem_iff_mem p hp]
  change (_ ∧ ((X (Sum.inl 0) : LineCoords k) ∈ q.asHomogeneousIdeal ∨
    (X (Sum.inr ()) : LineCoords k) ∈ q.asHomogeneousIdeal)) ↔ _
  rw [Pcf.Examples.PaperP.BasilicaProjectiveScheme.firstCoordinate_mem_iff,
    Pcf.Examples.PaperP.BasilicaProjectiveScheme.secondCoordinate_mem_iff]
  constructor
  · rintro ⟨_, h0 | h1⟩
    · exact Or.inl h0
    · exact Or.inr h1
  · rintro (rfl | hq)
    · exact ⟨Pcf.Examples.PaperP.BasilicaProjectiveScheme.zero_coheight k, Or.inl rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hq
      exact ⟨Pcf.Examples.PaperP.BasilicaProjectiveScheme.infinity_coheight k, Or.inr rfl⟩

local instance lineReturnPrimeFieldAlgebra [CharP k p] : Algebra (ZMod p) k :=
  ZMod.algebra k p

/-- For transcendental `c`, the weighted postcritical set of the line return is infinite.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem lineWeightedPostcriticalPointSet_infinite [Fact p.Prime] [CharP k p]
    (hc : Transcendental (ZMod p) c) :
    (Pcf.weightedPostcriticalPointSet (lineReturnMap k p c)).Infinite := by
  have hsub : Set.range (fun n : ℕ => (lineReturnMap k p c)^[n + 1] (finitePoint k 0)) ⊆
      Pcf.weightedPostcriticalPointSet (lineReturnMap k p c) := by
    rintro _ ⟨n, rfl⟩
    refine Set.mem_iUnion.mpr ⟨n, lineReturnMap k p c (finitePoint k 0), ?_, ?_⟩
    · rw [Pcf.weightedBranchPointSet_eq_image_criticalPointSet]
      exact ⟨_, zero_mem_lineWeightedCriticalPointSet k p c, rfl⟩
    · exact (Function.iterate_succ_apply _ n _).symm
  apply Set.Infinite.mono hsub
  apply Set.infinite_range_of_injective
  intro m n h
  simp only [lineReturnMap_iterate_finitePoint] at h
  have := returnFunction_orbit_injective k p c hc (finitePoint_injective k h)
  exact Nat.succ_injective this

/-! ### Transport across the canonical identification -/

/-- Weighted branch support is empty for an isomorphism. -/
theorem weightedBranchPointSet_eq_empty_of_isIso {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Pcf.Palomar.normalizationMap X)] [IsFinite (Pcf.Palomar.normalizationMap Y)]
    (e : X ⟶ Y) [IsIso e] : Pcf.weightedBranchPointSet e = ∅ := by
  have hcongr : ∀ (f g : X ⟶ X) [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g],
      f = g → Pcf.weightedBranchPointSet f = Pcf.weightedBranchPointSet g := by
    intro f g _ _ _ _ h
    subst h
    rfl
  have h := Pcf.weightedBranchPointSet_comp e (inv e)
  rw [hcongr (e ≫ inv e) (𝟙 X) (IsIso.hom_inv_id e), Pcf.weightedBranchPointSet_id] at h
  exact Set.image_eq_empty.mp (Set.union_empty_iff.mp h.symm).2


/-- Conjugation by an isomorphism transports the weighted postcritical generic points. -/
theorem weightedPostcriticalPointSet_image_of_conj {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Pcf.Palomar.normalizationMap X)] [IsFinite (Pcf.Palomar.normalizationMap Y)]
    (e : X ⟶ Y) [IsIso e] (f : X ⟶ X) (g : Y ⟶ Y) [IsFinite f] [IsDominant f]
    [IsFinite g] [IsDominant g] (h : f ≫ e = e ≫ g) :
    e '' Pcf.weightedPostcriticalPointSet f = Pcf.weightedPostcriticalPointSet g := by
  have hcongr : ∀ (a b : X ⟶ Y) [IsFinite a] [IsDominant a] [IsFinite b] [IsDominant b],
      a = b → Pcf.weightedBranchPointSet a = Pcf.weightedBranchPointSet b := by
    intro a b _ _ _ _ hab
    subst hab
    rfl
  have hB : e '' Pcf.weightedBranchPointSet f = Pcf.weightedBranchPointSet g := by
    have h1 := Pcf.weightedBranchPointSet_comp f e
    have h2 := Pcf.weightedBranchPointSet_comp e g
    rw [weightedBranchPointSet_eq_empty_of_isIso e, Set.empty_union] at h1
    rw [weightedBranchPointSet_eq_empty_of_isIso e, Set.image_empty, Set.union_empty] at h2
    rw [← h1, ← h2]
    exact hcongr _ _ h
  have hpt1 : ∀ q, e (f q) = g (e q) := by
    intro q
    have := congrArg (fun m : X ⟶ Y => m q) h
    simpa only [Scheme.Hom.comp_apply] using this
  have hpt : ∀ n q, e ((f : X → X)^[n] q) = (g : Y → Y)^[n] (e q) := by
    intro n
    induction n with
    | zero => intro q; rfl
    | succ n ih =>
      intro q
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hpt1, ih]
  unfold Pcf.weightedPostcriticalPointSet
  rw [Set.image_iUnion]
  congr 1
  funext n
  rw [← hB, Set.image_image, Set.image_image]
  exact Set.image_congr fun q _ => hpt n q

local instance ambientFinite [Fact p.Prime] :
    IsFinite (schemeMap k p c (Fact.out : p.Prime).pos) := schemeMap_finite k p c _
local instance ambientDominant [Fact p.Prime] :
    IsDominant (schemeMap k p c (Fact.out : p.Prime).pos) := schemeMap_dominant k p c _

/-- For transcendental `c`, the canonical reduced return on `H₀` is not PCF, for any
structure morphism of the reduced divisor.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem canonicalH0Return_not_isSeparableNormalizedPCF [Fact p.Prime] [CharP k p]
    (hc : Transcendental (ZMod p) c)
    (s : (Pcf.pointClosureIdealSheaf (H0gen k)).subscheme ⟶ Spec (.of k))
    [LocallyOfFiniteType s] :
    ¬ Pcf.IsSeparableNormalizedPCF k s (Pcf.pointClosureReturnMap
      (schemeMap k p c (Fact.out : p.Prime).pos) (H0gen k)
      (schemeMap_H0gen k p c (Fact.out : p.Prime).pos)) := by
  intro hpcf
  have hw := ((Pcf.isSeparableNormalizedPCF_iff_downstairs k s _).mp hpcf).2
  have hfin := (Pcf.isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite
    k s _).mp hw
  letI : IsFinite (Pcf.Palomar.normalizationMap
      (Pcf.pointClosureIdealSheaf (H0gen k)).subscheme) :=
    Pcf.schemeGlobalNormalizationMap_isFinite _ k s
  apply lineWeightedPostcriticalPointSet_infinite k p c hc
  rw [← weightedPostcriticalPointSet_image_of_conj (canonicalH0ToLine k) _ _
    (canonicalH0Return_square k p c (Fact.out : p.Prime).pos)]
  exact hfin.image _


set_option maxHeartbeats 1000000 in
-- Reducing the dependent recursive return type to the fixed line uses extra heartbeats.
/-- `paper-p.tex`, Example `ex:wild`: the actual map is not PCF all the way down
(Definition `def:pcfawd`), already at the first divisor return on `H₀`.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem schemeMap_not_isPCFAllDivisors [Fact p.Prime] [CharP k p]
    (hc : Transcendental (ZMod p) c) :
    ¬ Pcf.IsPCFAllDivisors k (structureMap k) (schemeMap k p c (Fact.out : p.Prime).pos) := by
  intro h
  have h₁ := h 1
  change Pcf.IsSeparableNormalizedPCF k (structureMap k) _ ∧ _ at h₁
  have hperiodic : Pcf.schemePointIterate (schemeMap k p c (Fact.out : p.Prime).pos) (0 + 1)
      (H0divisor k).1 =
      Pcf.schemePointIterate (schemeMap k p c (Fact.out : p.Prime).pos) 0 (H0divisor k).1 := by
    simpa [Pcf.schemePointIterate, H0divisor] using schemeMap_H0gen k p c _
  have hreturn := h₁.2 (H0divisor k) 0 1 le_rfl hperiodic
  change Pcf.IsSeparableNormalizedPCF k _ (Pcf.pointClosureReturnMap
    (schemeMap k p c (Fact.out : p.Prime).pos) (H0gen k)
    (schemeMap_H0gen k p c (Fact.out : p.Prime).pos)) at hreturn
  exact canonicalH0Return_not_isSeparableNormalizedPCF k p c hc
    ((Pcf.pointClosureIdealSheaf (H0gen k)).subschemeι ≫ structureMap k) hreturn

set_option maxHeartbeats 1000000 in
-- Reducing the dependent recursive return type to the fixed line uses extra heartbeats.
/-- The actual map also fails the all-proper-subvarieties variant of PCF all the way down.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem schemeMap_not_isPCFAllSubvarieties [Fact p.Prime] [CharP k p]
    (hc : Transcendental (ZMod p) c) :
    ¬ Pcf.IsPCFAllSubvarieties k (structureMap k)
      (schemeMap k p c (Fact.out : p.Prime).pos) := by
  intro h
  have h₁ := h 1
  change Pcf.IsSeparableNormalizedPCF k (structureMap k) _ ∧ _ at h₁
  let C : Pcf.ProperIntegralSubvarietyPoint (Proj (grading k)) :=
    ⟨H0gen k, (H0divisor k).ne_genericPoint⟩
  have hperiodic : Pcf.schemePointIterate (schemeMap k p c (Fact.out : p.Prime).pos) (0 + 1)
      C.1 = Pcf.schemePointIterate (schemeMap k p c (Fact.out : p.Prime).pos) 0 C.1 := by
    simpa [Pcf.schemePointIterate, C] using schemeMap_H0gen k p c _
  have hreturn := h₁.2 C 0 1 le_rfl hperiodic
  change Pcf.IsSeparableNormalizedPCF k _ (Pcf.pointClosureReturnMap
    (schemeMap k p c (Fact.out : p.Prime).pos) (H0gen k)
    (schemeMap_H0gen k p c (Fact.out : p.Prime).pos)) at hreturn
  exact canonicalH0Return_not_isSeparableNormalizedPCF k p c hc
    ((Pcf.pointClosureIdealSheaf (H0gen k)).subschemeι ≫ structureMap k) hreturn

/-- `paper-p.tex`, Example `ex:wild`, final sentence: the actual map is PCF but not
PCF all the way down.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem isSeparableNormalizedPCF_and_not_isPCFAllDivisors [Fact p.Prime] [CharP k p]
    (hc : Transcendental (ZMod p) c) :
    Pcf.IsSeparableNormalizedPCF k (structureMap k) (schemeMap k p c (Fact.out : p.Prime).pos) ∧
      ¬ Pcf.IsPCFAllDivisors k (structureMap k) (schemeMap k p c (Fact.out : p.Prime).pos) :=
  ⟨isSeparableNormalizedPCF k p c, schemeMap_not_isPCFAllDivisors k p c hc⟩

#print axioms lineEmbedding_isClosedImmersion
#print axioms lineEmbedding_comp_schemeMap
#print axioms lineEmbedding_range
#print axioms lineEmbedding_ker_eq_pointClosure
#print axioms canonicalH0ToLine_isIso
#print axioms canonicalH0Return_square
#print axioms lineReturnMap_finitePoint
#print axioms zero_mem_lineWeightedCriticalPointSet
#print axioms lineReturnMap_infinity
#print axioms lineWeightedCriticalPointSet_eq
#print axioms lineWeightedPostcriticalPointSet_infinite
#print axioms weightedPostcriticalPointSet_image_of_conj
#print axioms canonicalH0Return_not_isSeparableNormalizedPCF
#print axioms schemeMap_not_isPCFAllDivisors
#print axioms schemeMap_not_isPCFAllSubvarieties
#print axioms isSeparableNormalizedPCF_and_not_isPCFAllDivisors
end Pcf.Examples.PaperP.Wild
