/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GenericRegularityDescent
public import Pcf.Bounding.SeparablyGeneratedDescent
public import Pcf.Bounding.SmoothRegularLocal
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Generic regularity of finite-type domains over an arbitrary field

Every domain of finite type over a field `k` is regular on a nonempty basic open
set (`finiteTypeGenericRegularity`). Combined with Nagata's criterion this gives
closedness of the singular locus of any scheme locally of finite type over `k`
(Stacks Lemma 29.19.3 (1), `07R5`).

The proof follows Stacks Lemma 15.48.6 ((4) ⇒ (2)): after the finite purely
inseparable base change `k ⊆ k' = k(T)` of `SeparablyGeneratedDescent`, the
domain `B = k'[A] ⊆ Ω` has formally smooth fraction field over `k'`, hence is
smooth, so regular, on a nonempty open set; and `A ⊆ B` is finite and radicial,
so regularity descends (`GenericRegularityDescent`).
-/

@[expose] public section

namespace Pcf

open IsLocalRing IntermediateField CategoryTheory

universe u

set_option linter.style.haveILetI false

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- A finitely generated subalgebra whose fraction field is formally smooth over the
base field is regular on a nonempty basic open set. -/
theorem exists_regular_basicOpen_of_formallySmooth_adjoin {K Ω : Type u} [Field K]
    [Field Ω] [Algebra K Ω] (X : Finset Ω)
    [Algebra.FormallySmooth K (IntermediateField.adjoin K (X : Set Ω))] :
    ∃ h : Algebra.adjoin K (X : Set Ω), h ≠ 0 ∧ ∀ Q : PrimeSpectrum (Algebra.adjoin K (X : Set Ω)),
      h ∉ Q.asIdeal → Q ∈ primeRegularLocus (Algebra.adjoin K (X : Set Ω)) := by
  set B := Algebra.adjoin K (X : Set Ω)
  set L := IntermediateField.adjoin K (X : Set Ω)
  have : Algebra.FiniteType K B :=
    (Subalgebra.fg_iff_finiteType B).mp (Subalgebra.fg_adjoin_finset X)
  have : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : IsLocalization (⊥ : Ideal B).primeCompl L := by
    rw [Ideal.primeCompl_bot]; infer_instance
  let e : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[B] L :=
    IsLocalization.algEquiv (⊥ : Ideal B).primeCompl _ _
  have : Algebra.FormallySmooth K (Localization.AtPrime (⊥ : Ideal B)) :=
    .of_equiv (e.symm.restrictScalars K)
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ Algebra.smoothLocus K B := this
  obtain ⟨_, ⟨h, rfl⟩, hbh, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hbot
      Algebra.isOpen_smoothLocus
  refine ⟨h, fun h0 ↦ hbh (by simp [h0]), fun Q hQ ↦ ?_⟩
  have : Algebra.IsSmoothAt K Q.asIdeal := hsub hQ
  exact isRegularLocalRing_of_isSmoothAt K B Q.asIdeal

/-- Elements of `Ω` whose `q^N`-th power lies in the image of `A` form a `k`-subalgebra. -/
def powRangeSubalgebra (k A Ω : Type*) [Field k] [CommRing A] [Algebra k A] [Field Ω]
    [Algebra k Ω] [Algebra A Ω] [IsScalarTower k A Ω] (q N : ℕ) [ExpChar Ω q] :
    Subalgebra k Ω where
  carrier := {y | y ^ (q ^ N) ∈ Set.range (algebraMap A Ω)}
  mul_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by simp only [map_mul, ha, hb, mul_pow]⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simp only [map_add, ha, hb, add_pow_expChar_pow]⟩
  algebraMap_mem' c := ⟨algebraMap k A (c ^ (q ^ N)), by
    rw [← IsScalarTower.algebraMap_apply, map_pow]⟩

/-- **Generic regularity** over an arbitrary field: every domain of finite type over
`k` is regular on a nonempty basic open set. This is condition (2) of Stacks Lemma
15.48.6 for `R = k`, i.e. the field case of Stacks Proposition 15.49.7.

Divergence from Stacks: only fields are treated, and J-0 is stated in the
basic-open form `IsGenericallyRegular`.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
@[stacks 07PJ "(1) fields; J-0 of finite-type domains"]
theorem finiteTypeGenericRegularity (k : Type u) [Field k] : FiniteTypeGenericRegularity k := by
  intro A _ _ _ _
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let K := FractionRing A
  let Ω := AlgebraicClosure K
  have hφ : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective A K)
  obtain ⟨q, hq⟩ := ExpChar.exists k
  have : ExpChar Ω q := expChar_of_injective_algebraMap (algebraMap k Ω).injective q
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  set X := s.image (algebraMap A Ω)
  obtain ⟨T, hTP, hsm⟩ := exists_finset_perfectClosure_formallySmooth_adjoin k Ω X
  set k' := IntermediateField.adjoin k (T : Set Ω)
  set B := Algebra.adjoin k' (X : Set Ω)
  obtain ⟨h', hh'0, hreg⟩ := exists_regular_basicOpen_of_formallySmooth_adjoin (K := k') X
  -- `T` is integral over `k`, so `k' = k[T]`
  have hTint : ∀ t ∈ (T : Set Ω), IsIntegral k t := fun t ht ↦ by
    have := Algebra.IsIntegral.isIntegral (R := k) (⟨t, hTP ht⟩ : perfectClosure k Ω)
    simpa using this.map (perfectClosure k Ω).val
  have hk' : ∀ c, c ∈ k' ↔ c ∈ Algebra.adjoin k (T : Set Ω) := by
    intro c
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      fun t ht ↦ (hTint t ht).isAlgebraic]
    rfl
  -- the image of `A` lies in `B`
  have hφB : ∀ a : A, algebraMap A Ω a ∈ B := by
    intro a
    have ha : a ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have : IsScalarTower.toAlgHom k A Ω a ∈
        (Algebra.adjoin k (s : Set A)).map (IsScalarTower.toAlgHom k A Ω) :=
      Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin] at this
    have hle : Algebra.adjoin k ((IsScalarTower.toAlgHom k A Ω) '' (s : Set A)) ≤
        B.restrictScalars k := by
      refine Algebra.adjoin_le fun y hy ↦ ?_
      have hyX : y ∈ (X : Set Ω) := by
        obtain ⟨z, hz, rfl⟩ := hy
        exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
      exact (show y ∈ B from Algebra.subset_adjoin hyX)
    exact hle this
  letI : Algebra A B := (RingHom.codRestrict (algebraMap A Ω) B hφB).toAlgebra
  have hinj : Function.Injective (algebraMap A B) := fun a b h ↦ hφ (congrArg Subtype.val h)
  have hval : ∀ a : A, ((algebraMap A B a : B) : Ω) = algebraMap A Ω a := fun _ ↦ rfl
  -- radicial: a fixed `q`-power of every element of `B` lies in `A`
  have hTpow : ∀ t ∈ T, ∃ n, t ^ (q ^ n) ∈ Set.range (algebraMap k Ω) := fun t ht ↦
    (mem_perfectClosure_iff_pow_mem q).mp (hTP ht)
  choose! nT hnT using hTpow
  set N := T.sup nT
  set R := powRangeSubalgebra k A Ω q N
  have hTR : ∀ t ∈ T, t ∈ R := by
    intro t ht
    obtain ⟨c, hc⟩ := hnT t ht
    have hle : nT t ≤ N := Finset.le_sup ht
    refine ⟨algebraMap k A (c ^ (q ^ (N - nT t))), ?_⟩
    rw [← IsScalarTower.algebraMap_apply, map_pow, hc, ← pow_mul, ← pow_add,
      Nat.add_sub_cancel' hle]
  have hk'R : ∀ c ∈ k', c ∈ R := by
    intro c hc
    have hc' : c ∈ Algebra.adjoin k (T : Set Ω) := (hk' c).mp hc
    exact Algebra.adjoin_le (fun t ht ↦ hTR t ht) hc'
  let R' : Subalgebra k' Ω :=
    { R.toSubsemiring with algebraMap_mem' := fun c ↦ hk'R c c.2 }
  have hBR : B ≤ R' := Algebra.adjoin_le fun x hx ↦ by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨a ^ (q ^ N), by rw [map_pow]⟩
  have hpow : ∀ b : B, b ^ (q ^ N) ∈ Set.range (algebraMap A B) := by
    intro b
    obtain ⟨a, ha⟩ := hBR b.2
    exact ⟨a, Subtype.ext (by rw [hval, ha]; rfl)⟩
  -- finiteness: `B ⊆ A[T]`, which is finite over `A`
  set BA := Algebra.adjoin A (T : Set Ω)
  have : Module.Finite A BA := Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet
    fun t ht ↦ (hTint t ht).tower_top
  have hk'BA : ∀ c ∈ k', c ∈ BA := by
    intro c hc
    have hc' : c ∈ Algebra.adjoin k (T : Set Ω) := (hk' c).mp hc
    have hle : Algebra.adjoin k (T : Set Ω) ≤ BA.restrictScalars k :=
      Algebra.adjoin_le fun t ht ↦ (show t ∈ BA from Algebra.subset_adjoin ht)
    exact hle hc'
  let BA' : Subalgebra k' Ω := { BA.toSubsemiring with algebraMap_mem' := fun c ↦ hk'BA c c.2 }
  have hBBA : B ≤ BA' := Algebra.adjoin_le fun x hx ↦ by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    exact Subalgebra.algebraMap_mem BA a
  let ι : B →ₗ[A] BA :=
    { toFun := fun b ↦ ⟨b, hBBA b.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a b ↦ by
        apply Subtype.ext
        change ((a • b : B) : Ω) = a • (b : Ω)
        rw [Algebra.smul_def, Algebra.smul_def]
        rfl }
  have : Module.Finite A B := Module.Finite.of_injective ι fun x y h ↦
    Subtype.ext (congrArg Subtype.val h :)
  exact isGenericallyRegular_of_finite_of_pow_mem hinj (expChar_pow_pos k q N) hpow h' hh'0 hreg


/-- Stacks Lemma 29.19.3 (1), closedness form: the singular locus of a scheme locally
of finite type over an arbitrary field is closed.

Divergence from Stacks: Stacks proves the J-2 property (openness of the regular
locus for every scheme locally of finite type over the field). This declaration
states closedness of the singular locus of `X` itself.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
@[stacks 07R5 "(1), closedness of the singular locus of X"]
theorem isClosed_stalkSingularLocus_of_locallyOfFiniteType
    (k : Type u) [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.LocallyOfFiniteType f] :
    IsClosed (stalkSingularLocus X) :=
  isClosed_stalkSingularLocus_of_finiteTypeGenericRegularity (finiteTypeGenericRegularity k) f

/-- `paper-p.tex`, `thm:bounding`, Step 0, over an arbitrary field: the exact
exceptional set `Σ = (B ∩ Z) ∪ (B ∩ Sing Y) ∪ Sing B` is closed and proper, and
contains only finitely many divisor generic points.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem paperPBoundingSigma_closed_proper_finite
    (k : Type u) [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral Y]
    [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y]
    [IsNormalScheme Y] [TopologicalSpace.NoetherianSpace X] [TopologicalSpace.NoetherianSpace Y]
    [AlgebraicGeometry.IsFinite (Palomar.normalizationMap X)]
    [AlgebraicGeometry.IsFinite (Palomar.normalizationMap Y)]
    (s : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.LocallyOfFiniteType s]
    (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsDominant f]
    (hsep : IsGenericallySeparableSchemeMap f)
    (B : SchemeDivisorPoint Y) :
    IsClosed (paperPBoundingSigma f B) ∧
      paperPBoundingSigma f B ≠ Set.univ ∧
      {Q : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
        closure ({Q.1} : Set (pointClosureIdealSheaf B.1).subscheme) ⊆
          paperPBoundingSigma f B}.Finite :=
  paperPBoundingSigma_closed_proper_finite_of_finiteTypeGenericRegularity k
    (finiteTypeGenericRegularity k) s f hsep B

/-- Bounding-data form over an arbitrary field, for monodromy not divisible by `p`
(any `p : ℕ`; `p = 0` is the characteristic-zero case).

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem paperPBoundingSigma_closed_proper_finite_of_primeToPMonodromy
    (p : ℕ) (k : Type u) [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral Y] [IsNormalScheme Y]
    [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y]
    [TopologicalSpace.NoetherianSpace X] [TopologicalSpace.NoetherianSpace Y]
    (s : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.LocallyOfFiniteType s]
    (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f)
    (A : SchemeDivisorPoint X) :
    letI : AlgebraicGeometry.IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : AlgebraicGeometry.IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    IsClosed (paperPBoundingSigma f (A.mapFiniteDominantNormal f)) ∧
      paperPBoundingSigma f (A.mapFiniteDominantNormal f) ≠ Set.univ ∧
      {Q : SchemeDivisorPoint
          (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme |
        closure ({Q.1} : Set
          (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme) ⊆
          paperPBoundingSigma f (A.mapFiniteDominantNormal f)}.Finite :=
  paperPBoundingSigma_closed_proper_finite_of_primeToPMonodromy_of_genericRegularity p k
    (finiteTypeGenericRegularity k) s f hmono A

#print axioms finiteTypeGenericRegularity
#print axioms isClosed_stalkSingularLocus_of_locallyOfFiniteType
#print axioms paperPBoundingSigma_closed_proper_finite
#print axioms paperPBoundingSigma_closed_proper_finite_of_primeToPMonodromy

#print axioms exists_regular_basicOpen_of_formallySmooth_adjoin

end Pcf
