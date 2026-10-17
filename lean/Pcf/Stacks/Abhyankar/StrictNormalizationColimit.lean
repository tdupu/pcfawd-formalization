/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.Flat.TorsionFree
public import Pcf.Stacks.Abhyankar.NormalizationBaseChange
public import Pcf.Stacks.Abhyankar.StrictHenselizationColimit
public import Pcf.Stacks.Abhyankar.StrictHenselizationCompletionFlat
public import Pcf.Stacks.Abhyankar.StrictHenselizationQuotientComparison
public import Pcf.Stacks.Common.RegularLocalization

/-!
# The divisor and the normalization in the strict henselization

Two inputs of the strict-local paragraph of Stacks Tag `0EYG` for the pointed-étale-colimit model
`Rˢʰ = LocalColimit R Ω` of the strict henselization.

**A2 (the divisor stays regular).**  "Since `A → A^{sh}` is flat ... `f` maps to a nonzerodivisor
... `A^{sh}/fA^{sh} = (A/fA)^{sh}` (`05WS`) is a regular local ring as the strict henselization of
`O_{D,x}` (`06LN`)."

* `algebraMap_mem_nonZeroDivisors_localColimit` : flatness (any `R`, any `Ω`);
* `quotient_localColimit_isRegularLocalRing`, `quotient_span_localColimit_isRegularLocalRing`,
  `quotient_span_localColimit_isRegularRing` : `R` local, `Ω` a separable closure of the residue
  field; via the proved `05WS` comparison `localQuotientBaseChangeAlgEquiv` and the `06LN`/`06LJ`
  regularity of `LocalColimit (R ⧸ I) Ω`.

**A3 (normalization commutes with `R → Rˢʰ`).**  Stacks `03GE` (Lemma 10.147.2) is the étale case.
`Rˢʰ` is a filtered colimit of étale `R`-algebras, and integral closure commutes with it:

* `exists_refinement_map_eq_zero_of_map_eq_zero` : vanishing in `Rˢʰ ⊗[R] B` happens at a stage;
* `localColimit_toIntegralClosure_bijective` : the comparison map is bijective;
* `localColimit_isIntegralClosure`, `localColimit_isIntegralClosure_localizationAway` : the
  `IsIntegralClosure` forms; the latter is exactly the `hnormalization` input of
  `strictStandardPresentation_of_localizedPresentation`.

The A3 results hold for any `R` and any `Ω`; no locality is needed.
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace Pcf.Stacks.PointedEtaleNeighborhood

section Divisor

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- A nonzerodivisor of the base stays a nonzerodivisor in the strict local colimit, because
`R → LocalColimit R Ω` is flat. -/
theorem algebraMap_mem_nonZeroDivisors_localColimit {a : R} (ha : a ∈ nonZeroDivisors R) :
    algebraMap R (LocalColimit R Ω) a ∈ nonZeroDivisors (LocalColimit R Ω) := by
  have : Module.Flat R (LocalColimit R Ω) := localColimit_flat (R := R) (Ω := Ω)
  have hreg : IsSMulRegular (LocalColimit R Ω) a :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors ha
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply hreg
  change a • x = a • 0
  rw [smul_zero, Algebra.smul_def, mul_comm, hx]

variable [IsLocalRing R]
  [Algebra (IsLocalRing.ResidueField R) Ω]
  [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
  [IsSepClosure (IsLocalRing.ResidueField R) Ω]

omit [IsSepClosure (IsLocalRing.ResidueField R) Ω] in
/-- The kernel of `R → Ω` is the maximal ideal of `R`. -/
theorem ker_algebraMap_eq_maximalIdeal :
    RingHom.ker (algebraMap R Ω) = IsLocalRing.maximalIdeal R := by
  ext r
  rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) Ω,
    map_eq_zero_iff _ (algebraMap (IsLocalRing.ResidueField R) Ω).injective,
    IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]

/-- The strict local colimit modulo a regular quotient of the base is a regular local ring:
`Rˢʰ ⧸ I Rˢʰ ≅ (R ⧸ I)ˢʰ` (`05WS`, `localQuotientBaseChangeAlgEquiv`) and the strict
henselization of a regular local ring is regular local
(`06LN`, `localColimit_isRegularLocalRing`). -/
theorem quotient_localColimit_isRegularLocalRing (I : Ideal R)
    [IsRegularLocalRing (R ⧸ I)] :
    IsRegularLocalRing (LocalColimit R Ω ⧸ I.map (algebraMap R (LocalColimit R Ω))) := by
  have hItop : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hI : I ≤ RingHom.ker (algebraMap R Ω) := by
    rw [ker_algebraMap_eq_maximalIdeal]
    exact IsLocalRing.le_maximalIdeal hItop
  let φ : R ⧸ I →ₐ[R] Ω := quotientLiftPoint I hI
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  have : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let e : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField (R ⧸ I) :=
    IsLocalRing.ResidueField.mapEquivOfSurjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let _ : Algebra (IsLocalRing.ResidueField (R ⧸ I)) Ω :=
    ((algebraMap (IsLocalRing.ResidueField R) Ω).comp e.symm.toRingHom).toAlgebra
  have he : ∀ r : R, e.symm (IsLocalRing.residue (R ⧸ I) (Ideal.Quotient.mk I r)) =
      IsLocalRing.residue R r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (IsLocalRing.ResidueField.map_residue _ r).symm
  have : IsScalarTower (R ⧸ I) (IsLocalRing.ResidueField (R ⧸ I)) Ω := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change φ (Ideal.Quotient.mk I r) = algebraMap (IsLocalRing.ResidueField R) Ω
      (e.symm (IsLocalRing.residue (R ⧸ I) (Ideal.Quotient.mk I r)))
    rw [he, quotientLiftPoint_mk, IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) Ω]
    rfl
  have : IsSepClosure (IsLocalRing.ResidueField (R ⧸ I)) Ω := by
    have hsc : IsSepClosure (IsLocalRing.ResidueField R) Ω := inferInstance
    refine ⟨hsc.sep_closed, ?_⟩
    have := hsc.separable
    exact Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl Ω) (by
      ext x
      change algebraMap (IsLocalRing.ResidueField R) Ω (e.symm (e x)) =
        algebraMap (IsLocalRing.ResidueField R) Ω x
      rw [RingEquiv.symm_apply_apply])
  have hreg : IsRegularLocalRing (LocalColimit (R ⧸ I) Ω) :=
    localColimit_isRegularLocalRing
  exact IsRegularLocalRing.of_ringEquiv
    (localQuotientBaseChangeAlgEquiv I φ).toRingEquiv.symm

/-- **A2.** The image of the divisor in the strict henselization cuts out a regular ring:
`Rˢʰ ⧸ (a)` is regular local (hence a regular ring) when `R ⧸ (a)` is regular local. -/
theorem quotient_span_localColimit_isRegularLocalRing (a : R)
    [IsRegularLocalRing (R ⧸ Ideal.span {a})] :
    IsRegularLocalRing (LocalColimit R Ω ⧸
      Ideal.span {algebraMap R (LocalColimit R Ω) a}) := by
  have := quotient_localColimit_isRegularLocalRing (Ω := Ω) (Ideal.span {a})
  rwa [Ideal.map_span, Set.image_singleton] at this

/-- **A2, the form consumed by `0EYG`.**  For `a` in the maximal ideal of the local ring `R`
with `R ⧸ (a)` a regular ring, `Rˢʰ ⧸ (a)` is a regular ring.  This is the
`[IsRegularRing (LocalColimit R Ω ⧸ (a))]` input of
`strictStandardPresentation_of_localizedPresentation`. -/
theorem quotient_span_localColimit_isRegularRing (a : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) [IsRegularRing (R ⧸ Ideal.span {a})] :
    IsRegularRing (LocalColimit R Ω ⧸
      Ideal.span {algebraMap R (LocalColimit R Ω) a}) := by
  have hne : Ideal.span {a} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal a).mp ha
  have : Nontrivial (R ⧸ Ideal.span {a}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ Ideal.span {a}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsRegularLocalRing (R ⧸ Ideal.span {a}) :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  have := quotient_span_localColimit_isRegularLocalRing (Ω := Ω) a
  exact isRegularRing_of_isRegularLocalRing _

end Divisor

section Normalization

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- Finitely many elements of a stage that vanish in the strict local colimit vanish together
at one further stage. -/
theorem exists_refinement_forall_eq_zero (X : PointedEtaleNeighborhood R Ω) (s : Finset X)
    (hs : ∀ x ∈ s, toLocalColimitAlgHom (R := R) (Ω := Ω) X x = 0) :
    ∃ (Y : PointedEtaleNeighborhood R Ω) (f : X ⟶ Y), ∀ x ∈ s, f.hom x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨X, 𝟙 X, by simp⟩
  | insert x s hxs ih =>
    obtain ⟨Y, f, hf⟩ := ih fun y hy ↦ hs y (Finset.mem_insert_of_mem hy)
    have hx : toLocalColimitAlgHom (R := R) (Ω := Ω) Y (f.hom x) = 0 := by
      rw [← hs x (Finset.mem_insert_self x s)]
      exact DFunLike.congr_fun (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) f) x
    obtain ⟨Z, g, hg⟩ :=
      exists_refinement_eq_zero_of_toLocalColimitAlgHom_eq_zero (R := R) (Ω := Ω) Y (f.hom x) hx
    refine ⟨Z, f ≫ g, fun y hy ↦ ?_⟩
    rw [comp_hom, AlgHom.comp_apply]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hg
    · rw [hf y hy, map_zero]

/-- Vanishing in `Rˢʰ ⊗[R] B` descends to a pointed étale stage.

This is the filtered-colimit form of `Rˢʰ ⊗[R] B = colim (A_λ ⊗[R] B)`, proved elementwise with
the equational criterion for vanishing and flatness of `R → Rˢʰ`. -/
theorem exists_refinement_map_eq_zero_of_map_eq_zero {B : Type u} [CommRing B] [Algebra R B]
    (X : PointedEtaleNeighborhood R Ω) (z : X ⊗[R] B)
    (hz : Algebra.TensorProduct.map (toLocalColimitAlgHom (R := R) (Ω := Ω) X)
      (AlgHom.id R B) z = 0) :
    ∃ (Y : PointedEtaleNeighborhood R Ω) (f : X ⟶ Y),
      Algebra.TensorProduct.map f.hom (AlgHom.id R B) z = 0 := by
  classical
  have : Module.Flat R (LocalColimit R Ω) := localColimit_flat (R := R) (Ω := Ω)
  obtain ⟨k, m, n, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  let φ := toLocalColimitAlgHom (R := R) (Ω := Ω) X
  have hsum : ∑ i, n i ⊗ₜ[R] φ (m i) = (0 : B ⊗[R] LocalColimit R Ω) := by
    have := congrArg (TensorProduct.comm R (LocalColimit R Ω) B) hz
    simpa [map_sum, φ] using this
  obtain ⟨l, a, y, hy, ha⟩ :=
    TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective R
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective) hsum
  obtain ⟨Z, hZ⟩ := exists_stage_containing_finite_localColimit_set (R := R) (Ω := Ω)
    (Set.range y) (Set.finite_range y)
  choose yZ hyZ using fun j : Fin l ↦ hZ (Set.mem_range_self j)
  obtain ⟨W, ⟨fX⟩, ⟨fZ⟩⟩ := exists_common_refinement (R := R) (Ω := Ω) X Z
  let e : Fin k → W := fun i ↦ fX.hom (m i) - ∑ j, a i j • fZ.hom (yZ j)
  have he : ∀ x ∈ Finset.univ.image e, toLocalColimitAlgHom (R := R) (Ω := Ω) W x = 0 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    have hX' := DFunLike.congr_fun (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) fX) (m i)
    have hZ' := fun j ↦
      DFunLike.congr_fun (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) fZ) (yZ j)
    simp only [AlgHom.comp_apply] at hX' hZ'
    simp only [e, map_sub, map_sum, map_smul, hX', hZ', hyZ]
    rw [sub_eq_zero]
    exact hy i
  obtain ⟨Y, g, hg⟩ := exists_refinement_forall_eq_zero W _ he
  refine ⟨Y, fX ≫ g, ?_⟩
  have hm : ∀ i, (fX ≫ g).hom (m i) = ∑ j, a i j • g.hom (fZ.hom (yZ j)) := by
    intro i
    have := hg (e i) (Finset.mem_image_of_mem e (Finset.mem_univ i))
    simp only [e, map_sub, map_sum, map_smul, sub_eq_zero] at this
    rw [comp_hom, AlgHom.comp_apply, this]
  have hvan : ∑ i, n i ⊗ₜ[R] (fX ≫ g).hom (m i) = (0 : B ⊗[R] Y) :=
    TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially R ⟨l, a, _, hm, ha⟩
  have := congrArg (TensorProduct.comm R B Y) hvan
  simpa [map_sum] using this

omit [Field Ω] [Algebra R Ω] in
/-- `TensorProduct.toIntegralClosure` is natural in the base-changed ring. -/
theorem toIntegralClosure_map_val {Y T B : Type u} [CommRing Y] [CommRing T] [CommRing B]
    [Algebra R Y] [Algebra R T] [Algebra R B] (g : Y →ₐ[R] T)
    (u : Y ⊗[R] integralClosure R B) :
    (TensorProduct.toIntegralClosure R T B
        (Algebra.TensorProduct.map g (AlgHom.id R _) u) : T ⊗[R] B) =
      Algebra.TensorProduct.map g (AlgHom.id R B)
        (TensorProduct.toIntegralClosure R Y B u : Y ⊗[R] B) := by
  induction u using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul y b => rfl

/-- **A3, comparison map.**  For every `R`-algebra `B`, the comparison
`Rˢʰ ⊗[R] (integral closure of R in B) → integral closure of Rˢʰ in Rˢʰ ⊗[R] B` is bijective:
integral closure commutes with the ind-étale base change `R → Rˢʰ`.

Proof: injectivity is flatness.  For surjectivity, an element integral over `Rˢʰ` and its
integral equation are defined over a pointed étale stage `A_λ`; the equation holds after a
further stage (`exists_refinement_map_eq_zero_of_map_eq_zero`), where Stacks `03GE` (étale,
hence smooth, base change; Mathlib's `toIntegralClosure_bijective_of_smooth`) applies. -/
theorem localColimit_toIntegralClosure_bijective (B : Type u) [CommRing B] [Algebra R B] :
    Function.Bijective
      (TensorProduct.toIntegralClosure R (LocalColimit R Ω) B) := by
  classical
  have : Module.Flat R (LocalColimit R Ω) := localColimit_flat (R := R) (Ω := Ω)
  refine ⟨TensorProduct.toIntegralClosure_injective_of_flat, ?_⟩
  rintro ⟨t, ht⟩
  obtain ⟨p, hpm, hp⟩ := ht
  obtain ⟨k, c, b, htsum⟩ := TensorProduct.exists_sum_tmul_eq t
  set n := p.natDegree
  let S : Set (LocalColimit R Ω) :=
    Set.range c ∪ Set.range (fun i : Fin n ↦ p.coeff i)
  obtain ⟨X, hX⟩ := exists_stage_containing_finite_localColimit_set (R := R) (Ω := Ω) S
    ((Set.finite_range c).union (Set.finite_range _))
  choose cX hcX using fun i : Fin k ↦ hX (Or.inl (Set.mem_range_self i))
  choose pX hpX using fun i : Fin n ↦ hX (Or.inr (Set.mem_range_self i))
  let φX := toLocalColimitAlgHom (R := R) (Ω := Ω) X
  let tX : X ⊗[R] B := ∑ i, cX i ⊗ₜ[R] b i
  let w : X ⊗[R] B := tX ^ n + ∑ i : Fin n, (pX i ⊗ₜ[R] (1 : B)) * tX ^ (i : ℕ)
  have htX : Algebra.TensorProduct.map φX (AlgHom.id R B) tX = t := by
    simp [tX, φX, hcX, htsum]
  have hw : Algebra.TensorProduct.map φX (AlgHom.id R B) w = 0 := by
    have hpsum := hpm.as_sum
    have h0 : Polynomial.eval₂ (algebraMap (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] B)) t p
        = 0 := hp
    rw [hpsum, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum,
      ← Fin.sum_univ_eq_sum_range (fun i ↦ Polynomial.eval₂ _ t
        (Polynomial.C (p.coeff i) * Polynomial.X ^ i))] at h0
    simp only [Polynomial.eval₂_X_pow, Polynomial.eval₂_mul, Polynomial.eval₂_C] at h0
    rw [← h0]
    simp only [w, map_add, map_pow, map_sum, map_mul, htX]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    rw [← hpX i]
    rfl
  obtain ⟨Y, f, hf⟩ := exists_refinement_map_eq_zero_of_map_eq_zero X w hw
  let Φf := Algebra.TensorProduct.map f.hom (AlgHom.id R B)
  let tY := Φf tX
  let pY : Polynomial Y := Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (f.hom (pX i)) *
    Polynomial.X ^ (i : ℕ)
  have hpY : pY.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hintY : IsIntegral Y tY := by
    refine ⟨pY, hpY, ?_⟩
    rw [← hf]
    simp only [pY, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_X_pow]
    simp only [w, map_add, map_pow, map_sum, map_mul, tY]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.eval₂_monomial]
    rfl
  obtain ⟨u, hu⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := Y) (B := B)).2 ⟨tY, hintY⟩
  refine ⟨Algebra.TensorProduct.map (toLocalColimitAlgHom (R := R) (Ω := Ω) Y) (AlgHom.id R _) u,
    Subtype.ext ?_⟩
  rw [toIntegralClosure_map_val, hu]
  change Algebra.TensorProduct.map (toLocalColimitAlgHom (R := R) (Ω := Ω) Y) (AlgHom.id R B)
    (Φf tX) = t
  rw [← htX, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
    toLocalColimitAlgHom_naturality, AlgHom.comp_id]

section IntegralClosure

variable {N B : Type u} [CommRing N] [CommRing B]
variable [Algebra R N] [Algebra R B] [Algebra N B] [IsScalarTower R N B]
variable [IsIntegralClosure N R B]

attribute [local instance] normalizationBaseChangeAlgebra

/-- Ind-étale base change of an integral closure is canonically the integral closure after base
change (Stacks `03GE` for the filtered colimit `R → Rˢʰ` of étale algebras). -/
noncomputable def localColimitIntegralClosureEquiv :
    LocalColimit R Ω ⊗[R] N ≃ₐ[LocalColimit R Ω]
      integralClosure (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] B) :=
  (Algebra.TensorProduct.congr (.refl (R := LocalColimit R Ω) (A₁ := LocalColimit R Ω))
    (IsIntegralClosure.equiv R N B (integralClosure R B))).trans
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R (LocalColimit R Ω) B)
      (localColimit_toIntegralClosure_bijective B))

/-- The comparison equivalence commutes with the canonical maps into `Rˢʰ ⊗[R] B`. -/
theorem localColimitIntegralClosureEquiv_val (x : LocalColimit R Ω ⊗[R] N) :
    ((localColimitIntegralClosureEquiv (R := R) (Ω := Ω) (N := N) (B := B) x :
      integralClosure (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] B)) :
        LocalColimit R Ω ⊗[R] B) =
      algebraMap (LocalColimit R Ω ⊗[R] N) (LocalColimit R Ω ⊗[R] B) x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul x y =>
      change x ⊗ₜ[R] ((IsIntegralClosure.equiv R N B (integralClosure R B) y :
          integralClosure R B) : B) =
        (Algebra.TensorProduct.map (AlgHom.id (LocalColimit R Ω) (LocalColimit R Ω))
          (IsScalarTower.toAlgHom R N B)) (x ⊗ₜ[R] y)
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact congrArg (fun z : B => x ⊗ₜ[R] z)
        (IsIntegralClosure.algebraMap_equiv R N B (integralClosure R B) y)

/-- **A3.** If `N` is the integral closure of `R` in `B`, then `Rˢʰ ⊗[R] N` is the integral
closure of `Rˢʰ` in `Rˢʰ ⊗[R] B`.

Stacks `03GE` (Lemma 10.147.2) is the étale case; this is its extension to the filtered
colimit of pointed étale neighbourhoods defining `Rˢʰ`. -/
theorem localColimit_isIntegralClosure :
    IsIntegralClosure (LocalColimit R Ω ⊗[R] N) (LocalColimit R Ω)
      (LocalColimit R Ω ⊗[R] B) := by
  let e := localColimitIntegralClosureEquiv (R := R) (Ω := Ω) (N := N) (B := B)
  constructor
  · intro x y hxy
    apply e.injective
    apply Subtype.ext
    rw [localColimitIntegralClosureEquiv_val, localColimitIntegralClosureEquiv_val, hxy]
  · intro x
    constructor
    · intro hx
      let z : integralClosure (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] B) := ⟨x, hx⟩
      refine ⟨e.symm z, ?_⟩
      rw [← localColimitIntegralClosureEquiv_val]
      simp [e, z]
    · rintro ⟨y, rfl⟩
      rw [← localColimitIntegralClosureEquiv_val]
      exact (e y).2

end IntegralClosure

/-- **A3, the form consumed by `0EYG`.**  If `S` is the normalization of `R` in `S[1/a]`, then
`Rˢʰ ⊗[R] S` is the normalization of `Rˢʰ` in `(Rˢʰ ⊗[R] S)[1/a]`.

This is exactly the `hnormalization` hypothesis of
`strictStandardPresentation_of_localizedPresentation`. -/
theorem localColimit_isIntegralClosure_localizationAway
    {S : Type u} [CommRing S] [Algebra R S] (a : R)
    [IsIntegralClosure S R (Localization.Away (algebraMap R S a))] :
    IsIntegralClosure (LocalColimit R Ω ⊗[R] S) (LocalColimit R Ω)
      (Localization.Away
        (algebraMap (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] S)
          (algebraMap R (LocalColimit R Ω) a))) := by
  let R' := LocalColimit R Ω
  let B := Localization.Away (algebraMap R S a)
  let T := R' ⊗[R] S
  let _ : Algebra T (R' ⊗[R] B) :=
    normalizationBaseChangeAlgebra (R := R) (R' := R') (N := S) (B := B)
  have hIC : IsIntegralClosure T R' (R' ⊗[R] B) :=
    localColimit_isIntegralClosure (R := R) (Ω := Ω) (N := S) (B := B)
  let _ : IsIntegralClosure T R' (R' ⊗[R] B) := hIC
  let F : R' ⊗[R] B ≃ₐ[R'] Localization.Away ((1 : R') ⊗ₜ[R] algebraMap R S a) :=
    IsLocalization.Away.tensorProductEquivTMulRight R R' (algebraMap R S a) B
  have hbase : (1 : R') ⊗ₜ[R] algebraMap R S a = algebraMap R' T (algebraMap R R' a) := by
    change (1 : R') ⊗ₜ[R] algebraMap R S a = algebraMap R R' a ⊗ₜ[R] (1 : S)
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul a).symm
  rw [← hbase]
  apply IsIntegralClosure.of_algEquiv T F
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      change algebraMap T (Localization.Away ((1 : R') ⊗ₜ[R] algebraMap R S a)) (x ⊗ₜ[R] y) =
        F ((Algebra.TensorProduct.map (AlgHom.id R' R')
          (IsScalarTower.toAlgHom R S B)) (x ⊗ₜ[R] y))
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact (IsLocalization.Away.tensorProductEquivTMulRight_tmul
        (R := R) (S := R') S (algebraMap R S a) B x y).symm

end Normalization

end Pcf.Stacks.PointedEtaleNeighborhood
