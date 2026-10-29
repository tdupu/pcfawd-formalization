/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossProductGalois
public import Pcf.Examples.PaperP.MonodromyLossProductSlices
public import Pcf.Bounding.PrimeToPMonodromyOpenSquare
public import Pcf.Bounding.GenericStalkMonodromyTransport

/-!
# `F` has generic degree 2 and prime-to-3 monodromy (`ex:monodromy-loss`)

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: "`F(P,z) = (φ(P), 1/z)` is an étale
degree-2 self-map of `E × ℙ¹`".

* `chartRP ι₀ c : Spec R₀[T] ⟶ E ×ₖ ℙ¹`: the product of an open chart `ι₀ : Spec R₀ → E` with an
  open chart `c : 𝔸¹ → ℙ¹` (through `Spec R₀[T] = Spec R₀ ×ₖ 𝔸¹`, Mathlib `Algebra.IsPushout`);
  it is an open immersion.
* `alphaF` (`D(x) × D₊(v)`), `betaF` (`U_A × inv(D₊(v))`), **`square_bigF`**:
  `Spec psi ≫ betaF = alphaF ≫ F`, with `psi = phi1[T]`.
* `psi_finite`: by base change of `phi1` (`RingHom.finite_isStableUnderBaseChange`).
* `SpecPsi_galois`, `SpecPsi_isPrimeToPMonodromyMap`.
* **`bigF_genericDegree`** (`= 2`) and **`bigF_isPrimeToPMonodromyMap`** (`p ≠ 2`), in
  particular **`bigF_isPrimeToThreeMonodromy`**.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.MonodromyLossProductDegree

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossProductIntegral Pcf.Examples.PaperP.MonodromyLossProductGalois
open Pcf.Examples.PaperP.MonodromyLossProductSections
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

universe u

section Charts

variable (k : Type u) [Field k]

local notation "str" => BasilicaProjectiveScheme.structureMap k

variable (R₀ : Type u) [CommRing R₀] [Algebra k R₀]

/-- `Spec R₀[T] = Spec R₀ ×ₖ 𝔸¹`. -/
theorem isPullback_poly : IsPullback
    (Spec.map (CommRingCat.ofHom (algebraMap R₀ (MvPolynomial (Fin 1) R₀))))
    (Spec.map (CommRingCat.ofHom (algebraMap (Poly k) (MvPolynomial (Fin 1) R₀))))
    (Spec.map (CommRingCat.ofHom (algebraMap k R₀))) (A1toSpec k) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout k R₀ (Poly k) (MvPolynomial (Fin 1) R₀))

variable {R₀}

/-- The product chart `Spec R₀[T] ⟶ E ×ₖ ℙ¹`. -/
noncomputable def chartRP (ι₀ : Spec (.of R₀) ⟶ E k)
    (h₀ : Spec.map (CommRingCat.ofHom (algebraMap k R₀)) = ι₀ ≫ toSpec k)
    (c : Spec (.of (Poly k)) ⟶ Proj (grading k)) (hc : A1toSpec k = c ≫ str) :
    Spec (.of (MvPolynomial (Fin 1) R₀)) ⟶ EP1 k :=
  (isPullback_poly k R₀).isoPullback.hom ≫
    pullback.map _ _ (toSpec k) str ι₀ c (𝟙 _) ((Category.comp_id _).trans h₀)
      ((Category.comp_id _).trans hc)

instance chartRP_isOpenImmersion (ι₀ : Spec (.of R₀) ⟶ E k) [IsOpenImmersion ι₀]
    (h₀ : Spec.map (CommRingCat.ofHom (algebraMap k R₀)) = ι₀ ≫ toSpec k)
    (c : Spec (.of (Poly k)) ⟶ Proj (grading k)) [IsOpenImmersion c]
    (hc : A1toSpec k = c ≫ str) : IsOpenImmersion (chartRP k ι₀ h₀ c hc) := by
  have := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion ι₀) (inferInstance : IsOpenImmersion c) h₀ hc
  unfold chartRP
  infer_instance

@[reassoc] theorem chartRP_fst (ι₀ : Spec (.of R₀) ⟶ E k)
    (h₀ : Spec.map (CommRingCat.ofHom (algebraMap k R₀)) = ι₀ ≫ toSpec k)
    (c : Spec (.of (Poly k)) ⟶ Proj (grading k)) (hc : A1toSpec k = c ≫ str) :
    chartRP k ι₀ h₀ c hc ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap R₀ (MvPolynomial (Fin 1) R₀))) ≫ ι₀ := by
  rw [chartRP, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc]

@[reassoc] theorem chartRP_snd (ι₀ : Spec (.of R₀) ⟶ E k)
    (h₀ : Spec.map (CommRingCat.ofHom (algebraMap k R₀)) = ι₀ ≫ toSpec k)
    (c : Spec (.of (Poly k)) ⟶ Proj (grading k)) (hc : A1toSpec k = c ≫ str) :
    chartRP k ι₀ h₀ c hc ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap (Poly k) (MvPolynomial (Fin 1) R₀))) ≫ c := by
  rw [chartRP, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc]

instance inv_isIso : IsIso (inv k) := ⟨⟨inv k, inv_inv k, inv_inv k⟩⟩

end Charts

section Square

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

local notation "str" => BasilicaProjectiveScheme.structureMap k

omit [CharP k 3] in
theorem chartDx_toSpec : Spec.map (CommRingCat.ofHom (algebraMap k (Ax k))) =
    chartDx k ≫ toSpec k := by
  rw [chartDx, Category.assoc, ιA_toSpec, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq k (A k) (Ax k))

/-- The source chart `D(x) × D₊(v) ⟶ E ×ₖ ℙ¹`. -/
noncomputable def alphaF : Spec (.of (PAx k)) ⟶ EP1 k :=
  chartRP k (chartDx k) (chartDx_toSpec k) (chartP1 k (Equiv.refl _))
    (chartP1_structureMap k _).symm

omit [CharP k 3] in
theorem chart_inv_structureMap :
    A1toSpec k = (chartP1 k (Equiv.refl _) ≫ inv k) ≫ str := by
  rw [Category.assoc, inv_toSpec, chartP1_structureMap]

/-- The target chart `U_A × inv(D₊(v)) ⟶ E ×ₖ ℙ¹`. -/
noncomputable def betaF : Spec (.of (PA k)) ⟶ EP1 k :=
  chartRP k (ιA k) (ιA_toSpec k).symm (chartP1 k (Equiv.refl _) ≫ inv k)
    (chart_inv_structureMap k)

instance alphaF_isOpenImmersion : IsOpenImmersion (alphaF k) := by
  unfold alphaF; infer_instance

instance betaF_isOpenImmersion : IsOpenImmersion (betaF k) := by
  unfold betaF; infer_instance

/-- `Spec psi`. -/
noncomputable abbrev SpecPsi : Spec (.of (PAx k)) ⟶ Spec (.of (PA k)) :=
  Spec.map (CommRingCat.ofHom (psi k i hi))

/-- **Over the chart `D(x) × D₊(v)`, `F` is `Spec psi`.** -/
theorem square_bigF : SpecPsi k i hi ≫ betaF k = alphaF k ≫ bigF k i hi := by
  apply pullback.hom_ext
  · rw [Category.assoc, betaF, chartRP_fst, Category.assoc, bigF_fst, alphaF, chartRP_fst_assoc,
      ← square_phi, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change psi k i hi (MvPolynomial.C a) = MvPolynomial.C (phi1 k i hi a)
    simp [psi]
  · rw [Category.assoc, betaF, chartRP_snd, Category.assoc, bigF_snd, alphaF, chartRP_snd_assoc,
      ← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        MvPolynomial.algebraMap_def, psi, MvPolynomial.map_C, phi1_algebraMap]
    · intro n
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        MvPolynomial.algebraMap_def, psi, MvPolynomial.map_X]

end Square

section Monodromy

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

include hi in
/-- **`psi = phi1[T]` is finite** (base change of the finite `phi1`). -/
theorem psi_finite : (psi k i hi).Finite := by
  have h : (algebraMap (A k) (AxPhi k i hi)).Finite := phi1_finite k i hi
  have := RingHom.finite_isStableUnderBaseChange (A k) (AxPhi k i hi)
    (MvPolynomial (Fin 1) (A k)) (MvPolynomial (Fin 1) (AxPhi k i hi)) h
  rw [MvPolynomial.algebraMap_def] at this
  exact this

instance SpecPsi_isFinite : IsFinite (SpecPsi k i hi) := by
  rw [IsFinite.SpecMap_iff]; exact psi_finite k i hi

theorem SpecPsi_genericPoint_asIdeal :
    (SpecPsi k i hi (genericPoint (Spec (.of (PAx k))))).asIdeal = ⊥ := by
  change ((genericPoint (Spec (.of (PAx k)))).asIdeal).comap (psi k i hi) = ⊥
  rw [genericPoint_asIdeal_Spec]
  ext a
  simp only [Ideal.mem_comap, Ideal.mem_bot]
  exact ⟨fun h => psi_injective k i hi (h.trans (map_zero _).symm), fun h => by simp [h]⟩

instance SpecPsi_isDominant : IsDominant (SpecPsi k i hi) := by
  constructor
  have hg : SpecPsi k i hi (genericPoint (Spec (.of (PAx k)))) =
      genericPoint (Spec (.of (PA k))) := by
    apply PrimeSpectrum.ext
    rw [SpecPsi_genericPoint_asIdeal, genericPoint_asIdeal_Spec]
  refine Dense.mono (s₁ := {genericPoint (Spec (.of (PA k)))}) ?_ ?_
  · rintro _ rfl; exact ⟨_, hg⟩
  · rw [dense_iff_closure_eq]; exact genericPoint_spec (Spec (.of (PA k))) |>.def

/-- **The generic stalk extension of `Spec psi` is Galois of degree 2.** -/
theorem SpecPsi_galois
    (hF : IsField ((Spec (.of (PA k))).presheaf.stalk
      (SpecPsi k i hi (genericPoint (Spec (.of (PAx k))))))) :
    letI := hF.toField
    letI := ((SpecPsi k i hi).stalkMap (genericPoint (Spec (.of (PAx k))))).hom.toAlgebra
    IsGalois ((Spec (.of (PA k))).presheaf.stalk
        (SpecPsi k i hi (genericPoint (Spec (.of (PAx k))))))
      ((Spec (.of (PAx k))).presheaf.stalk (genericPoint (Spec (.of (PAx k))))) ∧
    Module.finrank ((Spec (.of (PA k))).presheaf.stalk
        (SpecPsi k i hi (genericPoint (Spec (.of (PAx k))))))
      ((Spec (.of (PAx k))).presheaf.stalk (genericPoint (Spec (.of (PAx k))))) = 2 := by
  letI := hF.toField
  letI := ((SpecPsi k i hi).stalkMap (genericPoint (Spec (.of (PAx k))))).hom.toAlgebra
  refine galois_of_psi k i hi (stalkCoord _) (stalkCoord _)
    (stalkCoord_isFractionRing _ (SpecPsi_genericPoint_asIdeal k i hi))
    (stalkCoord_isFractionRing _ genericPoint_asIdeal_Spec) ?_
  apply RingHom.ext
  intro a
  exact SpecMap_stalkMap_stalkCoord (psi k i hi) _ a

/-- **`Spec psi` has prime-to-`p` monodromy** for every prime `p ≠ 2`. -/
theorem SpecPsi_isPrimeToPMonodromyMap (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Pcf.IsPrimeToPMonodromyMap p (SpecPsi k i hi) := by
  let X := Spec (.of (PAx k))
  let f := SpecPsi k i hi
  have hgp : f (genericPoint X) = genericPoint (Spec (.of (PA k))) :=
    Pcf.map_genericPoint_eq_of_isDominant f
  let e := ((Spec (.of (PA k))).presheaf.stalkCongr
    (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hF : IsField ((Spec (.of (PA k))).presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field ((Spec (.of (PA k))).presheaf.stalk (f (genericPoint X))) := hF.toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  change Pcf.IsPrimeToPMonodromy.{u, u, u} p
    ((Spec (.of (PA k))).presheaf.stalk (f (genericPoint X))) (X.presheaf.stalk (genericPoint X))
  obtain ⟨hgal, hfin⟩ := SpecPsi_galois k i hi hF
  haveI := hgal
  haveI : FiniteDimensional ((Spec (.of (PA k))).presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) := Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
  refine Pcf.isPrimeToPMonodromy_of_embedding_into_galois p _ _ _ (AlgHom.id _ _) ?_
  rw [hfin]
  exact (Nat.coprime_primes Nat.prime_two Fact.out).mpr hp2.symm

instance alphaF_isDominant : IsDominant (alphaF k) := by
  constructor
  have hne : (Set.range (alphaF k)).Nonempty := ⟨_, ⟨⊥, Ideal.isPrime_bot⟩, rfl⟩
  exact ((alphaF k).isOpenEmbedding.isOpenMap.isOpen_range).dense hne

/-- **`F` has generic degree 2.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem bigF_genericDegree :
    letI := ((bigF k i hi).stalkMap (genericPoint (EP1 k))).hom.toAlgebra
    Module.finrank ((EP1 k).presheaf.stalk (bigF k i hi (genericPoint (EP1 k))))
      ((EP1 k).presheaf.stalk (genericPoint (EP1 k))) = 2 := by
  have hz : alphaF k (genericPoint (Spec (.of (PAx k)))) = genericPoint (EP1 k) :=
    Pcf.map_genericPoint_eq_of_isDominant (alphaF k)
  obtain ⟨eE, eK, hcomm⟩ := Pcf.exists_stalkEquivs_of_square (SpecPsi k i hi) (alphaF k)
    (betaF k) (bigF k i hi) (square_bigF k i hi) (genericPoint _) hz
    (ConcreteCategory.bijective_of_isIso _) (ConcreteCategory.bijective_of_isIso _)
  letI := ((bigF k i hi).stalkMap (genericPoint (EP1 k))).hom.toAlgebra
  letI := ((SpecPsi k i hi).stalkMap (genericPoint (Spec (.of (PAx k))))).hom.toAlgebra
  let X := Spec (.of (PAx k))
  let f := SpecPsi k i hi
  have hgp : f (genericPoint X) = genericPoint (Spec (.of (PA k))) :=
    Pcf.map_genericPoint_eq_of_isDominant f
  let e := ((Spec (.of (PA k))).presheaf.stalkCongr
    (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hF : IsField ((Spec (.of (PA k))).presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  obtain ⟨-, hfin⟩ := SpecPsi_galois k i hi hF
  rw [Algebra.finrank_eq_of_equiv_equiv eK eE hcomm]
  exact hfin

/-- **`F` has prime-to-`p` monodromy** for every prime `p ≠ 2`. -/
theorem bigF_isPrimeToPMonodromyMap (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Pcf.IsPrimeToPMonodromyMap p (bigF k i hi) := by
  obtain ⟨eE, eK, hcomm⟩ := Pcf.exists_stalkEquivs_of_square (SpecPsi k i hi) (alphaF k)
    (betaF k) (bigF k i hi) (square_bigF k i hi) (genericPoint _)
    (Pcf.map_genericPoint_eq_of_isDominant (alphaF k))
    (ConcreteCategory.bijective_of_isIso _) (ConcreteCategory.bijective_of_isIso _)
  refine Pcf.isPrimeToPMonodromyMap_of_genericStalkEquivs p (SpecPsi k i hi) (bigF k i hi)
    eK.symm eE.symm ?_ (SpecPsi_isPrimeToPMonodromyMap k i hi p hp2)
  apply RingHom.ext
  intro y
  have := congrArg (fun φ => φ (eK.symm y)) hcomm
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply] at this
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [this, RingEquiv.symm_apply_apply]

/-- **`F` has prime-to-3 monodromy.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem bigF_isPrimeToThreeMonodromy : Pcf.IsPrimeToPMonodromyMap 3 (bigF k i hi) :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  bigF_isPrimeToPMonodromyMap k i hi 3 (by decide)

end Monodromy

#print axioms square_bigF
#print axioms psi_finite
#print axioms bigF_genericDegree
#print axioms bigF_isPrimeToThreeMonodromy

end Pcf.Examples.PaperP.MonodromyLossProductDegree
