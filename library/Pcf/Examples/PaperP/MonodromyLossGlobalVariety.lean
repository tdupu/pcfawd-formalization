/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossGlobalX
public import Pcf.Examples.PaperP.TwoChartPinchFinite
public import Pcf.Examples.PaperP.FiniteCoverDescent
public import Pcf.Examples.PaperP.BasilicaProjectiveWeightedPCF

/-!
# The global pinched `X` of `ex:monodromy-loss` is a variety, and `ν` is finite

For `paper-p.tex`, Example `ex:monodromy-loss` (l. 846–868): "the resulting nonnormal variety
`X`".

* **`nu_isFinite`**: `ν : E ×ₖ ℙ¹ ⟶ X` is finite (chartwise `Spec pr₂`, `TwoChartPinchFinite`);
* `yMap_structureMap`: `y : E → ℙ¹` is a `k`-morphism;
* **`sX : X ⟶ Spec k`**, the structure morphism, from the pushout property `isPushoutX`, with
  `nu_sX : ν ≫ sX = (E ×ₖ ℙ¹ → Spec k)`;
* **`sX_locallyOfFiniteType`**, **`sX_quasiCompact`**, **`sX_isSeparated`**: `X` is separated and of
  finite type over `k` (descended along the finite surjective `ν`, `FiniteCoverDescent`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossProductIntegral Pcf.Examples.PaperP.MonodromyLossProductSlices
open Pcf.Examples.PaperP.MonodromyLossProductSections
open Pcf.Examples.PaperP.TwoChartPinch Pcf.Examples.PaperP.MonodromyLossPinchGlue
open Pcf.Examples.PaperP.MonodromyLossInf Pcf.Examples.PaperP.FerrandPushout
open Pcf.Examples.PaperP.MonodromyLossThirdChart
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

local notation "P1" => Proj (grading k)
local notation "str" => BasilicaProjectiveScheme.structureMap k

/-! ### `ν` is finite -/

instance D0_nu_isFinite : IsFinite (D0 k).nu :=
  (D0 k).nu_isFinite (awayEval_v_finite k) (awayEval_u_finite k)

instance Dinf_nu_isFinite : IsFinite (infData k i hi).nu :=
  (infData k i hi).nu_isFinite ((psiA_finite k i hi).comp (awayEval_v_finite k))
    ((psiInf_finite k i hi).comp (awayEval_u_finite k))

/-- **`ν : E ×ₖ ℙ¹ ⟶ X` is finite.** -/
instance nu_isFinite : IsFinite (nu k i hi) := by
  refine IsZariskiLocalAtTarget.of_openCover (TwoPieceGlue.openCover _ _) fun j => ?_
  rcases j with ⟨_ | _⟩
  · have h := isPullback_nu0 k i hi
    change IsFinite (pullback.snd (nu k i hi) (j0 k i hi))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @IsFinite]
    infer_instance
  · have h := isPullback_nuInf k i hi
    change IsFinite (pullback.snd (nu k i hi) (jInf k i hi))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @IsFinite]
    infer_instance

/-! ### The structure morphism -/

omit [CharP k 3] in
/-- A chart point `Spec T → D₊(X_j) ⊆ ℙ¹` is a `k`-morphism. -/
theorem awayChart_structureMap {T : Type u} [CommRing T] [Algebra k T] (j : Index) (x : Index → T)
    (h : IsUnit (aeval x (MvPolynomial.X j : Coordinates k))) :
    Spec.map (CommRingCat.ofHom (awayEval (MvPolynomial.X j) x h)) ≫
      Proj.awayι (grading k) (MvPolynomial.X j) (isHomogeneous_X k j) Nat.zero_lt_one ≫ str =
      Spec.map (CommRingCat.ofHom (algebraMap k T)) := by
  rw [BasilicaProjectiveScheme.structureMap, ← Category.assoc (Proj.awayι _ _ _ _),
    Proj.awayι_toSpecZero, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact awayEval_kAway (MvPolynomial.X j) x h c

omit [CharP k 3] in
/-- **`y : E → ℙ¹` is a morphism over `k`.** -/
theorem yMap_structureMap : yMap k ≫ str = toSpec k := by
  refine MonodromyLossCurve.hom_ext k ?_ ?_
  · rw [← Category.assoc, ιA_yMap, yChartA, Category.assoc, awayChart_structureMap, ιA_toSpec]
  · rw [← Category.assoc, ιB_yMap, yChartB, Category.assoc, awayChart_structureMap, ιB_toSpec]

/-- `E ×ₖ ℙ¹ → Spec k`. -/
noncomputable abbrev sEP : EP1 k ⟶ Spec (.of k) := pullback.fst _ _ ≫ toSpec k

/-- `ℙ¹ ⨿ ℙ¹ → Spec k`. -/
noncomputable abbrev sP : P1 ⨿ P1 ⟶ Spec (.of k) := coprod.desc str str

theorem sX_compat : iZ k ≫ sEP k = jZ k i hi ≫ sP k := by
  apply coprod.hom_ext
  · simp [iZ, jZ, yMap_structureMap]
  · simp [iZ, jZ, yMap_structureMap, phi_toSpec]

/-- **The structure morphism `X → Spec k`** (from the pushout property of `X`). -/
noncomputable def sX : X k i hi ⟶ Spec (.of k) :=
  (isPushoutX k i hi).desc (sEP k) (sP k) (sX_compat k i hi)

@[reassoc (attr := simp)] theorem nu_sX : nu k i hi ≫ sX k i hi = sEP k :=
  (isPushoutX k i hi).inl_desc _ _ _

@[reassoc (attr := simp)] theorem oX_sX : oX k i hi ≫ sX k i hi = sP k :=
  (isPushoutX k i hi).inr_desc _ _ _

/-! ### `X` is separated and of finite type over `k` -/

instance sEP_locallyOfFiniteType : LocallyOfFiniteType (sEP k) := by
  unfold sEP; infer_instance

instance sEP_isSeparated : IsSeparated (sEP k) := by
  unfold sEP; infer_instance

instance sEP_quasiCompact : QuasiCompact (sEP k) := by
  unfold sEP; infer_instance

/-- **`X` is locally of finite type over `k`.** -/
instance sX_locallyOfFiniteType : LocallyOfFiniteType (sX k i hi) := by
  haveI : LocallyOfFiniteType (nu k i hi ≫ sX k i hi) := by rw [nu_sX]; infer_instance
  exact FiniteCoverDescent.locallyOfFiniteType_of_finite_cover _ (nu k i hi)

/-- **`X` is separated over `k`.** -/
instance sX_isSeparated : IsSeparated (sX k i hi) := by
  haveI : IsSeparated (nu k i hi ≫ sX k i hi) := by rw [nu_sX]; infer_instance
  exact FiniteCoverDescent.isSeparated_of_surjective_universallyClosed _ (nu k i hi)

instance X_compactSpace : CompactSpace (X k i hi) := by
  haveI : CompactSpace (EP1 k) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := sEP k)).mp inferInstance
  refine ⟨?_⟩
  rw [← (nu k i hi).surjective.range_eq]
  exact isCompact_range (nu k i hi).continuous

/-- **`X` is quasi-compact over `k`** (so of finite type). -/
instance sX_quasiCompact : QuasiCompact (sX k i hi) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

#print axioms nu_isFinite
#print axioms sX_locallyOfFiniteType
#print axioms sX_isSeparated
#print axioms sX_quasiCompact

end Pcf.Examples.PaperP.MonodromyLossGlobal
