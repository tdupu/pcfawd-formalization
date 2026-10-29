/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossProductSections
public import Pcf.Examples.PaperP.MonodromyLossProductIntegral

/-!
# The slices `E × {0}`, `E × {∞}` and the restriction `F²|_{E×{0}}` (`ex:monodromy-loss`)

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: "`F` swaps `E × {0}` and `E × {∞}`" and
"The return is covered by the degree-4 map `F²|_{E×{0}}`, whose monodromy is prime to 3".

* `slice c : E ⟶ E ×ₖ ℙ¹`, `P ↦ (P, c)` for a `k`-point `c` of `ℙ¹`; it is a closed immersion
  (`slice_isClosedImmersion`, a section of the separated projection) and the base change of
  `c : Spec k ⟶ ℙ¹` along `pr₂` (`slice_isPullback`). `slice0 = E × {0}`, `sliceInf = E × {∞}`.
* **`slice0_bigF`**, **`sliceInf_bigF`**: `F` maps `E × {0}` to `E × {∞}` and back, covering `φ`.
* **`bigFSq_slice0_isPullback`**: the base change of `F²` along `E × {0} ↪ E ×ₖ ℙ¹` is `φ²`,
  i.e. `F²|_{E×{0}} = φ²`.
* `bigF_isDominant`: `F` is dominant.
* **`bigFSq_restrict_zero`**: hence `F²|_{E×{0}}` is (`φ²`, which is) finite of generic degree 4
  with prime-to-3 monodromy.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial

namespace Pcf.Examples.PaperP.MonodromyLossProductSlices

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossProductSections
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Slices

variable (k : Type u) [Field k]

local notation "P1" => Proj (grading k)
local notation "str" => BasilicaProjectiveScheme.structureMap k

/-- The coordinate points of `ℙ¹` are sections of `ℙ¹ → Spec k`. -/
theorem pointP1_structureMap (j : Index) (x : Index → k)
    (h : IsUnit (aeval x (X j : Coordinates k))) : pointP1 k j x h ≫ str = 𝟙 _ := by
  rw [pointP1, BasilicaProjectiveScheme.structureMap, Category.assoc,
    ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero, ← Spec.map_comp,
    ← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact awayEval_kAway (X j) x h c

theorem zeroPt_structureMap : zeroPt k ≫ str = 𝟙 _ := pointP1_structureMap k _ _ _
theorem infPt_structureMap : infPt k ≫ str = 𝟙 _ := pointP1_structureMap k _ _ _

/-- The slice `E × {c} ⟶ E ×ₖ ℙ¹`, `P ↦ (P, c)`. -/
noncomputable def slice (c : Spec (.of k) ⟶ P1) (hc : c ≫ str = 𝟙 _) : E k ⟶ EP1 k :=
  pullback.lift (𝟙 _) (toSpec k ≫ c) (by rw [Category.assoc, hc]; simp)

@[reassoc (attr := simp)] theorem slice_fst (c : Spec (.of k) ⟶ P1) (hc : c ≫ str = 𝟙 _) :
    slice k c hc ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem slice_snd (c : Spec (.of k) ⟶ P1) (hc : c ≫ str = 𝟙 _) :
    slice k c hc ≫ pullback.snd _ _ = toSpec k ≫ c := pullback.lift_snd _ _ _

instance structureMap_isSeparated : IsSeparated str := by
  unfold BasilicaProjectiveScheme.structureMap
  infer_instance

/-- **The slice is a closed immersion** (a section of the separated `pr₁`). -/
instance slice_isClosedImmersion (c : Spec (.of k) ⟶ P1) (hc : c ≫ str = 𝟙 _) :
    IsClosedImmersion (slice k c hc) := by
  have : IsSeparated (pullback.fst (toSpec k) str) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : IsClosedImmersion (slice k c hc ≫ pullback.fst (toSpec k) str) := by
    rw [slice_fst]; infer_instance
  exact IsClosedImmersion.of_comp (slice k c hc) (pullback.fst (toSpec k) str)

/-- **`E × {c}` is the base change of `c : Spec k ⟶ ℙ¹` along `pr₂`.** -/
theorem slice_isPullback (c : Spec (.of k) ⟶ P1) (hc : c ≫ str = 𝟙 _) :
    IsPullback (toSpec k) (slice k c hc) c (pullback.snd (toSpec k) str) := by
  refine IsPullback.of_bot (h₃₁ := toSpec k) (v₂₁ := pullback.fst (toSpec k) str)
    (v₂₂ := str) ?_ (by rw [slice_snd]) (IsPullback.of_hasPullback (toSpec k) str).flip
  rw [slice_fst, hc]
  exact IsPullback.of_id_fst.flip

/-- `E × {0}`. -/
noncomputable abbrev slice0 : E k ⟶ EP1 k := slice k (zeroPt k) (zeroPt_structureMap k)

/-- `E × {∞}`. -/
noncomputable abbrev sliceInf : E k ⟶ EP1 k := slice k (infPt k) (infPt_structureMap k)

end Slices

section BigF

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

theorem slice_bigF (c c' : Spec (.of k) ⟶ Proj (grading k))
    (hc : c ≫ BasilicaProjectiveScheme.structureMap k = 𝟙 _)
    (hc' : c' ≫ BasilicaProjectiveScheme.structureMap k = 𝟙 _) (h : c ≫ inv k = c') :
    slice k c hc ≫ bigF k i hi = phi k i hi ≫ slice k c' hc' := by
  apply pullback.hom_ext
  · rw [Category.assoc, bigF_fst, slice_fst_assoc, Category.assoc, slice_fst, Category.comp_id]
  · rw [Category.assoc, bigF_snd, slice_snd_assoc, Category.assoc, slice_snd, h,
      ← Category.assoc, phi_toSpec]

/-- **`F` maps `E × {0}` to `E × {∞}`, covering `φ`.** -/
theorem slice0_bigF : slice0 k ≫ bigF k i hi = phi k i hi ≫ sliceInf k :=
  slice_bigF k i hi _ _ _ _ (zeroPt_inv k)

/-- **`F` maps `E × {∞}` to `E × {0}`, covering `φ`.** -/
theorem sliceInf_bigF : sliceInf k ≫ bigF k i hi = phi k i hi ≫ slice0 k :=
  slice_bigF k i hi _ _ _ _ (infPt_inv k)

/-- `F²` maps `E × {0}` to itself, covering `φ²`. -/
theorem slice0_bigFSq : slice0 k ≫ bigF k i hi ≫ bigF k i hi = phiSq k i hi ≫ slice0 k := by
  rw [← Category.assoc, slice0_bigF, Category.assoc, sliceInf_bigF, ← Category.assoc]

theorem bigFSq_snd : (bigF k i hi ≫ bigF k i hi) ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [Category.assoc, bigF_snd, ← Category.assoc, bigF_snd, Category.assoc, inv_inv,
    Category.comp_id]

/-- **`F²|_{E×{0}} = φ²`**: the base change of `F²` along `E × {0} ↪ E ×ₖ ℙ¹` is `φ²`. -/
theorem bigFSq_slice0_isPullback :
    IsPullback (phiSq k i hi) (slice0 k) (slice0 k) (bigF k i hi ≫ bigF k i hi) := by
  refine IsPullback.of_right (h₁₂ := toSpec k) (h₂₂ := pullback.snd _ _) (v₁₃ := zeroPt k) ?_
    (slice0_bigFSq k i hi).symm (slice_isPullback k _ _)
  have e : phiSq k i hi ≫ toSpec k = toSpec k := by
    rw [Category.assoc, phi_toSpec, phi_toSpec]
  rw [e, bigFSq_snd]
  exact slice_isPullback k _ _

/-- **The restriction `F²|_{E×{0}}`**: it is the base change `φ²` of `F²` along the closed
immersion `E × {0} ↪ E ×ₖ ℙ¹`, finite, of generic degree 4, with prime-to-3 monodromy.

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem bigFSq_restrict_zero :
    IsClosedImmersion (slice0 k) ∧
    IsPullback (phiSq k i hi) (slice0 k) (slice0 k) (bigF k i hi ≫ bigF k i hi) ∧
    IsFinite (phiSq k i hi) ∧
    (letI := ((phiSq k i hi).stalkMap (genericPoint (E k))).hom.toAlgebra;
      Module.finrank ((E k).presheaf.stalk (phiSq k i hi (genericPoint (E k))))
        ((E k).presheaf.stalk (genericPoint (E k))) = 4) ∧
    Pcf.IsPrimeToPMonodromyMap 3 (phiSq k i hi) :=
  ⟨inferInstance, bigFSq_slice0_isPullback k i hi, inferInstance, phiSq_genericDegree k i hi,
    phiSq_isPrimeToThreeMonodromy k i hi⟩

/-- **`F` is dominant** (étale, hence open, onto a nonempty open of the irreducible `E ×ₖ ℙ¹`). -/
instance bigF_isDominant : IsDominant (bigF k i hi) := by
  constructor
  have hne : (Set.range (bigF k i hi)).Nonempty :=
    ⟨_, genericPoint (EP1 k), rfl⟩
  exact ((bigF k i hi).isOpenMap.isOpen_range).dense hne

end BigF

#print axioms slice_isClosedImmersion
#print axioms slice_isPullback
#print axioms slice0_bigF
#print axioms sliceInf_bigF
#print axioms bigFSq_slice0_isPullback
#print axioms bigFSq_restrict_zero
#print axioms bigF_isDominant

end Pcf.Examples.PaperP.MonodromyLossProductSlices
