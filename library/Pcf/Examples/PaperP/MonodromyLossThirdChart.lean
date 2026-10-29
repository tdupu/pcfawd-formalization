/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossProduct
public import Pcf.Examples.PaperP.MonodromyLossYFinite
public import Pcf.Examples.PaperP.MonodromyLossPinchCharts

/-!
# The affine open `(y ∘ φ)⁻¹(D₊(u))` of `E` (`ex:monodromy-loss`, third pinching chart)

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: the pinching of `E × {∞}` needs an affine
chart of `E` saturated for `y ∘ φ` near `∞ ∈ ℙ¹`. This is `U∞ = (y ∘ φ)⁻¹(D₊(u)) = φ⁻¹(U_B)`.

* `UInf := pullback φ ιB` (`φ⁻¹(U_B)` as a scheme), with the open immersion
  `UInfι = pullback.fst : UInf ⟶ E`, `UInfι_opensRange` (its image is `(φ ≫ y)⁻¹ D₊(u)`),
  **`UInf_isAffine`**.
* `psiInf : B → Γ(UInf)` (pullback of functions along `φ : UInf → Spec B`), **`psiInf_finite`**,
  `UInf_snd_eq` (the map `UInf → Spec B` is `Spec psiInf` under `UInf ≅ Spec Γ(UInf)`).
* **`wInf : k[w] → Γ(UInf)`**, `wInf_X` (the function `w ∘ φ`), **`wInf_finite`**.
* `UInfι_comp_yMap`: on `UInf`, `y ∘ φ` factors as `Spec k[u,v]_{(u)} → D₊(u) ⊂ ℙ¹`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial

namespace Pcf.Examples.PaperP.MonodromyLossThirdChart

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossPinch
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

local notation "uu" => (X (Sum.inl 0) : Coordinates k)

/-- `U∞ = φ⁻¹(U_B)`, as the pullback of `ιB` along `φ`. -/
noncomputable abbrev UInf : Scheme.{u} := pullback (phi k i hi) (ιB k)

/-- The open immersion `U∞ ⟶ E`. -/
noncomputable abbrev UInfι : UInf k i hi ⟶ E k := pullback.fst (phi k i hi) (ιB k)

instance UInf_isAffine : IsAffine (UInf k i hi) := inferInstance

theorem UInfι_opensRange :
    (UInfι k i hi).opensRange =
      (phi k i hi ≫ yMap k) ⁻¹ᵁ
        (Proj.awayι (grading k) uu (uu_mem k) Nat.zero_lt_one).opensRange := by
  ext x
  rw [Scheme.Hom.comp_preimage, yMap_preimage_u]
  change x ∈ Set.range (pullback.fst (phi k i hi) (ιB k)) ↔ _
  rw [Scheme.Pullback.range_fst]
  rfl

/-- Pullback of functions `B → Γ(U∞)` along `φ : U∞ → U_B = Spec B`. -/
noncomputable def psiInf : B k →+* Γ(UInf k i hi, ⊤) :=
  (pullback.snd (phi k i hi) (ιB k)).appTop.hom.comp (Scheme.ΓSpecIso (.of (B k))).inv.hom

/-- **`Γ(U∞)` is finite over `B`.** -/
theorem psiInf_finite : (psiInf k i hi).Finite := by
  have h1 := Scheme.Hom.finite_appTop (pullback.snd (phi k i hi) (ιB k))
  have h2 : (Scheme.ΓSpecIso (.of (B k))).inv.hom.Finite :=
    RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (B k))).inv).2
  exact h1.comp h2

theorem UInf_snd_eq : pullback.snd (phi k i hi) (ιB k) =
    (UInf k i hi).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (psiInf k i hi)) := by
  have e : CommRingCat.ofHom (psiInf k i hi) =
      (Scheme.ΓSpecIso (.of (B k))).inv ≫ (pullback.snd (phi k i hi) (ιB k)).appTop := rfl
  rw [e, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
    Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- **The coordinate `w ∘ φ` on `U∞`**: `k[w] → Γ(U∞)`. -/
noncomputable def wInf : Polynomial k →+* Γ(UInf k i hi, ⊤) :=
  (psiInf k i hi).comp (betaB k)

theorem wInf_X : wInf k i hi Polynomial.X = psiInf k i hi (wB k) := rfl

/-- **`Γ(U∞)` is finite over `k[w]`.** -/
theorem wInf_finite : (wInf k i hi).Finite :=
  (psiInf_finite k i hi).comp (betaB_finite k)

/-- On `U∞`, `y ∘ φ` lands in `D₊(u)` through the chart `Spec B → Spec k[u,v]_{(u)}`. -/
theorem UInfι_comp_yMap : UInfι k i hi ≫ phi k i hi ≫ yMap k =
    pullback.snd (phi k i hi) (ιB k) ≫
      Spec.map (CommRingCat.ofHom (awayEval uu (valsB k) (valsB_u k))) ≫
        Proj.awayι (grading k) uu (uu_mem k) Nat.zero_lt_one := by
  rw [← Category.assoc, pullback.condition, Category.assoc, ιB_yMap]
  rfl

#print axioms UInfι_opensRange
#print axioms psiInf_finite
#print axioms UInf_snd_eq
#print axioms wInf_finite
#print axioms UInfι_comp_yMap

end Pcf.Examples.PaperP.MonodromyLossThirdChart
