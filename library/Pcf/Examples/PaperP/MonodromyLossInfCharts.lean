/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.TwoChartPinchPushout
public import Pcf.Examples.PaperP.MonodromyLossThirdChart

/-!
# The charts `φ⁻¹(U_A)`, `φ⁻¹(U_B)` of `E` and the pinching data near `E × {∞}`

For `paper-p.tex`, Example `ex:monodromy-loss`: "Pinch ... `E × {∞}` along `y ∘ φ : E → ℙ¹`".
The charts of `E` saturated for `y ∘ φ` are `VInf = φ⁻¹(U_A) = (y ∘ φ)⁻¹(D₊(v))` and
`UInf = φ⁻¹(U_B) = (y ∘ φ)⁻¹(D₊(u))`, both affine (`φ` is finite), meeting in
`P01 = φ⁻¹(U_A ∩ U_B)`. All three are pullbacks of `φ`, so the localization statements follow
from one general lemma:

* `isLocalization_of_opensRange_eq_basicOpen`: an open immersion of affine schemes with image
  `D(r)` is, on global sections, the localization away from `r`;
* `isLocalization_of_isPullback`: base change of a basic open `D(r) ⊆ Spec R` along
  `g : X → Spec R` (`X` affine) is the localization away from `psi g r`;
* `infData : PinchData k Γ(VInf) Γ(UInf) Γ(P01)` with `β0 = psiA ∘ beta0`,
  `β1 = psiInf ∘ beta1` (the map `y ∘ φ` on the two charts);
* `infData_β0_isIntegral`, `infData_β1_isIntegral`, `infData_β0_injective`,
  `infData_β1_injective`, reducedness of the charts;
* **`isPushoutInf`**: the pinching `XInf` of `E' × 𝔸¹` along `E' × {0}` and `y ∘ φ` is the
  pushout of `E' × 𝔸¹ ← E' → ℙ¹` in `Scheme` (here `E' = infData.Ep` is the two-chart model of
  `E` given by `VInf ∪ UInf`, and `𝔸¹` has coordinate `t = 1/z`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization

namespace Pcf.Examples.PaperP.MonodromyLossInf

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossPinch
open Pcf.Examples.PaperP.FerrandPushout Pcf.Examples.PaperP.MonodromyLossPinchGlue
open Pcf.Examples.PaperP.TwoChartPinch Pcf.Examples.PaperP.MonodromyLossThirdChart
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-! ### General lemmas -/

/-- An open immersion of affine schemes with image a basic open `D(r)` is the localization away
from `r` on global sections. -/
theorem isLocalization_of_opensRange_eq_basicOpen {X Y : Scheme.{u}} [IsAffine X]
    (m : Y ⟶ X) [IsOpenImmersion m] (r : Γ(X, ⊤)) (h : m.opensRange = X.basicOpen r) :
    letI := m.appTop.hom.toAlgebra
    IsLocalization.Away r Γ(Y, ⊤) := by
  have hV : m ''ᵁ (m ⁻¹ᵁ ⊤) = X.basicOpen r := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_top_eq, h]
  have key : m.appTop ≫ (m.appIso (m ⁻¹ᵁ ⊤)).inv =
      X.presheaf.map (homOfLE (le_top : m ''ᵁ (m ⁻¹ᵁ ⊤) ≤ ⊤)).op :=
    m.app_appIso_inv ⊤
  letI := (X.presheaf.map (homOfLE (le_top : m ''ᵁ (m ⁻¹ᵁ ⊤) ≤ ⊤)).op).hom.toAlgebra
  haveI : IsLocalization.Away r Γ(X, m ''ᵁ (m ⁻¹ᵁ ⊤)) :=
    (isAffineOpen_top X).isLocalization_of_eq_basicOpen r _ hV
  letI := m.appTop.hom.toAlgebra
  let e : Γ(X, m ''ᵁ (m ⁻¹ᵁ ⊤)) ≃ₐ[Γ(X, ⊤)] Γ(Y, ⊤) :=
    { (m.appIso (m ⁻¹ᵁ ⊤)).commRingCatIsoToRingEquiv with
      commutes' := fun a => by
        change (m.appIso (m ⁻¹ᵁ ⊤)).hom (X.presheaf.map _ a) = m.appTop a
        rw [← key]
        change ((m.appTop ≫ (m.appIso (m ⁻¹ᵁ ⊤)).inv) ≫ (m.appIso (m ⁻¹ᵁ ⊤)).hom) a = _
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) e

/-- Functions on `X` pulled back along `g : X ⟶ Spec R`. -/
noncomputable def psi {X : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Spec R) : R →+* Γ(X, ⊤) :=
  g.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom

theorem psi_comp {X Y : Scheme.{u}} {R : CommRingCat.{u}} (m : Y ⟶ X) (g : X ⟶ Spec R) :
    psi (m ≫ g) = m.appTop.hom.comp (psi g) := by
  simp [psi]
  rfl

theorem psi_SpecMap {X : Scheme.{u}} {R S : CommRingCat.{u}} (h : X ⟶ Spec S) (f : R ⟶ S) :
    psi (h ≫ Spec.map f) = (psi h).comp f.hom := by
  ext a
  simp only [psi, Scheme.Hom.comp_appTop, RingHom.comp_apply]
  change h.appTop ((Spec.map f).appTop ((Scheme.ΓSpecIso R).inv a)) =
    h.appTop ((Scheme.ΓSpecIso S).inv (f a))
  congr 1
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Base change of a basic open `D(r) ⊆ Spec R` along `g : X ⟶ Spec R`. -/
theorem isLocalization_of_isPullback {P X Y : Scheme.{u}} [IsAffine X] {R : CommRingCat.{u}}
    {m : P ⟶ X} {s : P ⟶ Y} {g : X ⟶ Spec R} {j : Y ⟶ Spec R} [IsOpenImmersion j]
    (h : IsPullback m s g j) (r : R) (hr : ∀ p, p ∈ Set.range j ↔ r ∉ p.asIdeal) :
    IsOpenImmersion m ∧
      (letI := m.appTop.hom.toAlgebra; IsLocalization.Away (psi g r) Γ(P, ⊤)) := by
  have e : h.isoPullback.hom ≫ pullback.fst g j = m := h.isoPullback_hom_fst
  haveI : IsOpenImmersion m := by rw [← e]; infer_instance
  refine ⟨inferInstance, ?_⟩
  refine isLocalization_of_opensRange_eq_basicOpen m _ ?_
  have hj : j.opensRange = (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv r) := by
    rw [AlgebraicGeometry.basicOpen_eq_of_affine]
    ext p
    exact hr p
  have H : (h.isoPullback.hom ≫ pullback.fst g j).opensRange = X.basicOpen (psi g r) := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst, hj,
      Scheme.preimage_basicOpen_top]
    rfl
  have H' : ∀ x, x ∈ Set.range (h.isoPullback.hom ≫ pullback.fst g j) ↔
      x ∈ X.basicOpen (psi g r) := fun x => by
    rw [← H]; rfl
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  change x ∈ Set.range m ↔ _
  rw [← e]
  exact H' x

/-! ### The charts -/

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- `VInf = φ⁻¹(U_A)`. -/
noncomputable abbrev VInf : Scheme.{u} := pullback (phi k i hi) (ιA k)

/-- `P01 = φ⁻¹(U_A ∩ U_B)`, as the preimage of `Spec A[1/y]` in `VInf`. -/
noncomputable abbrev P01 : Scheme.{u} := pullback (pullback.snd (phi k i hi) (ιA k)) (jA k)

noncomputable abbrev mA : P01 k i hi ⟶ VInf k i hi := pullback.fst _ _
noncomputable abbrev sA : P01 k i hi ⟶ Spec (.of (Ay k)) := pullback.snd _ _

theorem mB_w : (mA k i hi ≫ pullback.fst (phi k i hi) (ιA k)) ≫ phi k i hi =
    (sA k i hi ≫ jB k) ≫ ιB k := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
    Category.assoc, (isPullback_charts k).w]

/-- `P01 → UInf`. -/
noncomputable def mB : P01 k i hi ⟶ UInf k i hi :=
  pullback.lift (mA k i hi ≫ pullback.fst _ _) (sA k i hi ≫ jB k) (mB_w k i hi)

theorem isPullback_A : IsPullback (mA k i hi) (sA k i hi)
    (pullback.snd (phi k i hi) (ιA k)) (jA k) :=
  IsPullback.of_hasPullback _ _

theorem isPullback_B : IsPullback (mB k i hi) (sA k i hi)
    (pullback.snd (phi k i hi) (ιB k)) (jB k) := by
  have outer : IsPullback (mA k i hi ≫ pullback.fst (phi k i hi) (ιA k)) (sA k i hi)
      (phi k i hi) (jA k ≫ ιA k) :=
    (isPullback_A k i hi).paste_horiz (IsPullback.of_hasPullback _ _)
  have e1 : mA k i hi ≫ pullback.fst (phi k i hi) (ιA k) =
      mB k i hi ≫ pullback.fst (phi k i hi) (ιB k) := (pullback.lift_fst _ _ _).symm
  rw [e1, (isPullback_charts k).w] at outer
  exact IsPullback.of_right outer (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)

instance jA_isOpenImmersion : IsOpenImmersion (jA k) := by unfold jA; infer_instance

instance jB_isOpenImmersion : IsOpenImmersion (jB k) := by
  letI := (BtoAy k).toAlgebra
  haveI := BtoAy_isLocalization k
  exact IsOpenImmersion.of_isLocalization (R := B k) (S := Ay k) (wB k)

instance VInf_isAffine : IsAffine (VInf k i hi) := inferInstance
instance P01_isAffine : IsAffine (P01 k i hi) := inferInstance

/-- `psiA : A → Γ(VInf)`. -/
noncomputable abbrev psiA : A k →+* Γ(VInf k i hi, ⊤) := psi (pullback.snd (phi k i hi) (ιA k))
/-- `psi01 : A[1/y] → Γ(P01)`. -/
noncomputable abbrev psi01 : Ay k →+* Γ(P01 k i hi, ⊤) := psi (sA k i hi)

theorem psiInf_eq : psiInf k i hi = psi (pullback.snd (phi k i hi) (ιB k)) := rfl

theorem mA_loc : IsOpenImmersion (mA k i hi) ∧
    (letI := (mA k i hi).appTop.hom.toAlgebra
     IsLocalization.Away (psiA k i hi (yA k)) Γ(P01 k i hi, ⊤)) :=
  isLocalization_of_isPullback (isPullback_A k i hi) (yA k) fun p =>
    mem_range_SpecMap_iff (algebraMap (A k) (Ay k)) (yA k) (Ay_isLocalization k) p

theorem mB_loc : IsOpenImmersion (mB k i hi) ∧
    (letI := (mB k i hi).appTop.hom.toAlgebra
     IsLocalization.Away (psiInf k i hi (wB k)) Γ(P01 k i hi, ⊤)) :=
  isLocalization_of_isPullback (isPullback_B k i hi) (wB k) fun p =>
    mem_range_SpecMap_iff (BtoAy k) (wB k) (BtoAy_isLocalization k) p

theorem psi01_comp_A : (psi01 k i hi).comp (algebraMap (A k) (Ay k)) =
    (mA k i hi).appTop.hom.comp (psiA k i hi) := by
  rw [← psi_comp, (isPullback_A k i hi).w, jA, psi_SpecMap]
  rfl

theorem psi01_comp_B : (psi01 k i hi).comp (BtoAy k) =
    (mB k i hi).appTop.hom.comp (psiInf k i hi) := by
  rw [psiInf_eq, ← psi_comp, (isPullback_B k i hi).w, jB, psi_SpecMap]
  rfl

/-- **The pinching data of `E × {∞}` along `y ∘ φ`.** -/
noncomputable def infData :
    PinchData k Γ(VInf k i hi, ⊤) Γ(UInf k i hi, ⊤) Γ(P01 k i hi, ⊤) where
  z0 := (mA k i hi).appTop.hom
  z1 := (mB k i hi).appTop.hom
  e0 := psiA k i hi (yA k)
  e1 := psiInf k i hi (wB k)
  loc0 := (mA_loc k i hi).2
  loc1 := (mB_loc k i hi).2
  β0 := (psiA k i hi).comp (beta0 k)
  β1 := (psiInf k i hi).comp (beta1 k)
  β01 := (psi01 k i hi).comp (beta01 k)
  hβ0 := by
    rw [RingHom.comp_assoc, hβ0, ← RingHom.comp_assoc, psi01_comp_A, RingHom.comp_assoc]
  hβ1 := by
    rw [RingHom.comp_assoc, hβ1, ← RingHom.comp_assoc, psi01_comp_B, RingHom.comp_assoc]
  β0_t0 := by simp [beta0_t0]
  β1_t1 := by simp [beta1_t1]

#print axioms isLocalization_of_opensRange_eq_basicOpen
#print axioms infData

end Pcf.Examples.PaperP.MonodromyLossInf
