/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimCoreDefs
public import Pcf.Bounding.AllCodimBlowupMonodromyTransport

/-!
# Good points and the splitting of the all-codimension core

Fix an affine open `U = Spec R` of the normal ambient `X` containing the
centre `y`, with prime `P` and a nonzero `a ∈ P`, and the normalized blow-up
`β : Y ⟶ X` of `P`. A point `x` of the closure `A` of `y` is *good* when `A`
is regular at `x` and every codimension-two point `E` over `x` on an
exceptional divisor dominating `A` satisfies `AllCodimGoodAt`. The bad points
are the finite set `T` of `latex/paper-p.tex`, proof of Theorem
`thm:allcodim-normal`.

`AllCodimAffineCore` follows from two statements proved separately:
`AllCodimBadFinite` (only finitely many codimension-one points of `A` are
bad) and `AllCodimEtaleOfGood` (the normalized return is étale at every
divisor over a good point).
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace Pcf.Bounding.AllCodimBlowup

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The prime of `y` in the affine chart `U`. -/
abbrev allCodimCentrePrime {X : Scheme.{u}} (U : X.affineOpens) (y : X)
    (hyU : y ∈ (U : X.Opens)) : Ideal Γ(X, U) :=
  (U.2.primeIdealOf ⟨y, hyU⟩).asIdeal

/-- The normalized blow-up of the centre on the chart, mapped to `X`. -/
def allCodimBlowupToAmbient {X : Scheme.{u}} [IsIntegral X] (U : X.affineOpens)
    [Nonempty (U : X.Opens)] (y : X)
    (hyU : y ∈ (U : X.Opens)) (a : allCodimCentrePrime U y hyU) (ha : (a : Γ(X, U)) ≠ 0) :
    letI : IsIntegral (reesProj (allCodimCentrePrime U y hyU)) :=
      reesProj_isIntegral _ a ha
    Palomar.normalization (reesProj (allCodimCentrePrime U y hyU)) ⟶ X :=
  letI : IsIntegral (reesProj (allCodimCentrePrime U y hyU)) := reesProj_isIntegral _ a ha
  Bounding.AllCodimBlowup.normalizedReesProjToSpec _ a ha ≫ U.2.fromSpec

/-- A good point `x` for the chart data. -/
def AllCodimGoodPoint (p : ℕ) {X : Scheme.{u}} [IsIntegral X] (U : X.affineOpens)
    [Nonempty (U : X.Opens)] (y : X)
    (hyU : y ∈ (U : X.Opens)) (a : allCodimCentrePrime U y hyU) (ha : (a : Γ(X, U)) ≠ 0)
    (B : Set X) (x : X) : Prop :=
  letI : IsIntegral (reesProj (allCodimCentrePrime U y hyU)) := reesProj_isIntegral _ a ha
  ∃ hyx : y ⤳ x, IsDiscreteValuationRing (closureStalk X hyx) ∧
    ∀ (d : SchemeDivisorPoint (Palomar.normalization (reesProj (allCodimCentrePrime U y hyU))))
      (_ : allCodimBlowupToAmbient U y hyU a ha d.1 = y)
      (E : Palomar.normalization (reesProj (allCodimCentrePrime U y hyU)))
      (hdE : d.1 ⤳ E) (_ : allCodimBlowupToAmbient U y hyU a ha E = x)
      (_ : Order.coheight E = 2),
      AllCodimGoodAt p (allCodimBlowupToAmbient U y hyU a ha) y B d E hdE

/-- **L2.** Only finitely many codimension-one points of the closure of `y`
in the chart are bad. -/
def AllCodimBadFinite (p : ℕ) (k : Type u) [Field k] [CharP k p] : Prop :=
  ∀ {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X] [IsLocallyNoetherian X]
    [NoetherianSpace X] (_ : X ⟶ Spec (.of k)) [LocallyOfFiniteType ‹X ⟶ Spec (.of k)›]
    (y : X) (_ : y ≠ genericPoint X) (B : Set X) (_ : B.Finite)
    (U : X.affineOpens) [Nonempty (U : X.Opens)] (hyU : y ∈ (U : X.Opens))
    (a : allCodimCentrePrime U y hyU) (ha : (a : Γ(X, U)) ≠ 0),
    {x : X | (∃ Q : SchemeDivisorPoint (pointClosureIdealSheaf y).subscheme,
        (pointClosureIdealSheaf y).subschemeι Q.1 = x) ∧ x ∈ (U : X.Opens) ∧
      ¬ AllCodimGoodPoint p U y hyU a ha B x}.Finite

/-- **L1.** At a divisor of the normalized return lying over a good point,
the normalized return is étale. -/
def AllCodimEtaleOfGood (p : ℕ) (k : Type u) [Field k] [CharP k p] : Prop :=
  ∀ {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X] [IsLocallyNoetherian X]
    [NoetherianSpace X] (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (y : X) (_ : y ≠ genericPoint X) (B : Set X)
    (U : X.affineOpens) [Nonempty (U : X.Opens)] (hyU : y ∈ (U : X.Opens))
    (a : allCodimCentrePrime U y hyU) (ha : (a : Γ(X, U)) ≠ 0)
    (h : X ⟶ X) [IsFinite h] [IsDominant h] (hfix : h y = y)
    (_ : IsPrimeToPMonodromyMap p h)
    (_ : ∀ w : SchemeDivisorPoint X, h w.1 ∉ B → (h.stalkMap w.1).hom.FormallyEtale),
    let A := (pointClosureIdealSheaf y).subscheme
    letI : IsFinite (Palomar.normalizationMap A) :=
      schemeGlobalNormalizationMap_isFinite A k ((pointClosureIdealSheaf y).subschemeι ≫ s)
    letI : IsFinite (pointClosureReturnMap h y hfix) := pointClosureReturnMap_isFinite h y hfix
    letI : IsDominant (pointClosureReturnMap h y hfix) :=
      pointClosureReturnMap_isDominant h y hfix
    let F := schemeGlobalNormalizationLift (pointClosureReturnMap h y hfix)
    ∀ Q₁ : SchemeDivisorPoint (Palomar.normalization A),
      (pointClosureIdealSheaf y).subschemeι (Palomar.normalizationMap A (F Q₁.1)) ∈
        (U : X.Opens) →
      AllCodimGoodPoint p U y hyU a ha B
        ((pointClosureIdealSheaf y).subschemeι (Palomar.normalizationMap A (F Q₁.1))) →
      (F.stalkMap Q₁.1).hom.FormallyEtale

/-- A point of an integral scheme with zero prime on an affine chart is the
generic point. -/
theorem allCodimCentrePrime_ne_bot {X : Scheme.{u}} [IsIntegral X] (U : X.affineOpens)
    [Nonempty (U : X.Opens)] (y : X) (hyU : y ∈ (U : X.Opens)) (hy : y ≠ genericPoint X) :
    allCodimCentrePrime U y hyU ≠ ⊥ := by
  intro hbot
  apply hy
  have hgU : genericPoint X ∈ (U : X.Opens) :=
    ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr ⟨y, trivial, hyU⟩
  have h1 : U.2.primeIdealOf ⟨y, hyU⟩ = U.2.primeIdealOf ⟨genericPoint X, hgU⟩ := by
    rw [U.2.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    ext1
    exact hbot
  have h2 := congrArg U.2.fromSpec h1
  rwa [U.2.fromSpec_primeIdealOf, U.2.fromSpec_primeIdealOf] at h2

/-- A finite dominant map to a scheme of finite type over a field sends
divisor points to divisor points. -/
theorem coheight_apply_eq_one_of_finite_of_locallyOfFiniteType
    (k : Type u) [Field k] {Z W : Scheme.{u}} [IsIntegral Z] [IsIntegral W]
    (t : W ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (f : Z ⟶ W) [IsFinite f] [IsDominant f] (Q : SchemeDivisorPoint Z) :
    Order.coheight (f Q.1) = 1 := by
  obtain ⟨V, hV, hQV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show f Q.1 ∈ (⊤ : W.Opens) from trivial)
  let U : W.affineOpens := ⟨V, hV⟩
  letI : Algebra k Γ(W, U) :=
    ((t.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  haveI : Algebra.FiniteType k Γ(W, U) := by
    apply RingHom.finiteType_algebraMap.mp
    change ((t.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).FiniteType
    exact (t.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType
  exact coheight_apply_eq_one_of_mem_affine_finiteType f k U Q hQV

/-- **The per-affine core from L1 and L2.** -/
theorem allCodimAffineCore_of_good (p : ℕ) (k : Type u) [Field k] [CharP k p]
    (hL2 : AllCodimBadFinite p k) (hL1 : AllCodimEtaleOfGood p k) :
    AllCodimAffineCore p k := by
  intro X _ _ _ _ s _ y hy B hB U hyU
  haveI : Nonempty (U : X.Opens) := ⟨⟨y, hyU⟩⟩
  obtain ⟨a, haP, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (allCodimCentrePrime_ne_bot U y hyU hy)
  let a' : allCodimCentrePrime U y hyU := ⟨a, haP⟩
  refine ⟨_, hL2 s y hy B hB U hyU a' ha, ?_⟩
  intro h _ _ hfix hmono hbranch A F Q₁ hxU hxT
  apply hL1 s y hy B U hyU a' ha h hfix hmono hbranch Q₁ hxU
  by_contra hbad
  apply hxT
  refine ⟨?_, hxU, hbad⟩
  letI : IsFinite (Palomar.normalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite A k ((pointClosureIdealSheaf y).subschemeι ≫ s)
  let Qt : SchemeDivisorPoint (Palomar.normalization A) := Q₁.mapFiniteDominantNormal F
  exact ⟨⟨Palomar.normalizationMap A Qt.1,
    coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k ((pointClosureIdealSheaf y).subschemeι ≫ s) (Palomar.normalizationMap A) Qt⟩, rfl⟩

#print axioms allCodimAffineCore_of_good

end
end Pcf
