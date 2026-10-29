/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimReturnPCFReduction
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Local data for the normalized blow-up argument

This module fixes the local conditions used in `latex/paper-p.tex`, proof of
Theorem `thm:allcodim-normal`, at a codimension-two point `E` of the
normalized blow-up `Y` lying on an exceptional divisor `D = \overline{d}`
over a codimension-one point `x` of the periodic subvariety
`A = \overline{y}`.

* `stalkGenerizationPrime` is the prime of a generization inside a stalk.
* `stalkGenerizationQuotientMap` is the induced map `𝒪_{A,x} ⟶ 𝒪_{D,E}`
  of reduced closures, through the stalk map of `β : Y ⟶ X`.
* `AllCodimGoodAt` collects the paper's conditions defining the finite bad
  set `T`: the divisor `D` is principal and regular at `E`, no other
  exceptional or postcritical divisor passes through `E`, and the fibre
  multiplicity `μ(E/x)` is a power of `p`. Regularity of `𝒪_{Y,E}` is a
  consequence (a principal prime with regular quotient), which replaces the
  paper's use of the closed singular locus.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The prime of a generization `d ⤳ E` inside the stalk at `E`. -/
def stalkGenerizationPrime (X : Scheme.{u}) {d E : X} (h : d ⤳ E) :
    Ideal (X.presheaf.stalk E) :=
  (maximalIdeal (X.presheaf.stalk d)).comap (X.presheaf.stalkSpecializes h).hom

instance stalkGenerizationPrime_isPrime (X : Scheme.{u}) {d E : X} (h : d ⤳ E) :
    (stalkGenerizationPrime X h).IsPrime :=
  Ideal.comap_isPrime _ _

/-- The stalk of the reduced closure of `y` at `x`, as a quotient of the
ambient stalk. -/
abbrev closureStalk (X : Scheme.{u}) {y x : X} (h : y ⤳ x) : Type u :=
  X.presheaf.stalk x ⧸ stalkGenerizationPrime X h

/-- A morphism sending `d ↦ y` and `E ↦ x` maps the closure prime of `y` at
`x` into the closure prime of `d` at `E`. -/
theorem stalkGenerizationPrime_le_comap {X Y : Scheme.{u}} (β : Y ⟶ X)
    {d E : Y} (hdE : d ⤳ E) :
    stalkGenerizationPrime X (hdE.map β.continuous) ≤
      (stalkGenerizationPrime Y hdE).comap (β.stalkMap E).hom := by
  intro r hr
  change (Y.presheaf.stalkSpecializes hdE).hom ((β.stalkMap E).hom r) ∈
    maximalIdeal (Y.presheaf.stalk d)
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
  exact map_nonunit (β.stalkMap d).hom _ hr

/-- The map of reduced closures `𝒪_{X,βE}/𝔭_{βd} ⟶ 𝒪_{Y,E}/𝔭_d` induced by `β`. -/
def stalkGenerizationQuotientMap {X Y : Scheme.{u}} (β : Y ⟶ X)
    {d E : Y} (hdE : d ⤳ E) :
    closureStalk X (hdE.map β.continuous) →+* closureStalk Y hdE :=
  Ideal.quotientMap _ (β.stalkMap E).hom (stalkGenerizationPrime_le_comap β hdE)

/-- The fibre multiplicity `μ(E/x)` of `latex/paper-p.tex`: the ramification
index of the closure of `d` at `E` over the closure of `β d` at `β E`. -/
def closureFibreMultiplicity {X Y : Scheme.{u}} (β : Y ⟶ X)
    {d E : Y} (hdE : d ⤳ E) : ℕ :=
  letI := (stalkGenerizationQuotientMap β hdE).toAlgebra
  (maximalIdeal (closureStalk Y hdE)).ramificationIdx (closureStalk X (hdE.map β.continuous))

/-- The local conditions at a codimension-two point `E` of an exceptional
divisor `d` of the normalized blow-up `β : Y ⟶ X`, relative to a set `B` of
points of `X` (the postcritical divisors), the centre `y`, and the prime `p`.
-/
structure AllCodimGoodAt (p : ℕ) {X Y : Scheme.{u}} (β : Y ⟶ X) (y : X)
    (B : Set X) (d : SchemeDivisorPoint Y) (E : Y) (hdE : d.1 ⤳ E) : Prop where
  /-- The divisor `D` is cut out by one equation at `E`. -/
  principal : (stalkGenerizationPrime Y hdE).IsPrincipal
  /-- The divisor `D` is regular at `E`. -/
  divisor_dvr : IsDiscreteValuationRing (closureStalk Y hdE)
  /-- No other exceptional or postcritical divisor passes through `E`. -/
  isolated : ∀ w : SchemeDivisorPoint Y, w.1 ⤳ E → w ≠ d →
    ¬ y ⤳ β w.1 ∧ β w.1 ∉ B
  /-- The fibre multiplicity is a power of `p`. -/
  primary : ∃ b : ℕ, closureFibreMultiplicity β hdE = p ^ b

open TopologicalSpace in
/-- **The per-affine core of `thm:allcodim-normal`.** For a normal ambient
`X`, a non-generic point `y`, a finite set `B` (the postcritical divisors) and
an affine open `U ∋ y`, one finite set `T` of points bounds, uniformly in
every finite self-map `h` fixing `y` with prime-to-`p` monodromy and branch
divisors over `B`, the images in `U` of the non-étale divisors of the
normalized return of `h` on the closure of `y`. -/
def AllCodimAffineCore (p : ℕ) (k : Type u) [Field k] [CharP k p] : Prop :=
  ∀ {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X] [IsLocallyNoetherian X]
    [NoetherianSpace X] (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (y : X) (_ : y ≠ genericPoint X) (B : Set X) (_ : B.Finite)
    (U : X.affineOpens) (_ : y ∈ (U : X.Opens)),
    ∃ T : Set X, T.Finite ∧
      ∀ (h : X ⟶ X) [IsFinite h] [IsDominant h] (hfix : h y = y)
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
          (pointClosureIdealSheaf y).subschemeι
              (Palomar.normalizationMap A (F Q₁.1)) ∈ (U : X.Opens) →
          (pointClosureIdealSheaf y).subschemeι
              (Palomar.normalizationMap A (F Q₁.1)) ∉ T →
          (F.stalkMap Q₁.1).hom.FormallyEtale

end
end Pcf
