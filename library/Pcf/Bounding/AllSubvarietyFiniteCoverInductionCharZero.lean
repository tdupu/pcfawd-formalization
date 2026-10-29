/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllSubvarietyFiniteCoverInduction

/-!
# Characteristic-zero finite-cover induction

This is the characteristic-zero companion to the conditional
positive-characteristic induction for `latex/paper-p.tex`, Theorem
`thm:allsubvar-pcfawd`. The PCF assertion for normalized periodic returns
remains an explicit `thm:allcodim-normal` hypothesis; no monodromy assumption
is needed in characteristic zero.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- The characteristic-zero PCF conclusion of the normalized blow-up trick
for a periodic original reduced point closure. -/
def AllCodimNormalizedReturnPCFCharZero
    (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [NoetherianSpace Y] [IsNormalScheme Y]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g],
    IsSeparableNormalizedPCF k t g →
    ∀ (y : Y) (n : ℕ) (_ : 0 < n)
      (hy : schemePointIterate g n y = y)
      (a : (pointClosureIdealSheaf y).subscheme ⟶ Spec (.of k))
      [LocallyOfFiniteType a],
      let q := pointClosureReturnMap (End.of g ^ n).asHom y hy
      let A := (pointClosureIdealSheaf y).subscheme
      let ν := Palomar.normalizationMap A
      letI : IsFinite ν := schemeGlobalNormalizationMap_isFinite A k a
      IsSeparableNormalizedPCF k (ν ≫ a) (schemeGlobalNormalizationLift q)

/-- Finite-depth induction for a normal finite cover in characteristic zero.
The periodic lift and normalization cover are constructed in Lean; only
the two source PCF descent results are supplied as hypotheses. -/
theorem isPCFAllSubvarietiesAtDepth_of_normal_finite_cover_charZero
    (k : Type u) [Field k] [CharZero k]
    (htransfer : FiniteSemiconjugacyPCFTransfer k)
    (hcodim : AllCodimNormalizedReturnPCFCharZero k)
    (d : ℕ)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y] [IsNormalScheme Y]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
    (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f)
    (hpcf : IsSeparableNormalizedPCF k (π ≫ s) g) :
    IsPCFAllSubvarietiesAtDepth k d s f := by
  induction d generalizing X Y s f g π with
  | zero => exact htransfer s f g π hcomm hpcf
  | succ d ih =>
      refine ⟨htransfer s f g π hcomm hpcf, ?_⟩
      intro C r q hq hperiodic
      obtain ⟨y, hπy, c, hc, hy, ρ, hρfin, hρdom, hcommρ⟩ :=
        exists_preperiodic_pointClosure_cover f g π hcomm C.1 r q hperiodic
      let B := schemePointIterate f r C.1
      let w := eventuallyPeriodicPointReturn f r q C.1 hperiodic
      let A := (pointClosureIdealSheaf y).subscheme
      let sB : (pointClosureIdealSheaf B).subscheme ⟶ Spec (.of k) :=
        (pointClosureIdealSheaf B).subschemeι ≫ s
      let a : A ⟶ Spec (.of k) := ρ ≫ sB
      letI : IsFinite ρ := hρfin
      letI : IsDominant ρ := hρdom
      letI : LocallyOfFiniteType a := by infer_instance
      let ν := Palomar.normalizationMap A
      letI : IsFinite ν := schemeGlobalNormalizationMap_isFinite A k a
      let qY := pointClosureReturnMap (End.of g ^ (q * c)).asHom y hy
      let H := schemeGlobalNormalizationLift qY
      let πB : Palomar.normalization A ⟶ (pointClosureIdealSheaf B).subscheme := ν ≫ ρ
      have hnorm : H ≫ ν = ν ≫ qY := by
        exact schemeGlobalNormalizationLift_comp qY
      have hcommB : H ≫ πB = πB ≫ (End.of w ^ c).asHom := by
        calc
          H ≫ πB = (H ≫ ν) ≫ ρ := by simp only [πB, Category.assoc]
          _ = (ν ≫ qY) ≫ ρ := by rw [hnorm]
          _ = ν ≫ (qY ≫ ρ) := by rw [Category.assoc]
          _ = ν ≫ (ρ ≫ (End.of w ^ c).asHom) := by rw [hcommρ]
          _ = πB ≫ (End.of w ^ c).asHom := by simp only [πB, Category.assoc]
      have hpcfB : IsSeparableNormalizedPCF k (πB ≫ sB) H := by
        have h := hcodim (π ≫ s) g hpcf y (q * c)
          (Nat.mul_pos hq hc) hy a
        simpa only [πB, a, H, ν, Category.assoc] using h
      have hBpow : IsPCFAllSubvarietiesAtDepth k d sB (End.of w ^ c).asHom :=
        ih sB (End.of w ^ c).asHom H πB hcommB hpcfB
      exact isPCFAllSubvarietiesAtDepth_of_pow k sB w c hc d hBpow

/-- Conditional characteristic-zero form of the finite-domination part of
`paper-p.tex`, Theorem `thm:allsubvar-pcfawd`. -/
theorem isPCFAllSubvarieties_of_normal_finite_cover_charZero
    (k : Type u) [Field k] [CharZero k]
    (htransfer : FiniteSemiconjugacyPCFTransfer k)
    (hcodim : AllCodimNormalizedReturnPCFCharZero k)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y] [IsNormalScheme Y]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
    (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f)
    (hpcf : IsSeparableNormalizedPCF k (π ≫ s) g) :
    IsPCFAllSubvarieties k s f := by
  intro d
  exact isPCFAllSubvarietiesAtDepth_of_normal_finite_cover_charZero
    k htransfer hcodim d s f g π hcomm hpcf

#print axioms isPCFAllSubvarietiesAtDepth_of_normal_finite_cover_charZero
#print axioms isPCFAllSubvarieties_of_normal_finite_cover_charZero

end Pcf
