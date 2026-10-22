/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimPreperiodicCover
public import Pcf.Bounding.AllSubvarietyIterationConverse
public import Pcf.Bounding.PointClosureReturnNormalizationMonodromy

/-!
# Finite-cover induction for all-subvariety PCF

This is the formal induction in `latex/paper-p.tex`, Theorem
`thm:allsubvar-pcfawd`, for positive characteristic. The two outstanding
geometric inputs are explicit hypotheses: PCF transfer through a finite
semiconjugacy, and PCF of the normalized periodic point-closure return.
The periodic lift, finite comparison, normalized lift, and recursive
induction are actual constructions.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- The still-conditional characteristic-`p` PCF-transfer assertion, stated
for actual finite commuting maps. Generic separability is included in the
conclusion, as in `paper-p.tex`, Lemma `lem:pcf-transfer-charp`. -/
def FiniteSemiconjugacyPCFTransfer
    (k : Type u) [Field k] : Prop :=
  ∀ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y] [IsNormalScheme Y]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
    (π : Y ⟶ X) [IsFinite π] [IsDominant π],
    g ≫ π = π ≫ f →
    IsSeparableNormalizedPCF k (π ≫ s) g →
    IsSeparableNormalizedPCF k s f

/-- The still-conditional PCF conclusion of the normalized blow-up trick,
for an actual periodic point closure and its canonical normalization. The
base morphism on the closure is arbitrary because PCF of a normal return is
intrinsic; in the induction it is the pullback of the downstairs cover. -/
def AllCodimNormalizedReturnPCF
    (p : ℕ) (k : Type u) [Field k] [CharP k p] : Prop :=
  ∀ {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [NoetherianSpace Y] [IsNormalScheme Y]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g],
    IsSeparableNormalizedPCF k t g → IsPrimeToPMonodromyMap p g →
    ∀ (y : Y) (n : ℕ) (_ : 0 < n)
      (hy : schemePointIterate g n y = y)
      (a : (pointClosureIdealSheaf y).subscheme ⟶ Spec (.of k))
      [LocallyOfFiniteType a],
      let q := pointClosureReturnMap (End.of g ^ n).asHom y hy
      let A := (pointClosureIdealSheaf y).subscheme
      let ν := Palomar.normalizationMap A
      letI : IsFinite ν := schemeGlobalNormalizationMap_isFinite A k a
      IsSeparableNormalizedPCF k (ν ≫ a) (schemeGlobalNormalizationLift q)

/-- Finite-depth induction for the source theorem. Each successor step uses
the checked periodic-cover theorem, then applies the two conditional source
inputs only to a finite normal cover of the lower-dimensional original
point closure. -/
theorem isPCFAllSubvarietiesAtDepth_of_normal_finite_cover_charp
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    (htransfer : FiniteSemiconjugacyPCFTransfer k)
    (hcodim : AllCodimNormalizedReturnPCF p k)
    (d : ℕ)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y] [IsNormalScheme Y]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
    (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f)
    (hpcf : IsSeparableNormalizedPCF k (π ≫ s) g)
    (hmono : IsPrimeToPMonodromyMap p g) :
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
        have h := hcodim (π ≫ s) g hpcf hmono y (q * c)
          (Nat.mul_pos hq hc) hy a
        simpa only [πB, a, H, ν, Category.assoc] using h
      have hmonoB : IsPrimeToPMonodromyMap p H := by
        have h := finiteType_pointClosureReturn_iterate_normalization_primeToPMonodromy
          p hp k g (π ≫ s) hmono (q * c) (Nat.mul_pos hq hc) y hy
        exact h
      have hBpow : IsPCFAllSubvarietiesAtDepth k d sB (End.of w ^ c).asHom :=
        ih sB (End.of w ^ c).asHom H πB hcommB hpcfB hmonoB
      exact isPCFAllSubvarietiesAtDepth_of_pow k sB w c hc d hBpow

/-- Conditional positive-characteristic form of `paper-p.tex`, Theorem
`thm:allsubvar-pcfawd`, for every finite semiconjugate image of a normal
PCF system. The induction itself has no domain-specific axioms. -/
theorem isPCFAllSubvarieties_of_normal_finite_cover_charp
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    (htransfer : FiniteSemiconjugacyPCFTransfer k)
    (hcodim : AllCodimNormalizedReturnPCF p k)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y] [IsNormalScheme Y]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
    (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f)
    (hpcf : IsSeparableNormalizedPCF k (π ≫ s) g)
    (hmono : IsPrimeToPMonodromyMap p g) :
    IsPCFAllSubvarieties k s f := by
  intro d
  exact isPCFAllSubvarietiesAtDepth_of_normal_finite_cover_charp
    p hp k htransfer hcodim d s f g π hcomm hpcf hmono

#print axioms isPCFAllSubvarietiesAtDepth_of_normal_finite_cover_charp
#print axioms isPCFAllSubvarieties_of_normal_finite_cover_charp

end Pcf
