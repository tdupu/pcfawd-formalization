/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeCharPTransfer

/-!
# PCF transfer through an arbitrary finite comparison map

This removes normality of the upper comparison variety from the existing
finite semiconjugacy theorem, as required by `paper-p.tex`, Lemma
`lem:pcf-transfer-charp`.
-/

@[expose] public section

namespace Pcf
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

set_option linter.style.haveILetI false

/-- `paper-p.tex`, Lemma `lem:pcf-transfer-charp`: a finite surjective
semiconjugacy descends separable normalized PCF from any integral upper
variety. The upper comparison map need not be separable.

`paper-p.tex` correspondence: Lemma 9.1 (`lem:pcf-transfer-charp`). -/
theorem paperP_pcf_transfer_finiteComparison
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
    (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f)
    (hpcf : IsSeparableNormalizedPCF k (π ≫ s) g) :
    IsSeparableNormalizedPCF k s f := by
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k (π ≫ s)
  let ν : Palomar.normalization Y ⟶ Y := Palomar.normalizationMap Y
  let g' := schemeGlobalNormalizationLift g
  let π' := ν ≫ π
  haveI : IsLocallyNoetherian (Palomar.normalization Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (ν ≫ π ≫ s)
  haveI : CompactSpace (Palomar.normalization Y) :=
    QuasiCompact.compactSpace_of_compactSpace ν
  haveI : IsNoetherian (Palomar.normalization Y) := ⟨⟩
  have hcomm' : g' ≫ π' = π' ≫ f := by
    calc
      g' ≫ π' = (schemeGlobalNormalizationLift g ≫ ν) ≫ π := rfl
      _ = (ν ≫ g) ≫ π := by rw [schemeGlobalNormalizationLift_comp]
      _ = ν ≫ (g ≫ π) := Category.assoc _ _ _
      _ = ν ≫ (π ≫ f) := by rw [hcomm]
      _ = π' ≫ f := by simp only [π', Category.assoc]
  have hpcfg : IsSeparableNormalizedPCF k (π' ≫ s) g' := by
    have hp := (isSeparableNormalizedPCF_iff_normalLift k (π ≫ s) g).mp hpcf
    obtain ⟨_, hpcfl⟩ := hp
    exact (normalScheme_isSeparableNormalizedPCF_iff k (π' ≫ s) g').mpr
      ⟨_, hpcfl⟩
  exact finiteSemiconjugacyPCFTransfer k s f g' π' hcomm' hpcfg

#print axioms paperP_pcf_transfer_finiteComparison

end Pcf
