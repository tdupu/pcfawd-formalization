/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimEtaleOfGood
public import Pcf.Bounding.NormalizationLiftMonodromy
public import Pcf.Bounding.AllCodimBadFinite

/-!
# Theorem A in positive characteristic

`latex/paper-p.tex`, Theorem `thm:A`, for `p > 0`: a finite surjective
separable PCF self-map with prime-to-`p` monodromy of an integral variety
over a field of characteristic `p` is PCF along all subvariety chains
(Definition `def:pcfawd-allsubvar`). The returns on every proper integral
closed subvariety, at every preperiod and period, are separable and PCF,
recursively, on the original reduced subvarieties.

The proof applies the finite-cover induction to the normalization `X^ν`
with the lifted map, using the PCF transfer (`lem:pcf-transfer-charp`) and
the normalized blow-up argument (`thm:allcodim-normal`).
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- Theorem A in characteristic `p`, given the finiteness of bad points. -/
theorem isPCFAllSubvarieties_charP_of_badFinite
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    (hL2 : AllCodimBadFinite p k)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsSeparableNormalizedPCF k s f)
    (hmono : IsPrimeToPMonodromyMap p f) :
    IsPCFAllSubvarieties k s f := by
  letI : IsFinite (Palomar.normalizationMap X) := schemeGlobalNormalizationMap_isFinite X k s
  let ν := Palomar.normalizationMap X
  let g := schemeGlobalNormalizationLift f
  haveI : IsLocallyNoetherian (Palomar.normalization X) :=
    LocallyOfFiniteType.isLocallyNoetherian (ν ≫ s)
  haveI : CompactSpace (Palomar.normalization X) :=
    QuasiCompact.compactSpace_of_compactSpace ν
  haveI : IsNoetherian (Palomar.normalization X) := ⟨⟩
  have hcomm : g ≫ ν = ν ≫ f := schemeGlobalNormalizationLift_comp f
  have hpcfg : IsSeparableNormalizedPCF k (ν ≫ s) g := by
    rw [isSeparableNormalizedPCF_iff_normalLift k s f] at hpcf
    obtain ⟨_, hpcfl⟩ := hpcf
    exact (normalScheme_isSeparableNormalizedPCF_iff k (ν ≫ s) g).mpr ⟨_, hpcfl⟩
  have hmonog : IsPrimeToPMonodromyMap p g :=
    isPrimeToPMonodromyMap_schemeGlobalNormalizationLift p f hmono
  exact isPCFAllSubvarieties_of_normal_finite_cover_charp p hp k
    (finiteSemiconjugacyPCFTransfer k)
    (allCodimNormalizedReturnPCF_of_affineCore p hp k
      (allCodimAffineCore_of_good p k hL2 (allCodimEtaleOfGood p hp k)))
    s f g ν hcomm hpcfg hmonog

#print axioms isPCFAllSubvarieties_charP_of_badFinite

/-- **Theorem A in characteristic `p`** (`latex/paper-p.tex`, Theorem
`thm:A`, the case `p > 0`). Let `X` be an integral scheme locally of finite
type over a field `k` of characteristic `p` (with Noetherian underlying
space), and `f : X ⟶ X` finite and surjective (dominant), separable and PCF
in the normalized sense, with prime-to-`p` monodromy. Then `f` is PCF along
all subvariety chains: for every proper integral closed subvariety and all
preperiods and periods, the return on the original reduced image is separable
and PCF, recursively at every depth (Definition `def:pcfawd-allsubvar`). -/
theorem isPCFAllSubvarieties_charP
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsSeparableNormalizedPCF k s f)
    (hmono : IsPrimeToPMonodromyMap p f) :
    IsPCFAllSubvarieties k s f :=
  isPCFAllSubvarieties_charP_of_badFinite p hp k (allCodimBadFinite p hp k) s f hpcf hmono

#print axioms isPCFAllSubvarieties_charP

end
end Pcf
