/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimEtaleOfGoodCharZero
public import Pcf.Bounding.AllCodimBadFiniteCharZero
public import Pcf.Bounding.TheoremACharP
public import Pcf.Bounding.TheoremACharPWeighted

/-!
# Theorem A in characteristic zero

`latex/paper-p.tex`, Theorem `thm:A`, for `p = 0`: a finite surjective PCF
self-map of an integral variety over a field of characteristic zero is PCF
along all subvariety chains (Definition `def:pcfawd-allsubvar`). No monodromy
hypothesis is needed: separability and tameness are automatic.

The proof is the characteristic-`p` one: the finite-cover induction on the
normalization `X^ν` with the lifted map, using the PCF transfer
(`lem:pcf-transfer-charp`, which holds over every field) and the
characteristic-zero normalized blow-up argument (`thm:allcodim-normal`).
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The characteristic-zero all-codimension input of the finite-cover
induction (`thm:allcodim-normal`, `p = 0`). -/
theorem allCodimNormalizedReturnPCFCharZero (k : Type u) [Field k] [CharZero k] :
    AllCodimNormalizedReturnPCFCharZero k :=
  allCodimNormalizedReturnPCFCharZero_of_affineCore k
    (allCodimAffineCoreCharZero_of_good k (allCodimBadFiniteCharZero k)
      (allCodimEtaleOfGoodCharZero k))

/-- **Theorem A in characteristic zero** (`latex/paper-p.tex`, Theorem
`thm:A`, the case `p = 0`). Let `X` be an integral scheme locally of finite
type over a field `k` of characteristic zero (with Noetherian underlying
space), and `f : X ⟶ X` finite and surjective (dominant) and PCF in the
normalized sense. Then `f` is PCF along all subvariety chains: for every
proper integral closed subvariety and all preperiods and periods, the return
on the original reduced image is separable and PCF, recursively at every
depth (Definition `def:pcfawd-allsubvar`). -/
theorem isPCFAllSubvarieties_charZero (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsSeparableNormalizedPCF k s f) :
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
  exact isPCFAllSubvarieties_of_normal_finite_cover_charZero k
    (finiteSemiconjugacyPCFTransfer k) (allCodimNormalizedReturnPCFCharZero k)
    s f g ν hcomm hpcfg

/-- **Theorem A in characteristic zero, in the paper's weighted PCF form.**
The weighted local-degree critical locus of the normalization lift has
finite postcritical support. Generic separability follows from
characteristic zero, and the conclusion concerns every original reduced
subvariety return in every codimension. -/
theorem isPCFAllSubvarieties_charZero_of_weightedPCF
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf :
      letI : IsFinite (Palomar.normalizationMap X) :=
        schemeGlobalNormalizationMap_isFinite X k s
      (schemeDeltaDynamicsOfFiniteDominantNormal
        (schemeGlobalNormalizationLift f)).IsPCF) :
    IsPCFAllSubvarieties k s f := by
  have hsep : IsGenericallySeparable f :=
    isGenericallySeparable_of_charZero_field k s f
  have hpcf' : IsSeparableNormalizedPCF k s f :=
    (isSeparableNormalizedPCF_iff_weightedNormalLift k s f).mpr ⟨hsep, hpcf⟩
  exact isPCFAllSubvarieties_charZero k s f hpcf'

#print axioms allCodimNormalizedReturnPCFCharZero
#print axioms isPCFAllSubvarieties_charZero
#print axioms isPCFAllSubvarieties_charZero_of_weightedPCF

end
end Pcf
