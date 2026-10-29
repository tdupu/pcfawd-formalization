/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimCoreAssembly
public import Pcf.Bounding.AllCodimCoreGood
public import Pcf.Bounding.AllSubvarietyFiniteCoverInductionCharZero
public import Pcf.Bounding.AllSubvarietyCharZeroSeparable

/-!
# The normalized blow-up argument in characteristic zero: core and assembly

`latex/paper-p.tex`, Theorem `thm:allcodim-normal`, for `p = 0`. The
characteristic-zero argument is the characteristic-`p` one with the
prime-to-`p` monodromy hypothesis removed: tameness and residue separability
are automatic, and the generic fibre multiplicity is one. Good points are
`AllCodimGoodPoint 1`: the multiplicity condition `μ = 1 ^ b` says `μ = 1`.

This file states the characteristic-zero core (`AllCodimAffineCoreCharZero`),
splits it into finiteness of bad points and étaleness over good points, and
derives the all-codimension input `AllCodimNormalizedReturnPCFCharZero` of the
characteristic-zero all-subvariety induction.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- The per-affine core of `thm:allcodim-normal` in characteristic zero. -/
def AllCodimAffineCoreCharZero (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X] [IsLocallyNoetherian X]
    [NoetherianSpace X] (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (y : X) (_ : y ≠ genericPoint X) (B : Set X) (_ : B.Finite)
    (U : X.affineOpens) (_ : y ∈ (U : X.Opens)),
    ∃ T : Set X, T.Finite ∧
      ∀ (h : X ⟶ X) [IsFinite h] [IsDominant h] (hfix : h y = y)
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

/-- Characteristic-zero **L2**: finitely many bad points, with good points in
the sense `AllCodimGoodPoint 1`. -/
def AllCodimBadFiniteCharZero (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X] [IsLocallyNoetherian X]
    [NoetherianSpace X] (_ : X ⟶ Spec (.of k)) [LocallyOfFiniteType ‹X ⟶ Spec (.of k)›]
    (y : X) (_ : y ≠ genericPoint X) (B : Set X) (_ : B.Finite)
    (U : X.affineOpens) [Nonempty (U : X.Opens)] (hyU : y ∈ (U : X.Opens))
    (a : allCodimCentrePrime U y hyU) (ha : (a : Γ(X, U)) ≠ 0),
    {x : X | (∃ Q : SchemeDivisorPoint (pointClosureIdealSheaf y).subscheme,
        (pointClosureIdealSheaf y).subschemeι Q.1 = x) ∧ x ∈ (U : X.Opens) ∧
      ¬ AllCodimGoodPoint 1 U y hyU a ha B x}.Finite

/-- Characteristic-zero **L1**: étaleness over good points. -/
def AllCodimEtaleOfGoodCharZero (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X] [IsLocallyNoetherian X]
    [NoetherianSpace X] (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (y : X) (_ : y ≠ genericPoint X) (B : Set X)
    (U : X.affineOpens) [Nonempty (U : X.Opens)] (hyU : y ∈ (U : X.Opens))
    (a : allCodimCentrePrime U y hyU) (ha : (a : Γ(X, U)) ≠ 0)
    (h : X ⟶ X) [IsFinite h] [IsDominant h] (hfix : h y = y)
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
      AllCodimGoodPoint 1 U y hyU a ha B
        ((pointClosureIdealSheaf y).subschemeι (Palomar.normalizationMap A (F Q₁.1))) →
      (F.stalkMap Q₁.1).hom.FormallyEtale

/-- The characteristic-zero core from L1 and L2. -/
theorem allCodimAffineCoreCharZero_of_good (k : Type u) [Field k] [CharZero k]
    (hL2 : AllCodimBadFiniteCharZero k) (hL1 : AllCodimEtaleOfGoodCharZero k) :
    AllCodimAffineCoreCharZero k := by
  intro X _ _ _ _ s _ y hy B hB U hyU
  haveI : Nonempty (U : X.Opens) := ⟨⟨y, hyU⟩⟩
  obtain ⟨a, haP, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (allCodimCentrePrime_ne_bot U y hyU hy)
  let a' : allCodimCentrePrime U y hyU := ⟨a, haP⟩
  refine ⟨_, hL2 s y hy B hB U hyU a' ha, ?_⟩
  intro h _ _ hfix hbranch A F Q₁ hxU hxT
  apply hL1 s y hy B U hyU a' ha h hfix hbranch Q₁ hxU
  by_contra hbad
  apply hxT
  refine ⟨?_, hxU, hbad⟩
  letI : IsFinite (Palomar.normalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite A k ((pointClosureIdealSheaf y).subschemeι ≫ s)
  let Qt : SchemeDivisorPoint (Palomar.normalization A) := Q₁.mapFiniteDominantNormal F
  exact ⟨⟨Palomar.normalizationMap A Qt.1,
    coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k
      ((pointClosureIdealSheaf y).subschemeι ≫ s) (Palomar.normalizationMap A) Qt⟩, rfl⟩

/-- **Non-generic case** in characteristic zero. -/
theorem allCodim_return_of_affineCoreCharZero_nonGeneric
    (k : Type u) [Field k] [CharZero k]
    (hcore : AllCodimAffineCoreCharZero k)
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [NoetherianSpace Y] [IsNormalScheme Y]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
    (hpcf : IsSeparableNormalizedPCF k t g)
    (y : Y) (hgen : y ≠ genericPoint Y) (n : ℕ) (_hn : 0 < n)
    (hy : schemePointIterate g n y = y)
    (a : (pointClosureIdealSheaf y).subscheme ⟶ Spec (.of k))
    [LocallyOfFiniteType a] :
    let q := pointClosureReturnMap (End.of g ^ n).asHom y hy
    let A := (pointClosureIdealSheaf y).subscheme
    let ν := Palomar.normalizationMap A
    letI : IsFinite ν := schemeGlobalNormalizationMap_isFinite A k a
    IsSeparableNormalizedPCF k (ν ≫ a) (schemeGlobalNormalizationLift q) := by
  intro q A ν
  letI : IsFinite ν := schemeGlobalNormalizationMap_isFinite A k a
  let F := schemeGlobalNormalizationLift q
  let ι := (pointClosureIdealSheaf y).subschemeι
  let gn := (End.of g ^ n).asHom
  obtain ⟨hsep, hpcfg⟩ := (normalScheme_isSeparableNormalizedPCF_iff k t g).mp hpcf
  let D := unnormalizedDynamicsOfFiniteDominantNormalSeparable g hsep
  let B : Set Y := Subtype.val '' D.nonEtalePostcriticalSet
  have hB : B.Finite := Set.Finite.image _ hpcfg
  have hcov : (Set.univ : Set Y) ⊆ ⋃ U : Y.affineOpens, (U : Set Y) := by
    intro x _
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : Y.Opens) from trivial)
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  obtain ⟨cov, hcov'⟩ := isCompact_univ.elim_finite_subcover
    (fun U : Y.affineOpens => (U : Set Y)) (fun U => U.1.isOpen) hcov
  classical
  let TU : Y.affineOpens → Set Y := fun U =>
    if hU : y ∈ (U : Y.Opens) then Classical.choose (hcore t y hgen B hB U hU) else ∅
  have hTU (U : Y.affineOpens) : (TU U).Finite := by
    by_cases hU : y ∈ (U : Y.Opens)
    · simp only [TU, hU, ↓reduceDIte]
      exact (Classical.choose_spec (hcore t y hgen B hB U hU)).1
    · simp only [TU, hU, ↓reduceDIte]
      exact Set.finite_empty
  let TX : Set Y := ⋃ U ∈ cov, TU U
  have hTX : TX.Finite := Set.Finite.biUnion cov.finite_toSet fun U _ => hTU U
  let T : Set (SchemeDivisorPoint (Palomar.normalization A)) :=
    {Q | ι (ν Q.1) ∈ TX}
  have hT : T.Finite := by
    have hpre : ((ν ≫ ι) ⁻¹' TX).Finite := (ν ≫ ι).finite_preimage hTX
    change (Subtype.val ⁻¹' ((ν ≫ ι) ⁻¹' TX)).Finite
    exact hpre.preimage Subtype.val_injective.injOn
  have hbound : ∀ (m : ℕ), 1 ≤ m →
      ∀ Q ∈ schemeDivisorNonEtaleLocus (End.of F ^ m).asHom,
      (fun d : SchemeDivisorPoint (Palomar.normalization A) =>
        d.mapFiniteDominantNormal F)^[m] Q ∈ T := by
    intro m hm Q hQ
    let h := (End.of gn ^ m).asHom
    have hfix : h y = y := end_pow_apply_eq_of_apply_eq gn y hy m
    have hpow : h = (End.of g ^ (n * m)).asHom := by
      change ((End.of g ^ n) ^ m).asHom = _
      rw [pow_mul]
    have hbranchh : ∀ (h' : Y ⟶ Y) (_ : h' = (End.of g ^ (n * m)).asHom),
        ∀ w : SchemeDivisorPoint Y, h' w.1 ∉ B → (h'.stalkMap w.1).hom.FormallyEtale := by
      intro h' e w hw
      subst e
      exact formallyEtale_end_pow_of_notMem_postcritical g hsep (n * m) w hw
    let Fh := schemeGlobalNormalizationLift (pointClosureReturnMap h y hfix)
    have heq : (End.of F ^ m).asHom = Fh := by
      rw [← schemeGlobalNormalizationLift_pow]
      exact schemeGlobalNormalizationLift_congr (pointClosureReturnMap_iterate gn y hy m)
    have hQ' : ¬ (Fh.stalkMap Q.1).hom.FormallyEtale := by
      have := hQ
      change ¬ (((End.of F ^ m).asHom).stalkMap Q.1).hom.FormallyEtale at this
      rwa [heq] at this
    change ι (ν ((fun d : SchemeDivisorPoint (Palomar.normalization A) =>
      d.mapFiniteDominantNormal F)^[m] Q).1) ∈ TX
    rw [mapFiniteDominantNormal_iterate_val, heq]
    obtain ⟨U, hUcov, hxU⟩ : ∃ U ∈ cov, ι (ν (Fh Q.1)) ∈ (U : Y.Opens) := by
      have := hcov' (Set.mem_univ (ι (ν (Fh Q.1))))
      simp only [Set.mem_iUnion] at this
      obtain ⟨U, hU, hx⟩ := this
      exact ⟨U, hU, hx⟩
    have hyU : y ∈ (U : Y.Opens) :=
      (pointClosure_specializes y (ν (Fh Q.1))).mem_open U.1.isOpen hxU
    by_contra hxT
    apply hQ'
    have hspec := (Classical.choose_spec (hcore t y hgen B hB U hyU)).2 h hfix
      (hbranchh h hpow) Q hxU
    apply hspec
    intro hmem
    apply hxT
    refine Set.mem_biUnion hUcov ?_
    simp only [TU, hyU, ↓reduceDIte]
    exact hmem
  have hsepF : IsGenericallySeparable F := isGenericallySeparable_of_charZero_field k (ν ≫ a) F
  haveI : IsLocallyNoetherian (Palomar.normalization A) :=
    LocallyOfFiniteType.isLocallyNoetherian ν
  haveI : CompactSpace (Palomar.normalization A) :=
    QuasiCompact.compactSpace_of_compactSpace ν
  haveI : IsNoetherian (Palomar.normalization A) := ⟨⟩
  rw [normalScheme_isSeparableNormalizedPCF_iff k (ν ≫ a) F]
  exact ⟨hsepF, isNormalNonEtalePCF_of_uniform_iterate_support F hsepF T hT hbound⟩

/-- **The characteristic-zero all-codimension input** from the affine core. -/
theorem allCodimNormalizedReturnPCFCharZero_of_affineCore
    (k : Type u) [Field k] [CharZero k]
    (hcore : AllCodimAffineCoreCharZero k) : AllCodimNormalizedReturnPCFCharZero k := by
  intro Y _ _ _ _ t _ g _ _ hpcf y n hn hy a _
  by_cases hgen : y = genericPoint Y
  · exact allCodim_return_generic k t g hpcf y hgen n hn hy a
  · exact allCodim_return_of_affineCoreCharZero_nonGeneric k hcore t g hpcf y hgen n hn hy a

#print axioms allCodimAffineCoreCharZero_of_good
#print axioms allCodim_return_of_affineCoreCharZero_nonGeneric
#print axioms allCodimNormalizedReturnPCFCharZero_of_affineCore

end
end Pcf
