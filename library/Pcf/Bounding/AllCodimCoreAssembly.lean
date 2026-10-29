/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimCoreAssemblyBranch

/-!
# Assembling the all-codimension return from the affine core

`AllCodimAffineCore` bounds, on one affine open and uniformly in a finite
self-map, the non-étale divisors of the normalized return. This module covers
the ambient scheme by finitely many affines, applies the core to every iterate
of the return (whose branch divisors lie over the postcritical set of the
ambient map), and deduces `AllCodimNormalizedReturnPCF`, the remaining input
of the all-subvariety induction for `latex/paper-p.tex`, Theorem `thm:A`.
The return on the closure of the generic point is handled by the PCF
transfer.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- Every point of the reduced closure of `y` specializes from `y`. -/
theorem pointClosure_specializes {Y : Scheme.{u}} (y : Y)
    (z : (pointClosureIdealSheaf y).subscheme) :
    y ⤳ (pointClosureIdealSheaf y).subschemeι z := by
  have hz : (pointClosureIdealSheaf y).subschemeι z ∈
      Set.range (pointClosureIdealSheaf y).subschemeι := ⟨z, rfl⟩
  rw [Scheme.IdealSheafData.range_subschemeι] at hz
  unfold pointClosureIdealSheaf at hz
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hz
  exact specializes_iff_mem_closure.mpr hz

/-- Iterating the divisor pushforward of a finite dominant normal self-map
moves the point by the scheme iterate. -/
theorem mapFiniteDominantNormal_iterate_val {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormalScheme X] (F : X ⟶ X) [IsFinite F] [IsDominant F]
    (m : ℕ) (Q : SchemeDivisorPoint X) :
    ((fun d : SchemeDivisorPoint X => d.mapFiniteDominantNormal F)^[m] Q).1 =
      (End.of F ^ m).asHom.base Q.1 := by
  induction m generalizing Q with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih, pow_succ]
      rfl

/-- The normalized lift depends only on the morphism. -/
theorem schemeGlobalNormalizationLift_congr {X : Scheme.{u}} [IsIntegral X]
    {f f' : X ⟶ X} [IsFinite f] [IsDominant f] [IsFinite f'] [IsDominant f']
    [IsIso (schemeNormalizationComparison f)] [IsIso (schemeNormalizationComparison f')]
    (e : f = f') : schemeGlobalNormalizationLift f = schemeGlobalNormalizationLift f' := by
  subst e
  rfl

/-- **Non-generic case.** The affine core gives the normalized return on the
closure of a non-generic periodic point separable normalized PCF. -/
theorem allCodim_return_of_affineCore_nonGeneric
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    (hcore : AllCodimAffineCore p k)
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [NoetherianSpace Y] [IsNormalScheme Y]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
    (hpcf : IsSeparableNormalizedPCF k t g) (hmono : IsPrimeToPMonodromyMap p g)
    (y : Y) (hgen : y ≠ genericPoint Y) (n : ℕ) (hn : 0 < n)
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
  -- the postcritical support of `g`
  obtain ⟨hsep, hpcfg⟩ := (normalScheme_isSeparableNormalizedPCF_iff k t g).mp hpcf
  let D := unnormalizedDynamicsOfFiniteDominantNormalSeparable g hsep
  let B : Set Y := Subtype.val '' D.nonEtalePostcriticalSet
  have hB : B.Finite := Set.Finite.image _ hpcfg
  -- a finite affine cover
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
  -- the bound for every iterate
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
    have hpos : 0 < n * m := Nat.mul_pos hn hm
    have hmonoh : ∀ (h' : Y ⟶ Y) (_ : h' = (End.of g ^ (n * m)).asHom)
        [IsFinite h'] [IsDominant h'], IsPrimeToPMonodromyMap p h' := by
      intro h' e _ _
      subst e
      exact isPrimeToPMonodromyMap_pow_pos p g hmono (n * m) hpos
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
      (hmonoh h hpow) (hbranchh h hpow) Q hxU
    apply hspec
    intro hmem
    apply hxT
    refine Set.mem_biUnion hUcov ?_
    simp only [TU, hyU, ↓reduceDIte]
    exact hmem
  -- conclusion, as in `allCodimNormalizedReturnPCF_of_uniformReturnSupport`
  have hmonoF : IsPrimeToPMonodromyMap p F :=
    finiteType_pointClosureReturn_iterate_normalization_primeToPMonodromy p hp k g t hmono
      n hn y hy
  have hsepF : IsGenericallySeparable F :=
    isGenericallySeparable_of_isPrimeToPMonodromyMap p F hmonoF
  haveI : IsLocallyNoetherian (Palomar.normalization A) :=
    LocallyOfFiniteType.isLocallyNoetherian ν
  haveI : CompactSpace (Palomar.normalization A) :=
    QuasiCompact.compactSpace_of_compactSpace ν
  haveI : IsNoetherian (Palomar.normalization A) := ⟨⟩
  rw [normalScheme_isSeparableNormalizedPCF_iff k (ν ≫ a) F]
  exact ⟨hsepF, isNormalNonEtalePCF_of_uniform_iterate_support F hsepF T hT hbound⟩

/-- **Generic case.** On the closure of the generic point the return is
conjugate to an iterate of the ambient map, and the PCF transfer applies. -/
theorem allCodim_return_generic
    (k : Type u) [Field k]
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [NoetherianSpace Y] [IsNormalScheme Y]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
    (hpcf : IsSeparableNormalizedPCF k t g)
    (y : Y) (hgen : y = genericPoint Y) (n : ℕ) (hn : 0 < n)
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
  let ι := (pointClosureIdealSheaf y).subschemeι
  let gn := (End.of g ^ n).asHom
  haveI : Surjective ι := by
    constructor
    intro x
    have hx : x ∈ Set.range ι := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      unfold pointClosureIdealSheaf
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hgen]
      change x ∈ closure ({genericPoint Y} : Set Y)
      rw [(genericPoint_spec Y).def]
      trivial
    exact hx
  haveI : IsIso ι := isIso_of_isClosedImmersion_of_surjective ι
  let π : Y ⟶ A := inv ι
  have h1 : q ≫ ι = ι ≫ gn := pointClosureSubschemeMap_subschemeι gn y y hy
  have hcomm : gn ≫ π = π ≫ q := by
    simp only [π]
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← h1, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hup : IsSeparableNormalizedPCF k (π ≫ a) gn :=
    (isSeparableNormalizedPCF_base_iff k t (π ≫ a) gn).mp
      ((isSeparableNormalizedPCF_pow_iff k t g n hn).mpr hpcf)
  have hdown := finiteSemiconjugacyPCFTransfer k a q gn π hcomm hup
  rw [isSeparableNormalizedPCF_iff_normalLift k a q] at hdown
  obtain ⟨hs, hp'⟩ := hdown
  haveI : IsLocallyNoetherian (Palomar.normalization A) :=
    LocallyOfFiniteType.isLocallyNoetherian ν
  haveI : CompactSpace (Palomar.normalization A) :=
    QuasiCompact.compactSpace_of_compactSpace ν
  haveI : IsNoetherian (Palomar.normalization A) := ⟨⟩
  rw [normalScheme_isSeparableNormalizedPCF_iff k (ν ≫ a) (schemeGlobalNormalizationLift q)]
  exact ⟨_, hp'⟩

/-- **The affine core gives the all-codimension normalized return input.** -/
theorem allCodimNormalizedReturnPCF_of_affineCore
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    (hcore : AllCodimAffineCore p k) : AllCodimNormalizedReturnPCF p k := by
  intro Y _ _ _ _ t _ g _ _ hpcf hmono y n hn hy a _
  by_cases hgen : y = genericPoint Y
  · exact allCodim_return_generic k t g hpcf y hgen n hn hy a
  · exact allCodim_return_of_affineCore_nonGeneric p hp k hcore t g hpcf hmono y hgen n hn hy a

#print axioms allCodim_return_of_affineCore_nonGeneric
#print axioms allCodim_return_generic
#print axioms allCodimNormalizedReturnPCF_of_affineCore

end
end Pcf
