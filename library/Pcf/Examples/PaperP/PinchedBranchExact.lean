/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedPostcritical
public import Pcf.Examples.PaperP.FrobeniusPinchingBranchExact

/-!
# The pinched plane: `PC(f) = {ν(V(z)), ν(V(w))}` and `f` is PCF

For `paper-p.tex`, Example `ex:pinched`: "`branch(f) = ν(branch(f̃))` …, `f̃` is étale exactly off
`V(z) ∪ V(w)` and `branch(f̃) = V(z) ∪ V(w)`. Both lines are invariant under `f̃`, so
`PC(f) = PC₀(f) = PC₁(f) = {ν(V(z)), ν(V(w))}`."

The ambient `f̃ = (z², w²)` is literally the map `Hs` of `ex:frobenius-pinching`
(`fTilde_eq_Hs`), so the étale/ramification computations
(`FrobeniusPinchingPCF.Hs_stalk_formallyEtale`,
`FrobeniusPinchingBranchExact.Hs_ramificationIdx_axis_ne_one`) are reused verbatim.

* `lift_eq_canonical`: the canonical lift of `f` to `normalization(X) ≅ 𝔸²` is `f̃`.
* `weightedBranchPointSet_eq`: the normalized weighted branch divisors of `f` are exactly
  `ν(V(z))`, `ν(V(w))` (`axisImage 0`, `axisImage 1`, distinct: `axisImage_injective`).
* `weightedPostcriticalPointSet_eq`: `PC(f) = {ν(V(z)), ν(V(w))}`.
* `f_isPCF`, `f_isPCF_zero_one`: `f` is PCF, and (via `pinched_postcritical_coincide`)
  `PC₀(f)`, `PC₁(f)` have the same generic points and `f` is `0`-PCF and `1`-PCF.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedBranchExact

open AlgebraicGeometry CategoryTheory MvPolynomial Pcf.Examples.Pinched
open Pcf.Examples.PaperP.PinchedNormalization Pcf.Examples.PaperP.PinchedAmbient
open Pcf.Examples.PaperP.FrobeniusPinchingNormalization (Hs)
open Pcf.Examples.PaperP.FrobeniusPinchingPCF (axisPt axisPt_coheight eq_axisPt
  Hs_stalk_formallyEtale iso_stalk_formallyEtale)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k
local notation "S" => PlaneRing k

/-- The pinched surface `X`. -/
noncomputable abbrev Xs := Spec (.of R)

theorem fTilde_eq_Hs : fTilde k = Hs k := by
  unfold fTilde Hs
  rfl

theorem two_ne_zero' : (2 : k) ≠ 0 := two_ne_zero

/-- The candidate lift `iso⁻¹ ∘ f̃ ∘ iso` on the normalization. -/
noncomputable def lift : Pcf.Palomar.normalization (Xs k) ⟶ Pcf.Palomar.normalization (Xs k) :=
  (pinchedNormalizationIso k).hom ≫ Hs k ≫ (pinchedNormalizationIso k).inv

theorem lift_comp_normalizationMap :
    lift k ≫ Pcf.Palomar.normalizationMap (Xs k) =
      Pcf.Palomar.normalizationMap (Xs k) ≫ fScheme k := by
  rw [← pinchedNormalizationIso_hom_comp, lift]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← fTilde_eq_Hs, fScheme_comp_nu]

/-- Maps from the spectrum of a field into `𝔸²` are determined by their composite to `X` when that
composite is injective on rings. -/
theorem spec_ext {L : CommRingCat} (hL : IsField L) (u v : Spec L ⟶ Spec (.of S))
    (c : R →+* L) (hc : Function.Injective c)
    (hu : u ≫ nu k = Spec.map (CommRingCat.ofHom c))
    (hv : v ≫ nu k = Spec.map (CommRingCat.ofHom c)) : u = v := by
  letI : Field L := hL.toField
  obtain ⟨a, rfl⟩ := Spec.map_surjective u
  obtain ⟨b, rfl⟩ := Spec.map_surjective v
  rw [← Spec.map_comp] at hu hv
  have ha := congrArg CommRingCat.Hom.hom (Spec.map_injective hu)
  have hb := congrArg CommRingCat.Hom.hom (Spec.map_injective hv)
  congr 1
  apply CommRingCat.hom_ext
  apply BirationalAffineNormalization.ringHom_ext_of_birational R S
  · exact ha.trans hb.symm
  · change Function.Injective ((CommRingCat.ofHom (algebraMap R S) ≫ a).hom)
    rw [Spec.map_injective hu]
    exact hc

/-- The generic inclusion of `X` composed with `f`, as a ring map. -/
noncomputable def genericRing : R →+* (Xs k).functionField :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫
    (Xs k).presheaf.germ ⊤ (genericPoint (Xs k)) trivial).hom.comp (fStar k)

theorem genericRing_injective : Function.Injective (genericRing k) := by
  intro a b h
  apply fStar_injective k
  have hg := germ_injective_of_isIntegral (Xs k) (U := ⊤) (genericPoint (Xs k)) trivial
  have h' := hg h
  exact (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.injective h'

theorem genericIncl_f :
    Pcf.schemeGenericInclusion (Xs k) ≫ fScheme k =
      Spec.map (CommRingCat.ofHom (genericRing k)) := by
  unfold Pcf.schemeGenericInclusion fScheme genericRing
  rw [Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rfl

theorem lift_generic :
    Pcf.Palomar.genericToNormalization (Xs k) ≫ lift k =
      Pcf.schemeGenericMorphism (fScheme k) ≫ Pcf.Palomar.genericToNormalization (Xs k) := by
  apply (cancel_mono (pinchedNormalizationIso k).hom).mp
  have hG : Pcf.Palomar.genericToNormalization (Xs k) ≫ (pinchedNormalizationIso k).hom =
      BirationalAffineNormalization.genericToCover R S :=
    BirationalAffineNormalization.genericToNormalization_normalizationToCover _ _
  simp only [lift, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hG]
  have hgc := BirationalAffineNormalization.genericToCover_comp R S
  apply spec_ext k (Field.toIsField _) _ _ (genericRing k) (genericRing_injective k)
  · rw [Category.assoc, ← fTilde_eq_Hs, fScheme_comp_nu, ← Category.assoc, hgc, genericIncl_f]
  · rw [Category.assoc, hgc, Pcf.schemeGenericMorphism_comp, genericIncl_f]

/-- **The canonical lift of `f` to the normalization is `f̃ = (z², w²)`.** -/
theorem lift_eq_canonical : lift k = Pcf.schemeGlobalNormalizationMorphism (fScheme k) :=
  Pcf.schemeGlobalNormalizationMorphism_unique _ _ (lift_comp_normalizationMap k)
    (lift_generic k)

/-! ### Branch divisors -/

instance fTilde_isFinite : IsFinite (fTilde k) := by
  rw [fTilde_eq_Hs]; exact FrobeniusPinchingPCF.Hs_finite k 2

theorem lift_finite : IsFinite (lift k) := by
  haveI := FrobeniusPinchingPCF.Hs_finite k 2
  unfold lift; infer_instance

instance normalizationFinite : IsFinite (Pcf.Palomar.normalizationMap (Xs k)) :=
  BirationalAffineNormalization.normalizationMap_isFinite R S

theorem lift_stalk_formallyEtale (z : Pcf.Palomar.normalization (Xs k))
    (hx : (X 0 : S) ∉ ((pinchedNormalizationIso k).hom z).asIdeal)
    (hy : (X 1 : S) ∉ ((pinchedNormalizationIso k).hom z).asIdeal) :
    ((lift k).stalkMap z).hom.FormallyEtale := by
  unfold lift
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
  refine RingHom.FormallyEtale.comp ?_ (iso_stalk_formallyEtale _ _)
  exact RingHom.FormallyEtale.comp (iso_stalk_formallyEtale _ _)
    (Hs_stalk_formallyEtale k (two_ne_zero' k) _ hx hy)

theorem delta_gt_one_axis (d : Pcf.SchemeDivisorPoint (Pcf.Palomar.normalization (Xs k)))
    (hd : 1 < Pcf.schemeDivisorDelta (lift k) d) :
    ∃ i : Fin 2, (pinchedNormalizationIso k).hom d.1 = axisPt k i := by
  haveI := lift_finite k
  have hcoh : Order.coheight ((pinchedNormalizationIso k).hom d.1) = 1 :=
    (AlgebraicGeometry.coheight_eq_of_isOpenImmersion (pinchedNormalizationIso k).hom).trans d.2
  by_cases h0 : (X 0 : S) ∈ ((pinchedNormalizationIso k).hom d.1).asIdeal
  · exact ⟨0, eq_axisPt k _ hcoh 0 h0⟩
  by_cases h1 : (X 1 : S) ∈ ((pinchedNormalizationIso k).hom d.1).asIdeal
  · exact ⟨1, eq_axisPt k _ hcoh 1 h1⟩
  exfalso
  have := Pcf.schemeDivisorDelta_eq_one_of_formallyEtale (lift k) d
    (lift_stalk_formallyEtale k d.1 h0 h1)
  omega

theorem lift_ramificationIdx_eq (z : Pcf.SchemeDivisorPoint (Pcf.Palomar.normalization (Xs k)))
    (hz : Order.coheight ((pinchedNormalizationIso k).hom z.1) = 1) :
    Pcf.schemeDivisorRamificationIdx (lift k) z =
      Pcf.schemeDivisorRamificationIdx (Hs k) ⟨(pinchedNormalizationIso k).hom z.1, hz⟩ := by
  let a := (pinchedNormalizationIso k).hom
  let b := (pinchedNormalizationIso k).inv
  let y := Hs k (a z.1)
  let e₁ := (asIso (b.stalkMap y)).commRingCatIsoToRingEquiv
  let e₂ := (asIso (a.stalkMap z.1)).commRingCatIsoToRingEquiv.symm
  have hφ : (lift k).stalkMap z.1 = b.stalkMap y ≫ (Hs k).stalkMap (a z.1) ≫ a.stalkMap z.1 := by
    unfold lift
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
    simp only [Category.assoc]
    rfl
  have hcomm : ((Hs k).stalkMap (a z.1)).hom.comp e₁.toRingHom =
      e₂.toRingHom.comp ((lift k).stalkMap z.1).hom := by
    apply RingHom.ext
    intro r
    rw [hφ]
    change _ = e₂ ((a.stalkMap z.1).hom (((Hs k).stalkMap (a z.1)).hom ((b.stalkMap y).hom r)))
    change _ = (asIso (a.stalkMap z.1)).commRingCatIsoToRingEquiv.symm
      ((asIso (a.stalkMap z.1)).commRingCatIsoToRingEquiv _)
    rw [RingEquiv.symm_apply_apply]
    rfl
  exact Pcf.ramificationIdx_maximalIdeal_eq_of_ringEquiv _ _ e₁ e₂ hcomm

theorem delta_gt_one_of_axis (i : Fin 2) :
    1 < Pcf.schemeDivisorDelta (lift k)
      ⟨(pinchedNormalizationIso k).inv (axisPt k i),
        (AlgebraicGeometry.coheight_eq_of_isOpenImmersion (pinchedNormalizationIso k).inv).trans
          (axisPt_coheight k i)⟩ := by
  haveI := lift_finite k
  set z : Pcf.SchemeDivisorPoint (Pcf.Palomar.normalization (Xs k)) :=
    ⟨(pinchedNormalizationIso k).inv (axisPt k i),
      (AlgebraicGeometry.coheight_eq_of_isOpenImmersion (pinchedNormalizationIso k).inv).trans
        (axisPt_coheight k i)⟩
  have hz : (pinchedNormalizationIso k).hom z.1 = axisPt k i := by
    change ((pinchedNormalizationIso k).inv ≫ (pinchedNormalizationIso k).hom) (axisPt k i) = _
    rw [Iso.inv_hom_id]
    rfl
  have hcoh : Order.coheight ((pinchedNormalizationIso k).hom z.1) = 1 := by
    rw [hz]; exact axisPt_coheight k i
  have he : Pcf.schemeDivisorRamificationIdx (lift k) z ≠ 1 := by
    rw [lift_ramificationIdx_eq k z hcoh]
    have h := FrobeniusPinchingBranchExact.Hs_ramificationIdx_axis_ne_one k 2 i
    have hzz : (⟨(pinchedNormalizationIso k).hom z.1, hcoh⟩ :
        Pcf.SchemeDivisorPoint (Spec (.of S))) = ⟨axisPt k i, axisPt_coheight k i⟩ :=
      Subtype.ext hz
    rw [hzz]
    exact h
  have hpos := Pcf.schemeDivisorDelta_pos_of_isFinite (lift k) z
  unfold Pcf.schemeDivisorDelta at hpos ⊢
  set e := Pcf.schemeDivisorRamificationIdx (lift k) z
  have key : ∀ n : ℕ, 0 < e * n → 1 < e * n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, mul_zero] at hn; exact absurd hn (lt_irrefl 0)
    have he0 : e ≠ 0 := fun h => by rw [h, zero_mul] at hn; exact lt_irrefl 0 hn
    have : 2 ≤ e := by omega
    nlinarith
  exact key _ hpos

/-- `ν(V(z))` and `ν(V(w))`. -/
noncomputable def axisImage (i : Fin 2) : Xs k := nu k (axisPt k i)

theorem fTilde_axisPt (i : Fin 2) : fTilde k (axisPt k i) = axisPt k i := by
  rw [fTilde_eq_Hs]; exact FrobeniusPinchingPCF.Hs_axisPt k 2 i

theorem f_axisImage (i : Fin 2) : fScheme k (axisImage k i) = axisImage k i := by
  unfold axisImage
  rw [← Scheme.Hom.comp_apply, ← fScheme_comp_nu, Scheme.Hom.comp_apply, fTilde_axisPt]

/-- `ν(V(z)) ≠ ν(V(w))`: `w ∈ R` vanishes on `V(w)` but not on `V(z)`. -/
theorem axisImage_injective : Function.Injective (axisImage k) := by
  have hmem : ∀ i : Fin 2, (PinchedRing.mk k (X 1) (w_mem k) : R) ∈ (axisImage k i).asIdeal ↔
      (X 1 : S) ∈ Ideal.span {(X i : S)} := fun i => Iff.rfl
  have hne : axisImage k 0 ≠ axisImage k 1 := by
    intro h
    have h1 := (hmem 1).mpr (Ideal.mem_span_singleton_self _)
    have hI : (axisImage k 0).asIdeal = (axisImage k 1).asIdeal := congrArg PrimeSpectrum.asIdeal h
    have h0 := hI ▸ h1
    rw [hmem 0, Ideal.mem_span_singleton] at h0
    exact absurd ((MvPolynomial.X_dvd_X).mp h0) (by decide)
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij hne
  · exact absurd hij.symm hne
  · rfl

/-- **The normalized weighted branch divisors of `f` are exactly `ν(V(z))` and `ν(V(w))`.** -/
theorem weightedBranchPointSet_eq :
    Pcf.weightedBranchPointSet (fScheme k) = Set.range (axisImage k) := by
  have hF := (lift_eq_canonical k).symm
  apply Set.Subset.antisymm
  · rintro q ⟨r, ⟨d, hdr, hd⟩, rfl⟩
    rw [hF] at hd
    obtain ⟨i, hi⟩ := delta_gt_one_axis k d hd
    refine ⟨i, ?_⟩
    subst hdr
    change axisImage k i = Pcf.Palomar.normalizationMap (Xs k)
      (Pcf.schemeGlobalNormalizationMorphism (fScheme k) d.1)
    rw [hF, ← Scheme.Hom.comp_apply, lift_comp_normalizationMap, Scheme.Hom.comp_apply,
      ← pinchedNormalizationIso_hom_comp, Scheme.Hom.comp_apply, hi]
    exact (f_axisImage k i).symm
  · rintro _ ⟨i, rfl⟩
    let d : Pcf.SchemeDivisorPoint (Pcf.Palomar.normalization (Xs k)) :=
      ⟨(pinchedNormalizationIso k).inv (axisPt k i),
        (AlgebraicGeometry.coheight_eq_of_isOpenImmersion (pinchedNormalizationIso k).inv).trans
          (axisPt_coheight k i)⟩
    have hδ := delta_gt_one_of_axis k i
    refine ⟨d.mapFiniteDominantNormal (Pcf.schemeGlobalNormalizationMorphism (fScheme k)),
      ⟨d, rfl, ?_⟩, ?_⟩
    · rw [hF]; exact hδ
    · have hi : (pinchedNormalizationIso k).hom d.1 = axisPt k i := by
        change ((pinchedNormalizationIso k).inv ≫ (pinchedNormalizationIso k).hom)
          (axisPt k i) = _
        rw [Iso.inv_hom_id]
        rfl
      change Pcf.Palomar.normalizationMap (Xs k)
        (Pcf.schemeGlobalNormalizationMorphism (fScheme k) d.1) = axisImage k i
      rw [hF, ← Scheme.Hom.comp_apply, lift_comp_normalizationMap, Scheme.Hom.comp_apply,
        ← pinchedNormalizationIso_hom_comp, Scheme.Hom.comp_apply, hi]
      exact f_axisImage k i

/-- **`PC(f) = {ν(V(z)), ν(V(w))}`.**

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem weightedPostcriticalPointSet_eq :
    Pcf.weightedPostcriticalPointSet (fScheme k) = Set.range (axisImage k) := by
  apply Set.Subset.antisymm
  · intro q hq
    simp only [Pcf.weightedPostcriticalPointSet, Set.mem_iUnion] at hq
    obtain ⟨n, z, hz, rfl⟩ := hq
    rw [weightedBranchPointSet_eq] at hz
    obtain ⟨i, rfl⟩ := hz
    refine ⟨i, ?_⟩
    induction n with
    | zero => rfl
    | succ n ih =>
        change axisImage k i = (fScheme k : _ → _)^[n + 1] (axisImage k i)
        rw [Function.iterate_succ_apply', ← show axisImage k i =
          (fScheme k : _ → _)^[n] (axisImage k i) from ih, f_axisImage]
  · intro q hq
    simp only [Pcf.weightedPostcriticalPointSet, Set.mem_iUnion]
    exact ⟨0, q, by rw [weightedBranchPointSet_eq]; exact hq, rfl⟩

/-! ### `f` is PCF, `0`-PCF and `1`-PCF -/

open Pcf.Examples.PaperP.PinchedPostcritical in
/-- **`f` is PCF** (weighted normalized, downstairs form of `def:pcf`). -/
theorem f_isPCF :
    Pcf.IsWeightedNormalizedPCFDownstairs k (structureMap k) (fScheme k) := by
  apply (Pcf.isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite k
    (structureMap k) _).2
  convert Set.finite_range (axisImage k)
  exact weightedPostcriticalPointSet_eq k

open Pcf.Examples.PaperP.PinchedPostcritical in
/-- **`PC(f) = PC₀(f) = PC₁(f) = {ν(V(z)), ν(V(w))}`** (generic points), and `f` is `0`-PCF and
`1`-PCF.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem postcritical_eq_and_isPCF :
    Subtype.val '' Pcf.schemeUnnormalizedPostcriticalSet false k (structureMap k) (fScheme k) =
        Set.range (axisImage k) ∧
      Subtype.val '' Pcf.schemeUnnormalizedPostcriticalSet true k (structureMap k) (fScheme k) =
        Set.range (axisImage k) ∧
      Pcf.IsSchemeUnnormalizedPCF false k (structureMap k) (fScheme k) ∧
      Pcf.IsSchemeUnnormalizedPCF true k (structureMap k) (fScheme k) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := pinched_postcritical_coincide k
  have hPC : Pcf.weightedPostcriticalPointSet (fScheme k) = Set.range (axisImage k) :=
    weightedPostcriticalPointSet_eq k
  refine ⟨?_, ?_, h3.mp (f_isPCF k), h4.mp (h3.mp (f_isPCF k))⟩
  · rw [← h1]; exact hPC
  · rw [← h2, ← h1]; exact hPC

#print axioms lift_eq_canonical
#print axioms weightedBranchPointSet_eq
#print axioms weightedPostcriticalPointSet_eq
#print axioms axisImage_injective
#print axioms f_isPCF
#print axioms postcritical_eq_and_isPCF

end Pcf.Examples.PaperP.PinchedBranchExact
