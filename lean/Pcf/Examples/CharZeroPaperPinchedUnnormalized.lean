/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperPinchedLine
public import Pcf.PaperCharZero.SupportingDictionary

/-!
# Unnormalized branch loci of the pinched plane, `paper.tex`, Example `ex:pinched`

For the actual map `f : X → X`:

* `fiber_isReduced_iff_plane`, `stalk_formallyEtale_iff_plane`: at every integral
  effective divisor, the actual fibre and the actual stalk map of `f` agree with those
  of `f̃ = (z,w) ↦ (z²,w²)` at any point of `𝔸²` above it. The proof chooses `c ∈ 𝔪_o`
  with `f*(c) ∈ 𝔪_o` and `c` outside the divisor, and compares the actual pullback
  squares over `D(c)` (where `ν` is an isomorphism);
* `ambient_nonreducedFibreBranch`, `ambient_nonEtaleBranch`: the nonreduced-fibre and
  non-étale divisorial branch loci of `f` are both exactly `{ν(V(z)), ν(V(w))}`;
* `ambient_pcf_nonreducedFibre`, `ambient_pcf_nonEtale`: `f` is PCF for both
  unnormalized conventions (the normalized one is `ambient_isNormalizedPCF`);
* `ambient_normalizedBranch_divisors`: the three conventions give the same divisors.

No branch or PCF assertion is an input.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperPinched

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Pcf.PaperCharZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

/-! ### Transport of fibres and stalk maps along open immersions -/

section Transport

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- In a pullback square along an open immersion `g`, the fibre of `snd` over `y` is
isomorphic to the fibre of `f` over `g y`. -/
theorem fiber_isReduced_iff_of_isPullback (h : IsPullback fst snd f g) [IsOpenImmersion g]
    (y : Y) : IsReduced (snd.fiber y) ↔ IsReduced (f.fiber (g y)) := by
  have H := isPullback_fiberToSpecResidueField_of_isPullback h y
  have : IsIso (g.residueFieldMap y) := inferInstance
  have hi : IsIso (Spec.map (g.residueFieldMap y)) := inferInstance
  obtain ⟨t, ht⟩ : ∃ t : snd.fiber y ⟶ f.fiber (g y), IsIso t := ⟨_, H.isIso_fst_of_isIso⟩
  constructor
  · intro hr
    exact @isReduced_of_isOpenImmersion _ _ (inv t) inferInstance hr
  · intro hr
    exact @isReduced_of_isOpenImmersion _ _ t inferInstance hr

/-- In a commutative square whose two horizontal maps are open immersions, the stalk
maps of the vertical maps are simultaneously formally étale. -/
theorem stalk_formallyEtale_iff_of_comm (w : fst ≫ f = snd ≫ g) [IsOpenImmersion fst]
    [IsOpenImmersion g] (x : P) :
    (snd.stalkMap x).hom.FormallyEtale ↔ (f.stalkMap (fst x)).hom.FormallyEtale := by
  have e := Scheme.Hom.stalkMap_congr_hom (fst ≫ f) (snd ≫ g) w x
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e
  have key : (f.stalkMap (fst x) ≫ fst.stalkMap x).hom.FormallyEtale ↔
      (snd.stalkMap x).hom.FormallyEtale := by
    rw [e]
    exact (formallyEtale_respectsIso.cancel_left_isIso _ _).trans
      (formallyEtale_respectsIso.cancel_left_isIso _ _)
  exact key.symm.trans (formallyEtale_respectsIso.cancel_right_isIso _ _)

end Transport

/-! ### Basic opens of `X` over which `ν` and `f` are compatible -/

variable (k : Type u) [Field k] [CharZero k]

/-- The maximal ideal of `ν(a, 1)`. -/
def mPoint (a : k) : Ideal (PinchedRing k) :=
  RingHom.ker ((MvPolynomial.aeval ![a, 1]).toRingHom.comp
    (algebraMap (PinchedRing k) (PlaneRing k)))

instance mPoint_isMaximal (a : k) : (mPoint k a).IsMaximal := by
  unfold mPoint
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  refine ⟨algebraMap k (PinchedRing k) c, ?_⟩
  change MvPolynomial.aeval ![a, 1] (algebraMap k (PlaneRing k) c) = c
  simp

/-- `ν(a, 1)` has height at least two: `0 ⊊ ν(V(w-1)) ⊊ 𝔪`. -/
theorem two_le_height_mPoint (a : k) : 2 ≤ (mPoint k a).height := by
  have hP : (bPoint k).asIdeal.IsPrime := (bPoint k).isPrime
  have hPo : (bPoint k).asIdeal < mPoint k a := by
    refine lt_of_le_of_ne (fun h hh => ?_) (fun heq => ?_)
    · rw [mem_bPoint_iff] at hh
      have := congrArg (Polynomial.eval a) hh
      rw [eval_planeToLine, Polynomial.eval_zero] at this
      exact this
    · have hz : mk k (MvPolynomial.X 0 ^ 2 - MvPolynomial.C (a ^ 2))
          (by rw [mem_pinchedAlg_iff]; simp) ∈ mPoint k a := by
        change MvPolynomial.aeval ![a, 1] (MvPolynomial.X 0 ^ 2 - MvPolynomial.C (a ^ 2)) = 0
        simp
      rw [← heq, mem_bPoint_iff] at hz
      have hx : planeToLine k (MvPolynomial.X 0 ^ 2 - MvPolynomial.C (a ^ 2)) =
          Polynomial.X ^ 2 - Polynomial.C (a ^ 2) := by
        simp [planeToLine]
      exact Polynomial.X_pow_sub_C_ne_zero (by norm_num) (a ^ 2) (hx ▸ hz)
  have hP0 : ⊥ < (bPoint k).asIdeal := by
    refine bot_lt_iff_ne_bot.mpr (fun h0 => wSubOne_ne_zero k ?_)
    have : wSubOne k ∈ (bPoint k).asIdeal := by
      rw [mem_bPoint_iff]
      change planeToLine k (MvPolynomial.X 1 - 1) = 0
      simp [planeToLine]
    rw [h0] at this
    exact this
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP0
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hPo
  rw [Ideal.height_bot, zero_add] at h1
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ (bPoint k).asIdeal.height + 1 := by gcongr
    _ ≤ _ := h2

theorem height_one_ne_mPoint (E : Ideal (PinchedRing k)) (hE : E.height = 1) (a : k) :
    E ≠ mPoint k a := by
  rintro rfl
  have := two_le_height_mPoint k a
  rw [hE] at this
  norm_num at this

/-- For a height-one prime `E`, some `c ∈ 𝔪_o ∩ 𝔪_{ν(4,1)}` avoids `E`. -/
theorem exists_good_element (E : Ideal (PinchedRing k)) [E.IsPrime] (hE : E.height = 1) :
    ∃ c ∈ mPoint k 2, c ∈ mPoint k 4 ∧ c ∉ E := by
  have hn (a : k) : ¬ mPoint k a ≤ E := fun hle =>
    height_one_ne_mPoint k E hE a ((mPoint_isMaximal k a).eq_of_le
      (Ideal.IsPrime.ne_top ‹_›) hle).symm
  obtain ⟨a, ha, haE⟩ := Set.not_subset.mp (hn 2)
  obtain ⟨b, hb, hbE⟩ := Set.not_subset.mp (hn 4)
  refine ⟨a * b, Ideal.mul_mem_right _ _ ha, Ideal.mul_mem_left _ _ hb, ?_⟩
  intro hab
  rcases Ideal.IsPrime.mem_or_mem ‹_› hab with h | h
  · exact haE h
  · exact hbE h

theorem mPoint_two_eq : mPoint k 2 = oIdeal k := rfl

theorem fStar_mem_oIdeal {c : PinchedRing k} (hc : c ∈ mPoint k 4) : fStar k c ∈ oIdeal k := by
  change MvPolynomial.aeval ![(2 : k), 1] (squaringMap k (val k c)) = 0
  have : MvPolynomial.aeval ![(2 : k), 1] (squaringMap k (val k c)) =
      MvPolynomial.aeval ![(4 : k), 1] (val k c) := by
    rw [squaringMap, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2
    funext i
    fin_cases i <;> norm_num
  rw [this]
  exact hc

/-! ### The three localization squares -/

/-- `Spec R_c → X`. -/
abbrev jX (c : PinchedRing k) : Spec (.of (Localization.Away c)) ⟶ pinchedPlane k :=
  Spec.map (CommRingCat.ofHom (algebraMap (PinchedRing k) (Localization.Away c)))

/-- `Spec S_c → 𝔸²`. -/
abbrev jP (c : PlaneRing k) : Spec (.of (Localization.Away c)) ⟶ plane k :=
  Spec.map (CommRingCat.ofHom (algebraMap (PlaneRing k) (Localization.Away c)))

/-- `f` over `D(c)`. -/
abbrev fC (c : PinchedRing k) :
    Spec (.of (Localization.Away (fStar k c))) ⟶ Spec (.of (Localization.Away c)) :=
  Spec.map (CommRingCat.ofHom (Localization.awayMap (fStar k) c))

/-- `f̃*` as a ring map. -/
def sqRing : PlaneRing k →+* PlaneRing k := (squaringMap k).toRingHom

/-- `f̃` over `D(c)`. -/
abbrev fP (c : PlaneRing k) :
    Spec (.of (Localization.Away (sqRing k c))) ⟶ Spec (.of (Localization.Away c)) :=
  Spec.map (CommRingCat.ofHom (Localization.awayMap (sqRing k) c))

/-- `ν` over `D(c)`. -/
abbrev uC (c : PinchedRing k) :
    Spec (.of (Localization.Away (algebraMap (PinchedRing k) (PlaneRing k) c))) ⟶
      Spec (.of (Localization.Away c)) :=
  Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap _ (PlaneRing k)) c))

theorem isPullback_awayMap {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (c : A) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ c)))))
      (Spec.map (CommRingCat.ofHom (Localization.awayMap φ c)))
      (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away c)))) := by
  apply isPullback_SpecMap_of_isPushout
  have : IsLocalization ((Submonoid.powers c).map φ) (Localization.Away (φ c)) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact CommRingCat.isPushout_of_isLocalization φ (Localization.awayMap φ c)
    (IsLocalization.map_comp _) (Submonoid.powers c)

theorem sq1 (c : PinchedRing k) :
    IsPullback (jX k (fStar k c)) (fC k c) (ambientMap k) (jX k c) :=
  isPullback_awayMap (fStar k) c

theorem sq3 (c : PlaneRing k) :
    IsPullback (jP k (sqRing k c)) (fP k c) (planeSquaring k) (jP k c) :=
  isPullback_awayMap (sqRing k) c

theorem sq2_comm (c : PinchedRing k) :
    uC k (fStar k c) ≫ fC k c =
      fP k (algebraMap (PinchedRing k) (PlaneRing k) c) ≫ uC k c := by
  unfold uC fC fP
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers c)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc,
    Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_comp]
  simp only [← RingHom.comp_assoc, IsLocalization.map_comp]
  change _ = ((Localization.awayMap (sqRing k) (algebraMap _ (PlaneRing k) c)).comp
      (Localization.awayMap (algebraMap (PinchedRing k) (PlaneRing k)) c)).comp
          (algebraMap (PinchedRing k) (Localization.Away c))
  simp only [Localization.awayMap, IsLocalization.Away.map]
  conv_rhs => rw [RingHom.comp_assoc, IsLocalization.map_comp, ← RingHom.comp_assoc,
    IsLocalization.map_comp]
  exact RingHom.ext fun r => rfl

theorem sq2 (c : PinchedRing k) (hc : c ∈ oIdeal k) (hfc : fStar k c ∈ oIdeal k) (h0 : c ≠ 0) :
    IsPullback (uC k (fStar k c)) (fP k (algebraMap (PinchedRing k) (PlaneRing k) c))
      (fC k c) (uC k c) := by
  have : IsIso (uC k c) := nu_away_isIso k c hc h0
  have : IsIso (uC k (fStar k c)) := nu_away_isIso k _ hfc
    (fun h => h0 (fStar_injective k (h.trans (map_zero _).symm)))
  exact IsPullback.of_horiz_isIso ⟨sq2_comm k c⟩

theorem nu_jP (c : PinchedRing k) :
    jP k (algebraMap (PinchedRing k) (PlaneRing k) c) ≫ nu k = uC k c ≫ jX k c :=
  (nu_isPullback_away k c).w

theorem mem_range_jX (c : PinchedRing k) (x : pinchedPlane k) (hx : c ∉ x.asIdeal) :
    ∃ y, jX k c y = x := by
  have : x ∈ Set.range (jX k c) := by
    change x ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (PinchedRing k) (Localization.Away c)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away c) c]
    exact hx
  exact this

theorem mem_range_jP (c : PlaneRing k) (x : plane k) (hx : c ∉ x.asIdeal) :
    ∃ y, jP k c y = x := by
  have : x ∈ Set.range (jP k c) := by
    change x ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (PlaneRing k) (Localization.Away c)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away c) c]
    exact hx
  exact this

theorem divisor_height (E : SchemeDivisorPoint (pinchedPlane k)) : E.1.asIdeal.height = 1 :=
  (idealHeight_eq_coheight (.of (PinchedRing k)) E.1).trans E.2

/-- **The fibre of `f` over a divisor is the fibre of `f̃` over a point above it.** -/
theorem fiber_isReduced_iff_plane (E : SchemeDivisorPoint (pinchedPlane k)) (E' : plane k)
    (hE' : nu k E' = E.1) :
    IsReduced ((ambientMap k).fiber E.1) ↔ IsReduced ((planeSquaring k).fiber E') := by
  have := E.1.isPrime
  obtain ⟨c, hc2, hc4, hcE⟩ := exists_good_element k E.1.asIdeal (divisor_height k E)
  have hfc := fStar_mem_oIdeal k hc4
  have h0 : c ≠ 0 := by rintro rfl; exact hcE E.1.asIdeal.zero_mem
  have hcE' : algebraMap (PinchedRing k) (PlaneRing k) c ∉ E'.asIdeal := by
    intro h; apply hcE; rw [← hE']; exact h
  obtain ⟨y, rfl⟩ := mem_range_jP k _ E' hcE'
  have hE : jX k c (uC k c y) = E.1 := by
    rw [← hE', ← Scheme.Hom.comp_apply, ← nu_jP, Scheme.Hom.comp_apply]
  have h1 := fiber_isReduced_iff_of_isPullback (sq1 k c) (uC k c y)
  have : IsIso (uC k c) := nu_away_isIso k c hc2 h0
  have h2 := fiber_isReduced_iff_of_isPullback (sq2 k c hc2 hfc h0) y
  have h3 := fiber_isReduced_iff_of_isPullback (sq3 k (algebraMap _ (PlaneRing k) c)) y
  rw [hE] at h1
  exact h1.symm.trans (h2.symm.trans h3)

/-- **The stalk map of `f` at a divisor is the stalk map of `f̃` at a point above it.** -/
theorem stalk_formallyEtale_iff_plane (D : SchemeDivisorPoint (pinchedPlane k)) (D' : plane k)
    (hD' : nu k D' = D.1) :
    ((ambientMap k).stalkMap D.1).hom.FormallyEtale ↔
      ((planeSquaring k).stalkMap D').hom.FormallyEtale := by
  let S := SquaringSource (fStar k)
  have : Module.Finite (PinchedRing k) S := fStar_finite k
  have : FaithfulSMul (PinchedRing k) S :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (fStar_injective k)
  let Q : Ideal S := D.1.asIdeal
  have : Q.IsPrime := D.1.isPrime
  have hEh : (Q.under (PinchedRing k)).height = 1 := by
    rw [height_under_eq_of_finite_of_finiteType k]
    exact divisor_height k D
  have : (Q.under (PinchedRing k)).IsPrime := Ideal.IsPrime.under _ _
  obtain ⟨c, hc2, hc4, hcE⟩ := exists_good_element k _ hEh
  have hfc := fStar_mem_oIdeal k hc4
  have h0 : c ≠ 0 := by rintro rfl; exact hcE (Ideal.zero_mem _)
  have hfcD : fStar k c ∉ D.1.asIdeal := hcE
  have hfcD' : sqRing k (algebraMap (PinchedRing k) (PlaneRing k) c) ∉ D'.asIdeal := by
    intro h; apply hfcD; rw [← hD']; exact h
  obtain ⟨y, rfl⟩ := mem_range_jP k _ D' hfcD'
  have : IsIso (uC k c) := nu_away_isIso k c hc2 h0
  have : IsIso (uC k (fStar k c)) := nu_away_isIso k _ hfc
    (fun h => h0 (fStar_injective k (h.trans (map_zero _).symm)))
  have e : jP k (sqRing k (algebraMap (PinchedRing k) (PlaneRing k) c)) ≫ nu k =
      uC k (fStar k c) ≫ jX k (fStar k c) := nu_jP k (fStar k c)
  have hD : jX k (fStar k c) (uC k (fStar k c) y) = D.1 := by
    rw [← hD', ← Scheme.Hom.comp_apply, e]
    rfl
  have hA := stalk_formallyEtale_iff_of_comm (sq1 k c).w (uC k (fStar k c) y)
  have hB := stalk_formallyEtale_iff_of_comm (sq2 k c hc2 hfc h0).w y
  have hC := stalk_formallyEtale_iff_of_comm (sq3 k (algebraMap _ (PlaneRing k) c)).w y
  rw [hD] at hA
  exact hA.symm.trans (hB.symm.trans hC)

/-! ### The unnormalized branch loci of `f` -/

/-- A point of `𝔸²` over a divisor of `X` is a divisor of `𝔸²`. -/
def planeDivisorOver (E : SchemeDivisorPoint (pinchedPlane k)) (E' : plane k)
    (hE' : nu k E' = E.1) : SchemeDivisorPoint (plane k) :=
  ⟨E', by
    let x : PrimeSpectrum (PlaneRing k) := E'
    rw [← idealHeight_eq_coheight]
    change x.asIdeal.height = 1
    rw [← height_under_eq_of_finite_of_finiteType k (R := PinchedRing k)]
    change (nu k E').asIdeal.height = 1
    rw [hE']
    exact divisor_height k E⟩

/-- `ν` of a divisor of `𝔸²` is a divisor of `X`. -/
def divisorBelow (D : SchemeDivisorPoint (plane k)) : SchemeDivisorPoint (pinchedPlane k) :=
  ⟨nu k D.1, by
    let x : PrimeSpectrum (PlaneRing k) := D.1
    have h : x.asIdeal.height = 1 :=
      (idealHeight_eq_coheight (.of (PlaneRing k)) x).trans D.2
    rw [← idealHeight_eq_coheight]
    change (x.asIdeal.under (PinchedRing k)).height = 1
    rw [height_under_eq_of_finite_of_finiteType k]
    exact h⟩

theorem eq_imageDivisor (E : SchemeDivisorPoint (pinchedPlane k)) (E' : plane k)
    (hE' : nu k E' = E.1) (i : Fin 2) (h : planeDivisorOver k E E' hE' = axisDivisor k i) :
    E = imageDivisor k i := by
  apply Subtype.ext
  rw [← hE']
  exact congrArg (fun D : SchemeDivisorPoint (plane k) => nu k D.1) h

/-- **`ex:pinched`, nonreduced-fibre convention.** The nonreduced-fibre branch divisors
of `f` are exactly `ν(V(z))` and `ν(V(w))`. -/
theorem ambient_nonreducedFibreBranch :
    nonreducedFibreBranch (ambientMap k) = {zDivisor k, wDivisor k} := by
  ext E
  constructor
  · intro hE
    obtain ⟨E', hE'⟩ := (nu k).surjective E.1
    have hmem : planeDivisorOver k E E' hE' ∈ schemeReducedFiberBranch (planeSquaring k) :=
      fun h => hE ((fiber_isReduced_iff_plane k E E' hE').mpr h)
    rw [planeSquaring_reducedFiberBranch] at hmem
    rcases hmem with h | h
    · exact Or.inl (eq_imageDivisor k E E' hE' 0 h)
    · exact Or.inr (eq_imageDivisor k E E' hE' 1 h)
  · have key (i : Fin 2) : imageDivisor k i ∈ nonreducedFibreBranch (ambientMap k) := by
      intro hred
      have h := (fiber_isReduced_iff_plane k (imageDivisor k i) (axisDivisor k i).1 rfl).mp hred
      have hmem : axisDivisor k i ∈ schemeReducedFiberBranch (planeSquaring k) := by
        rw [planeSquaring_reducedFiberBranch]
        fin_cases i <;> simp
      exact hmem h
    rintro (rfl | rfl)
    · exact key 0
    · exact key 1

/-- The structure morphism `𝔸² → Spec k`. -/
def planeStructure : plane k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (PlaneRing k)))

/-- **`ex:pinched`, non-étale convention.** The non-étale branch divisors of `f` are
exactly `ν(V(z))` and `ν(V(w))`. -/
theorem ambient_nonEtaleBranch :
    nonEtaleBranch (ambientMap k) = {zDivisor k, wDivisor k} := by
  ext E
  constructor
  · rintro ⟨D, hD, hDE⟩
    obtain ⟨D', hD'⟩ := (nu k).surjective D.1
    let P := planeDivisorOver k D D' hD'
    have hne : ¬ ((planeSquaring k).stalkMap P.1).hom.FormallyEtale :=
      fun h => hD ((stalk_formallyEtale_iff_plane k D D' hD').mpr h)
    have hram : 1 < schemeDivisorRamificationIdx (planeSquaring k) P := by
      have h1 := schemeDivisorRamificationIdx_pos (planeSquaring k) P
      have h2 : schemeDivisorRamificationIdx (planeSquaring k) P ≠ 1 := fun h =>
        hne ((ramificationIdx_eq_one_iff_formallyEtale_charZero k (planeStructure k)
          (planeSquaring k) P).mp h)
      omega
    let F : SchemeDivisorPoint (plane k) :=
      ⟨planeSquaring k P.1, coheight_apply_eq_one (planeSquaring k) P⟩
    have hF : F ∈ schemeReducedFiberBranch (planeSquaring k) :=
      (mem_schemeReducedFiberBranch_iff (planeSquaring k) F).mpr ⟨P, rfl, hram⟩
    rw [planeSquaring_reducedFiberBranch] at hF
    have hE : E.1 = nu k F.1 := by
      rw [← hDE, ← hD']
      change ambientMap k (nu k D') = nu k (planeSquaring k D')
      rw [← Scheme.Hom.comp_apply, ← planeSquaring_nu, Scheme.Hom.comp_apply]
    rcases hF with h | h
    · left; apply Subtype.ext; rw [hE, h]; rfl
    · right; apply Subtype.ext; rw [hE, h]; rfl
  · have key (i : Fin 2) : imageDivisor k i ∈ nonEtaleBranch (ambientMap k) := by
      have hmem : axisDivisor k i ∈ schemeReducedFiberBranch (planeSquaring k) := by
        rw [planeSquaring_reducedFiberBranch]
        fin_cases i <;> simp
      obtain ⟨Q, hQ, hram⟩ :=
        (mem_schemeReducedFiberBranch_iff (planeSquaring k) _).mp hmem
      have hne : ¬ ((planeSquaring k).stalkMap Q.1).hom.FormallyEtale := fun h => by
        have := (ramificationIdx_eq_one_iff_formallyEtale_charZero k (planeStructure k)
          (planeSquaring k) Q).mpr h
        omega
      refine ⟨divisorBelow k Q, fun h => hne ?_, ?_⟩
      · exact (stalk_formallyEtale_iff_plane k (divisorBelow k Q) Q.1 rfl).mp h
      · change ambientMap k (nu k Q.1) = nu k (axisDivisor k i).1
        rw [← Scheme.Hom.comp_apply, ← planeSquaring_nu, Scheme.Hom.comp_apply, hQ]
    rintro (rfl | rfl)
    · exact key 0
    · exact key 1

/-! ### PCF in all three conventions -/

theorem divisorPostcritical_of_fixed {X : Scheme.{u}} (f : X ⟶ X)
    (B : Set (SchemeDivisorPoint X)) (h : ∀ E ∈ B, f E.1 = E.1) :
    divisorPostcritical f B = Subtype.val '' B := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, ⟨E, hE, rfl⟩, rfl⟩ := hn
    exact ⟨E, hE, (Function.iterate_fixed (h E hE) n).symm⟩
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨0, x, hx, rfl⟩

theorem ambient_branch_fixed :
    ∀ E ∈ ({zDivisor k, wDivisor k} : Set (SchemeDivisorPoint (pinchedPlane k))),
      ambientMap k E.1 = E.1 := by
  rintro E (rfl | rfl)
  · exact ambientMap_zDivisor k
  · exact ambientMap_wDivisor k

/-- **`ex:pinched`: `f` is PCF for the nonreduced-fibre branch locus.** -/
theorem ambient_pcf_nonreducedFibre :
    (divisorPostcritical (ambientMap k) (nonreducedFibreBranch (ambientMap k))).Finite := by
  rw [ambient_nonreducedFibreBranch, divisorPostcritical_of_fixed _ _ (ambient_branch_fixed k)]
  exact ((Set.finite_singleton _).insert _).image _

/-- **`ex:pinched`: `f` is PCF for the non-étale branch locus.** -/
theorem ambient_pcf_nonEtale :
    (divisorPostcritical (ambientMap k) (nonEtaleBranch (ambientMap k))).Finite := by
  rw [ambient_nonEtaleBranch, divisorPostcritical_of_fixed _ _ (ambient_branch_fixed k)]
  exact ((Set.finite_singleton _).insert _).image _

/-- **`ex:pinched`: the three divisorial branch loci of `f` coincide.** -/
theorem ambient_three_branch_loci :
    normalizedMorphismBranchSupport (ambientMap k) =
        divisorSupport (nonreducedFibreBranch (ambientMap k)) ∧
      nonreducedFibreBranch (ambientMap k) = nonEtaleBranch (ambientMap k) := by
  rw [ambient_normalizedBranch, ambient_nonreducedFibreBranch, ambient_nonEtaleBranch]
  exact ⟨rfl, rfl⟩

end Pcf.Examples.CharZeroPaperPinched

#print axioms Pcf.Examples.CharZeroPaperPinched.fiber_isReduced_iff_of_isPullback
#print axioms Pcf.Examples.CharZeroPaperPinched.stalk_formallyEtale_iff_of_comm
#print axioms Pcf.Examples.CharZeroPaperPinched.fiber_isReduced_iff_plane
#print axioms Pcf.Examples.CharZeroPaperPinched.stalk_formallyEtale_iff_plane
#print axioms Pcf.Examples.CharZeroPaperPinched.ambient_nonreducedFibreBranch
#print axioms Pcf.Examples.CharZeroPaperPinched.ambient_nonEtaleBranch
#print axioms Pcf.Examples.CharZeroPaperPinched.ambient_pcf_nonreducedFibre
#print axioms Pcf.Examples.CharZeroPaperPinched.ambient_pcf_nonEtale
#print axioms Pcf.Examples.CharZeroPaperPinched.ambient_three_branch_loci
