/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperPinchedSquaring
public import Pcf.Examples.CharZeroPaperSquaring
public import Pcf.Bounding.PcfAllTheWayDownScheme

/-!
# Normalized branch locus and PCF of the pinched plane, `paper.tex`, `ex:pinched`

For the actual descended squaring map `f : X → X` of the pinched plane:

* `ambient_lift_eq`: the canonical lift of `f` to `Palomar.normalization X` is the
  squaring map `f̃` of `𝔸²`, transported along `normalizationIso`;
* `jacobian_eq`: the Jacobian determinant of `f̃` is `4zw`;
* `ambient_normalizedBranch`: the normalized branch support of `f` is
  `ν(V(z)) ∪ ν(V(w))`, the union of the two integral effective divisors
  `zDivisor`, `wDivisor` of `X`; both are invariant under `f`
  (`ambientMap_zDivisor`, `ambientMap_wDivisor`);
* `ambient_isNormalizedPCF`: `f` is PCF for the normalized branch locus, in
  the project's sense `IsNormalizedPCFOfFiniteType`;
* `divisor_ne_oPoint`, `exists_away_isIso`: every integral effective divisor of
  `X` has a basic-open neighbourhood over which `ν` is an isomorphism, so `f`
  agrees with `f̃` at the generic point of every divisor.

No branch, lift or PCF assertion is an input.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperPinched

open CategoryTheory AlgebraicGeometry Pcf.PaperCharZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

/-! ### Lifts conjugate to a map on an explicit normalization -/

section Conjugate

variable (R : CommRingCat.{u}) [IsDomain R] {N : Scheme.{u}} [IsIntegral N] [IsNormalScheme N]
  (p : N ⟶ Spec R) [IsFinite p] [IsDominant p]
  (e : N ≅ Palomar.normalization (Spec R))
  (he : e.hom ≫ Palomar.normalizationMap (Spec R) = p)

include he in
/-- If `N ≅ normalization(Spec R)` over `Spec R`, and `g` on `N` lifts `f` along
`p`, then the canonical normalized lift of `f` is `g` transported along `N ≅ Ñ`. -/
theorem lift_eq_conj (f : Spec R ⟶ Spec R) [IsFinite f] [IsDominant f]
    (g : N ⟶ N) [IsFinite g] [IsDominant g] (hg : g ≫ p = p ≫ f) :
    schemeGlobalNormalizationMorphism f = e.inv ≫ g ≫ e.hom := by
  have h1 := schemeGlobalNormalizationMorphism_eq_of_factor R (g ≫ p) (g ≫ e.hom)
    (by rw [Category.assoc, he])
  have h2 := schemeGlobalNormalizationMorphism_eq_of_factor R p e.hom he
  have key : ∀ (h : N ⟶ Spec R) [IsFinite h] [IsDominant h], h = p ≫ f →
      schemeGlobalNormalizationMorphism h =
        schemeGlobalNormalizationMorphism p ≫ schemeGlobalNormalizationMorphism f := by
    intro h _ _ hh
    subst hh
    exact (schemeGlobalNormalizationMorphism_comp_morphism p f).symm
  have h3 := (key (g ≫ p) hg).symm
  rw [h1, h2] at h3
  let : IsIso (Palomar.normalizationMap N) := normalScheme_normalizationMap_isIso N
  rw [Category.assoc] at h3
  have h4 := (cancel_epi (Palomar.normalizationMap N)).mp h3
  rw [← h4]
  simp

theorem branch_iso_empty {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    divisorSupport (schemeReducedFiberBranch g) = ∅ := by
  rw [reducedFiberBranch_empty_of_isIso]
  simp [divisorSupport]

/-- Branch support of a conjugate by an isomorphism of normal integral schemes. -/
theorem conj_branch_support {N M : Scheme.{u}} [IsIntegral N] [IsNormalScheme N]
    [IsLocallyNoetherian N] [IsIntegral M] [IsNormalScheme M] [IsLocallyNoetherian M]
    (e : N ≅ M) (g : N ⟶ N) [IsFinite g] [IsDominant g] :
    divisorSupport (schemeReducedFiberBranch (e.inv ≫ g ≫ e.hom)) =
      e.hom '' divisorSupport (schemeReducedFiberBranch g) := by
  rw [reducedFiberBranch_support_tower, reducedFiberBranch_support_tower,
    branch_iso_empty e.inv, branch_iso_empty e.hom]
  simp

/-- **Normalized PCF from an explicit normalization.** If `f` on `Spec R` lifts
along `N ≅ normalization(Spec R)` to `g`, whose branch divisors form a finite set
of `g`-fixed divisors, then `f` is PCF for the normalized branch locus. -/
theorem isNormalizedPCF_of_conj (k : Type u) [Field k] [CharZero k]
    (R : CommRingCat.{u}) [IsDomain R] [IsNoetherianRing R]
    (s : Spec R ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    {N : Scheme.{u}} [IsIntegral N] [IsNormalScheme N] [IsLocallyNoetherian N]
    (p : N ⟶ Spec R) [IsFinite p] [IsDominant p]
    (e : N ≅ Palomar.normalization (Spec R))
    (he : e.hom ≫ Palomar.normalizationMap (Spec R) = p)
    (f : Spec R ⟶ Spec R) [IsFinite f] [IsDominant f]
    (g : N ⟶ N) [IsFinite g] [IsDominant g] (hg : g ≫ p = p ≫ f)
    (S : Set (SchemeDivisorPoint N)) (hS : schemeReducedFiberBranch g = S)
    (hfin : S.Finite) (hfix : ∀ D ∈ S, g D.1 = D.1) :
    IsNormalizedPCFOfFiniteType k s f := by
  letI := schemeGlobalNormalizationMap_isFinite (Spec R) k s
  letI := charZero_stalk_of_field k s (genericPoint (Spec R))
  rw [isNormalizedPCFOfFiniteType_iff_lift]
  set D := divisorDynamicsOfFiniteDominantNormalCharZero (schemeGlobalNormalizationLift f)
  let L := schemeGlobalNormalizationLift f
  have hL : L = e.inv ≫ g ≫ e.hom := lift_eq_conj R p e he f g hg
  have hbranch : D.branch = schemeReducedFiberBranch L := by
    ext E
    rw [mem_schemeReducedFiberBranch_iff L E, DivisorDynamics.mem_branch_iff]
    constructor
    · rintro ⟨Q, hQE, hram⟩
      exact ⟨Q, congrArg Subtype.val hQE, hram⟩
    · rintro ⟨Q, hQE, hram⟩
      exact ⟨Q, Subtype.ext hQE, hram⟩
  have hsupp : divisorSupport (schemeReducedFiberBranch L) = e.hom '' divisorSupport S := by
    rw [hL, conj_branch_support, hS]
  have hfix' : ∀ E ∈ D.branch, D.step E = E := by
    intro E hE
    rw [hbranch] at hE
    have hE' : E.1 ∈ divisorSupport (schemeReducedFiberBranch L) :=
      (mem_divisorSupport_iff E _).mpr hE
    rw [hsupp] at hE'
    obtain ⟨x, hx, hxE⟩ := hE'
    have hxcodim : Order.coheight x = 1 := by
      have := coheight_apply_eq_of_finite_dominant_normal e.hom x
      rw [← this, hxE]
      exact E.2
    have hxS : (⟨x, hxcodim⟩ : SchemeDivisorPoint N) ∈ S :=
      (mem_divisorSupport_iff ⟨x, hxcodim⟩ S).mp hx
    have hxfix : g x = x := hfix _ hxS
    apply Subtype.ext
    change L E.1 = E.1
    rw [← hxE, hL]
    simp [hxfix]
  have hpc : D.postcriticalSet = D.branch := by
    apply le_antisymm
    · intro E hE
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hE
      obtain ⟨F, hF, rfl⟩ := hn
      have : D.step^[n] F = F := Function.iterate_fixed (hfix' F hF) n
      rw [this]
      exact hF
    · intro E hE
      exact Set.mem_iUnion.mpr ⟨0, E, hE, rfl⟩
  change D.postcriticalSet.Finite
  rw [hpc, hbranch]
  have hcodim : ∀ Q : SchemeDivisorPoint N, Order.coheight (e.hom Q.1) = 1 :=
    coheight_apply_eq_one e.hom
  have hset : schemeReducedFiberBranch L = schemeDivisorMap e.hom hcodim '' S := by
    rw [← divisorSupport_eq_iff, ← image_divisorSupport e.hom hcodim]
    exact hsupp
  rw [hset]
  exact hfin.image _

end Conjugate

/-! ### The lift of `f` and its branch locus -/

variable (k : Type u) [Field k] [CharZero k]

instance plane_isNormal' : IsNormalScheme (plane k) := plane_isNormal k

/-- The canonical normalized lift of `f` is `f̃ = (z,w) ↦ (z², w²)`, transported. -/
theorem ambient_lift_eq :
    schemeGlobalNormalizationMorphism (ambientMap k) =
      (normalizationIso k).inv ≫ planeSquaring k ≫ (normalizationIso k).hom :=
  lift_eq_conj (.of (PinchedRing k)) (nu k) (normalizationIso k) (normalizationIso_comm k)
    (ambientMap k) (planeSquaring k) (planeSquaring_nu k)

open MvPolynomial in
/-- `ex:pinched`: the Jacobian determinant of `f̃` is `4zw`. -/
theorem jacobian_eq :
    Matrix.det (fun i j : Fin 2 => pderiv j ((X i : PlaneRing k) ^ 2)) =
      4 * X 0 * X 1 := by
  rw [CharZeroPaperSquaring.polynomial_jacobian, Matrix.det_diagonal, Fin.prod_univ_two]
  ring

instance normalizationMap_isFinite : IsFinite (Palomar.normalizationMap (pinchedPlane k)) := by
  have : Palomar.normalizationMap (pinchedPlane k) = (normalizationIso k).inv ≫ nu k := by
    rw [← normalizationIso_comm, Iso.inv_hom_id_assoc]
  rw [this]
  infer_instance

instance pinchedPlane_noetherian : IsNoetherianRing (PinchedRing k) := inferInstance

/-- The branch support of the canonical lift is the transport of `V(z) ∪ V(w)`. -/
theorem lift_branch_support :
    divisorSupport (schemeReducedFiberBranch (schemeGlobalNormalizationMorphism (ambientMap k))) =
      (normalizationIso k).hom '' divisorSupport (schemeReducedFiberBranch (planeSquaring k)) := by
  rw [ambient_lift_eq, reducedFiberBranch_support_tower, reducedFiberBranch_support_tower,
    branch_iso_empty (normalizationIso k).inv, branch_iso_empty (normalizationIso k).hom]
  simp

/-- `V(z)` and `V(w)` in `𝔸²` and their images in `X`. -/
theorem planeSquaring_branch_support :
    divisorSupport (schemeReducedFiberBranch (planeSquaring k)) =
      closure {(axisDivisor k 0).1} ∪ closure {(axisDivisor k 1).1} := by
  rw [planeSquaring_reducedFiberBranch]
  simp [divisorSupport, Set.iUnion_or, Set.iUnion_union_distrib]

/-- The integral effective divisor `ν(V(X i))` of `X`. -/
def imageDivisor (i : Fin 2) : SchemeDivisorPoint (pinchedPlane k) :=
  ⟨nu k (axisDivisor k i).1, by
    let x : PrimeSpectrum (PlaneRing k) := (axisDivisor k i).1
    have h : x.asIdeal.height = 1 :=
      (idealHeight_eq_coheight (.of (PlaneRing k)) x).trans (axisDivisor k i).2
    rw [← idealHeight_eq_coheight]
    change (x.asIdeal.under (PinchedRing k)).height = 1
    rw [height_under_eq_of_finite_of_finiteType k]
    exact h⟩

/-- `ν(V(z))`. -/
abbrev zDivisor : SchemeDivisorPoint (pinchedPlane k) := imageDivisor k 0
/-- `ν(V(w))`. -/
abbrev wDivisor : SchemeDivisorPoint (pinchedPlane k) := imageDivisor k 1

theorem nu_closure (x : plane k) : nu k '' closure {x} = closure {nu k x} := by
  rw [← (nu k).isClosedMap.closure_image_eq_of_continuous (nu k).continuous, Set.image_singleton]

/-- **`ex:pinched`, normalized convention.** The normalized branch support of `f`
is `ν(V(z)) ∪ ν(V(w))`. -/
theorem ambient_normalizedBranch :
    normalizedMorphismBranchSupport (ambientMap k) =
      divisorSupport {zDivisor k, wDivisor k} := by
  unfold normalizedMorphismBranchSupport
  have hcomp : ⇑(Palomar.normalizationMap (pinchedPlane k)) ∘ ⇑(normalizationIso k).hom =
      ⇑(nu k) := by
    funext x
    rw [← normalizationIso_comm]
    rfl
  rw [lift_branch_support, ← Set.image_comp, hcomp,
    planeSquaring_branch_support, Set.image_union, nu_closure, nu_closure]
  simp only [divisorSupport, Set.biUnion_insert, Set.biUnion_singleton]
  rfl

/-- `f(ν(V(X i))) = ν(V(X i))`. -/
theorem ambientMap_imageDivisor (i : Fin 2) :
    ambientMap k (imageDivisor k i).1 = (imageDivisor k i).1 := by
  change ambientMap k (nu k (axisDivisor k i).1) = nu k (axisDivisor k i).1
  rw [← Scheme.Hom.comp_apply, ← planeSquaring_nu, Scheme.Hom.comp_apply, planeSquaring_axis]

theorem ambientMap_zDivisor : ambientMap k (zDivisor k).1 = (zDivisor k).1 :=
  ambientMap_imageDivisor k 0

theorem ambientMap_wDivisor : ambientMap k (wDivisor k).1 = (wDivisor k).1 :=
  ambientMap_imageDivisor k 1

theorem zDivisor_ne_wDivisor : zDivisor k ≠ wDivisor k := by
  intro h
  have h' := congrArg (fun E : SchemeDivisorPoint (pinchedPlane k) => E.1.asIdeal) h
  have hmem : mk k (MvPolynomial.X 0 ^ 2) (z_sq_mem k) ∈ (zDivisor k).1.asIdeal := by
    change MvPolynomial.X 0 ^ 2 ∈ Ideal.span {(MvPolynomial.X 0 : PlaneRing k)}
    exact Ideal.mem_span_singleton.mpr ⟨MvPolynomial.X 0, by ring⟩
  simp only at h'
  rw [h'] at hmem
  change MvPolynomial.X 0 ^ 2 ∈ Ideal.span {(MvPolynomial.X 1 : PlaneRing k)} at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  have := congrArg (MvPolynomial.aeval ![(1 : k), 0]) hc
  simp at this

/-! ### Normalized PCF -/

/-- The structure morphism `X → Spec k`. -/
def structureMap : pinchedPlane k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (PinchedRing k)))

instance structureMap_locallyOfFiniteType : LocallyOfFiniteType (structureMap k) := by
  unfold structureMap
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- **`ex:pinched`**: `f` is PCF for the normalized branch locus. -/
theorem ambient_isNormalizedPCF :
    IsNormalizedPCFOfFiniteType k (structureMap k) (ambientMap k) :=
  isNormalizedPCF_of_conj k (.of (PinchedRing k)) (structureMap k) (nu k) (normalizationIso k)
    (normalizationIso_comm k) (ambientMap k) (planeSquaring k) (planeSquaring_nu k)
    {axisDivisor k 0, axisDivisor k 1} (planeSquaring_reducedFiberBranch k)
    (Set.toFinite _) (by
      rintro D (rfl | rfl)
      · exact planeSquaring_axis k 0
      · exact planeSquaring_axis k 1)

/-! ### Agreement with `f̃` near every divisor -/

/-- `ν(V(w - 1))` lies strictly between `0` and `𝔪_o`, so `o` has height at least two
and is not a divisor. -/
theorem divisor_ne_oPoint (E : SchemeDivisorPoint (pinchedPlane k)) : E.1 ≠ oPoint k := by
  intro hE
  have hheight : (oIdeal k).height = 1 := by
    have := (idealHeight_eq_coheight (.of (PinchedRing k)) E.1).trans E.2
    rw [hE] at this
    exact this
  -- the prime `P = {h : h(z, 1) = 0}` sits strictly between `0` and `𝔪_o`
  let P : Ideal (PinchedRing k) := RingHom.ker
    ((MvPolynomial.aeval ![MvPolynomial.X 0, (1 : PlaneRing k)]).toRingHom.comp
      (algebraMap (PinchedRing k) (PlaneRing k)))
  have hP : P.IsPrime := RingHom.ker_isPrime _
  have hPo : P < oIdeal k := by
    refine lt_of_le_of_ne (fun h hh => ?_) (fun heq => ?_)
    · rw [mem_oIdeal_iff]
      have := congrArg (MvPolynomial.aeval ![(2 : k), 0]) hh
      change MvPolynomial.aeval ![(2 : k), 0] (MvPolynomial.aeval
        ![MvPolynomial.X 0, (1 : PlaneRing k)] (val k h)) = MvPolynomial.aeval ![(2 : k), 0] 0
        at this
      rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, map_zero] at this
      have hv : (fun i => MvPolynomial.aeval ![(2 : k), 0]
          (![MvPolynomial.X 0, (1 : PlaneRing k)] i)) = ![2, 1] := by
        funext i; fin_cases i <;> simp
      rw [hv] at this
      exact this
    · have hz : zSqSubFour k ∈ P := heq ▸ zSqSubFour_mem_oIdeal k
      change MvPolynomial.aeval ![MvPolynomial.X 0, (1 : PlaneRing k)]
        ((MvPolynomial.X 0 : PlaneRing k) ^ 2 - 4) = 0 at hz
      simp only [map_sub, map_pow, MvPolynomial.aeval_X, map_ofNat, Matrix.cons_val_zero] at hz
      have := congrArg (MvPolynomial.eval ![(0 : k), 0]) hz
      simp at this
  have hP0 : ⊥ < P := by
    refine bot_lt_iff_ne_bot.mpr (fun h0 => wSubOne_ne_zero k ?_)
    have : wSubOne k ∈ P := by
      change MvPolynomial.aeval ![MvPolynomial.X 0, (1 : PlaneRing k)]
        ((MvPolynomial.X 1 : PlaneRing k) - 1) = 0
      simp
    rw [h0] at this
    exact this
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP0
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hPo
  rw [Ideal.height_bot, zero_add] at h1
  rw [hheight] at h2
  have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left h1 1).trans h2
  norm_num at this

/-- `ex:pinched`: every integral effective divisor `E` of `X` lies in a basic open
`D(c)`, `c ∈ 𝔪_o`, over which `ν` is an isomorphism (`nu_isPullback_away`); so at the
generic point of every divisor `f` agrees with the squaring map. -/
theorem exists_away_isIso (E : SchemeDivisorPoint (pinchedPlane k)) :
    ∃ c ∈ oIdeal k, c ∉ E.1.asIdeal ∧
      IsIso (Spec.map (CommRingCat.ofHom
        (Localization.awayMap (algebraMap (PinchedRing k) (PlaneRing k)) c))) := by
  have := E.1.isPrime
  obtain ⟨c, hc, hcE⟩ := exists_mem_oIdeal_not_mem k E.1.asIdeal
    (fun h => divisor_ne_oPoint k E (PrimeSpectrum.ext h))
  refine ⟨c, hc, hcE, nu_away_isIso k c hc ?_⟩
  rintro rfl
  exact hcE E.1.asIdeal.zero_mem

end Pcf.Examples.CharZeroPaperPinched

#print axioms Pcf.Examples.CharZeroPaperPinched.lift_eq_conj
#print axioms Pcf.Examples.CharZeroPaperPinched.isNormalizedPCF_of_conj
#print axioms Pcf.Examples.CharZeroPaperPinched.ambient_lift_eq
#print axioms Pcf.Examples.CharZeroPaperPinched.jacobian_eq
#print axioms Pcf.Examples.CharZeroPaperPinched.ambient_normalizedBranch
#print axioms Pcf.Examples.CharZeroPaperPinched.ambientMap_zDivisor
#print axioms Pcf.Examples.CharZeroPaperPinched.ambientMap_wDivisor
#print axioms Pcf.Examples.CharZeroPaperPinched.zDivisor_ne_wDivisor
#print axioms Pcf.Examples.CharZeroPaperPinched.ambient_isNormalizedPCF
#print axioms Pcf.Examples.CharZeroPaperPinched.divisor_ne_oPoint
#print axioms Pcf.Examples.CharZeroPaperPinched.exists_away_isIso
