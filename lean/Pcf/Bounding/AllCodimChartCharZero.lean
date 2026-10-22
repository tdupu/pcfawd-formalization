/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimChartProofAffine
public import Pcf.Bounding.TameChartRestrictionDVR
public import Pcf.Stacks.Abhyankar.TameRamification

/-!
# The chart property in characteristic zero

The characteristic-zero form of `AllCodimChartProperty`, for `latex/paper-p.tex`,
proof of Theorem `thm:allcodim-normal` with `p = 0`. The statement drops the
prime-to-`p` monodromy hypothesis. The proof is that of `allCodimChartProperty`
with its two monodromy inputs replaced: generic étaleness comes from separability
of the finite function-field extension (characteristic-zero fields are perfect),
and tameness of the local chart comes from every positive integer being a unit
(`Stacks.isTamelyRamifiedInCodimensionOneAlong_of_isUnit_natCast`).
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The chart property over a base field of characteristic zero: as
`AllCodimChartProperty`, without a monodromy hypothesis. -/
def AllCodimChartPropertyCharZero (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ {Xs Y : Scheme.{u}} [IsIntegral Xs] [IsIntegral Y]
    [IsNormalScheme Xs] [IsNormalScheme Y]
    [IsLocallyNoetherian Xs] [IsLocallyNoetherian Y]
    (_ : Y ⟶ Spec (.of k)) (F : Xs ⟶ Y) [IsFinite F] [IsDominant F]
    (d' : SchemeDivisorPoint Xs) (E₀ : Xs) (hdE : d'.1 ⤳ E₀)
    (_ : Order.coheight E₀ = 2)
    (_ : (stalkGenerizationPrime Y (hdE.map F.continuous)).IsPrincipal)
    (_ : IsDiscreteValuationRing (closureStalk Y (hdE.map F.continuous)))
    (_ : ∀ w : SchemeDivisorPoint Xs, F w.1 ⤳ F E₀ → F w.1 ≠ F d'.1 →
      (F.stalkMap w.1).hom.FormallyEtale),
    IsDiscreteValuationRing (closureStalk Xs hdE) ∧
      (letI := (stalkGenerizationQuotientMap F hdE).toAlgebra
       (maximalIdeal (closureStalk Xs hdE)).ramificationIdx
         (closureStalk Y (hdE.map F.continuous)) = 1)

set_option backward.isDefEq.respectTransparency false in
/-- The chart property in characteristic zero. -/
theorem allCodimChartPropertyCharZero (k : Type u) [Field k] [CharZero k] :
    AllCodimChartPropertyCharZero k := by
  intro Xs Y _ _ _ _ _ _ sY F _ _ d' E₀ hdE hcoh hprin hdvr hunram
  set E : Y := F E₀ with hEdef
  set d : Y := F d'.1 with hddef
  have hdE' : d ⤳ E := hdE.map F.continuous
  obtain ⟨W, hW, hEW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show E ∈ (⊤ : Y.Opens) from trivial)
  let U : Y.affineOpens := ⟨W, hW⟩
  haveI : Nonempty (U : Y.Opens) := ⟨⟨E, hEW⟩⟩
  have hdW : d ∈ W := hdE'.mem_open W.isOpen hEW
  let V := finitePreimageAffine F U
  have hE₀V : E₀ ∈ (V : Xs.Opens) := hEW
  have hd'V : d'.1 ∈ (V : Xs.Opens) := hdE.mem_open (V : Xs.Opens).isOpen hE₀V
  let R := Γ(Y, W)
  let S := Γ(Xs, (V : Xs.Opens))
  letI : Algebra R S := (F.app W).hom.toAlgebra
  let q : Ideal R := (hW.primeIdealOf ⟨E, hEW⟩).asIdeal
  let Pd : Ideal R := (hW.primeIdealOf ⟨d, hdW⟩).asIdeal
  let 𝔐 : Ideal S := (V.2.primeIdealOf ⟨E₀, hE₀V⟩).asIdeal
  let 𝔓 : Ideal S := (V.2.primeIdealOf ⟨d'.1, hd'V⟩).asIdeal
  -- incidences
  have hPdq : Pd ≤ q := affineOpen_primeIdealOf_le_of_specializes hW hdE' hEW
  have h𝔓𝔐 : 𝔓 ≤ 𝔐 := affineOpen_primeIdealOf_le_of_specializes V.2 hdE hE₀V
  have hVW : (V : Xs.Opens) ≤ F ⁻¹ᵁ W := le_rfl
  have happ : (F.app W).hom = (F.appLE W (V : Xs.Opens) hVW).hom := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  have h𝔐q : 𝔐.comap (algebraMap R S) = q := by
    change 𝔐.comap (F.app W).hom = q
    rw [happ]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE W hW (V : Xs.Opens) V.2 hVW hE₀V)
  have h𝔓Pd : 𝔓.comap (algebraMap R S) = Pd := by
    change 𝔓.comap (F.app W).hom = Pd
    rw [happ]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE W hW (V : Xs.Opens) V.2 hVW hd'V)
  -- the stalk at `E` as a localization
  let Rq := Localization.AtPrime q
  letI : Algebra R (Y.presheaf.stalk E) := Y.presheaf.algebra_section_stalk ⟨E, hEW⟩
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk E) q := hW.isLocalization_stalk ⟨E, hEW⟩
  let eR : Y.presheaf.stalk E ≃ₐ[R] Rq := IsLocalization.algEquiv q.primeCompl _ _
  have h𝔭d : stalkGenerizationPrime Y hdE' = Pd.map (algebraMap R (Y.presheaf.stalk E)) :=
    affineOpen_stalkGenerizationPrime_eq_map hW hdE' hEW
  obtain ⟨g, hg⟩ := hprin
  set a : Rq := eR g with ha_def
  have hPda : Pd.map (algebraMap R Rq) = Ideal.span {a} := by
    have hcomp : (eR.toRingHom).comp (algebraMap R (Y.presheaf.stalk E)) = algebraMap R Rq :=
      eR.toAlgHom.comp_algebraMap
    rw [← hcomp, ← Ideal.map_map, ← h𝔭d, hg]
    refine (Ideal.map_span _ {g}).trans ?_
    rw [Set.image_singleton]
    rfl
  -- the base divisor `R_q/(a)` is the closure stalk of `d` at `E`
  let 𝔭E := stalkGenerizationPrime Y hdE'
  have h𝔭E : 𝔭E = Pd.map (algebraMap R (Y.presheaf.stalk E)) := h𝔭d
  have hPdle : Pd ≤ 𝔭E.comap (algebraMap R (Y.presheaf.stalk E)) := by
    rw [h𝔭E]
    exact Ideal.le_comap_map
  letI : Algebra (R ⧸ Pd) (closureStalk Y hdE') :=
    Ideal.Quotient.algebraQuotientOfLEComap hPdle
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ Pd) q.primeCompl)
      (closureStalk Y hdE') :=
    IsLocalization.of_surjective q.primeCompl (Y.presheaf.stalk E) (Ideal.Quotient.mk Pd)
      Ideal.Quotient.mk_surjective (Ideal.Quotient.mk 𝔭E) Ideal.Quotient.mk_surjective
      (by ext; rfl) (by rw [Ideal.mk_ker, Ideal.mk_ker, h𝔭E])
  letI : Algebra (R ⧸ Pd) (Rq ⧸ Ideal.span {a}) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp hPda.le)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ Pd) q.primeCompl)
      (Rq ⧸ Ideal.span {a}) := targetQuotient_isLocalization q Pd a hPda
  let eA : (Rq ⧸ Ideal.span {a}) ≃ₐ[R ⧸ Pd] closureStalk Y hdE' :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (R ⧸ Pd) q.primeCompl) _ _
  haveI : IsDomain (Rq ⧸ Ideal.span {a}) := eA.toRingEquiv.toMulEquiv.isDomain _
  haveI hdvrA : IsDiscreteValuationRing (Rq ⧸ Ideal.span {a}) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eA.symm
  have regular_divisor : IsRegularLocalRing (Rq ⧸ Ideal.span {a}) := inferInstance
  have dim_divisor : ringKrullDim (Rq ⧸ Ideal.span {a}) = 1 :=
    IsDiscreteValuationRing.ringKrullDim_eq_one _
  -- the base `R_q`
  haveI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  have hcohE : Order.coheight E = 2 := by
    rw [hEdef, coheight_apply_eq_of_finite_dominant_normal F E₀, hcoh]
  have hcohd : Order.coheight d = 1 := by
    rw [hddef, coheight_apply_eq_of_finite_dominant_normal F d'.1, d'.2]
  have dim_base : ringKrullDim Rq = 2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q Rq]
    rw [affineOpen_primeIdealOf_height hW E hEW, hcohE]
    rfl
  have ha_max : a ∈ maximalIdeal Rq := by
    have : a ∈ Pd.map (algebraMap R Rq) := by rw [hPda]; exact Ideal.mem_span_singleton_self a
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hPdq this
  have ha_ne : a ≠ 0 := by
    intro h0
    have hPd0 : Pd.map (algebraMap R Rq) = ⊥ := by rw [hPda, h0, Ideal.span_singleton_eq_bot]
    have hPdbot : Pd = ⊥ := by
      have := congrArg (Ideal.under R) hPd0
      rw [IsLocalization.under_map_of_isPrime_disjoint q.primeCompl Rq inferInstance
        (by
          rw [Set.disjoint_left]
          intro x hx hxP
          exact hx (hPdq hxP))] at this
      rw [this]
      exact Ideal.comap_bot_of_injective _ (IsLocalization.injective Rq
        q.primeCompl_le_nonZeroDivisors)
    have h1 := affineOpen_primeIdealOf_height hW d hdW
    change Pd.height = _ at h1
    rw [hPdbot, hcohd, Ideal.height_bot] at h1
    exact zero_ne_one h1
  have regular_base : IsRegularLocalRing Rq :=
    isRegularLocalRing_of_quotient_nonZeroDivisor a ha_max (mem_nonZeroDivisors_of_ne_zero ha_ne)
  -- the cover side
  let Sq := Localization (Algebra.algebraMapSubmonoid S q.primeCompl)
  have hdisj : ∀ P : Ideal S, P.comap (algebraMap R S) ≤ q →
      Disjoint (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (P : Set S) := by
    intro P hP
    rw [Set.disjoint_left]
    rintro x ⟨r, hr, rfl⟩ hx
    exact hr (hP hx)
  have h𝔓disj := hdisj 𝔓 (h𝔓Pd.le.trans hPdq)
  have h𝔐disj := hdisj 𝔐 h𝔐q.le
  let pS : Ideal Sq := 𝔓.map (algebraMap S Sq)
  haveI : pS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S q.primeCompl) Sq 𝔓 inferInstance h𝔓disj
  have height_cover_divisor : pS.height = 1 := by
    rw [IsLocalization.height_map_of_disjoint (Algebra.algebraMapSubmonoid S q.primeCompl) 𝔓
      h𝔓disj, affineOpen_primeIdealOf_height V.2 d'.1 hd'V, d'.2]
  have hmap_le : ∀ (J : Ideal R) (K : Ideal S), J.map (algebraMap R S) ≤ K →
      (J.map (algebraMap R Rq)).map (algebraMap Rq Sq) ≤ K.map (algebraMap S Sq) := by
    intro J K hJK
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R S Sq,
      ← Ideal.map_map]
    exact Ideal.map_mono hJK
  have hPd𝔓 : Pd.map (algebraMap R S) ≤ 𝔓 := by
    rw [Ideal.map_le_iff_le_comap, h𝔓Pd]
  have equation_mem : algebraMap Rq Sq a ∈ pS := by
    apply hmap_le Pd 𝔓 hPd𝔓
    apply Ideal.mem_map_of_mem
    rw [hPda]
    exact Ideal.mem_span_singleton_self a
  -- étaleness of the chart at primes of `S_q`
  have hGL : ∀ (w : Ideal Sq) [w.IsPrime] (x : Xs) (hx : x ∈ (V : Xs.Opens)),
      (V.2.primeIdealOf ⟨x, hx⟩).asIdeal = w.comap (algebraMap S Sq) →
      (F.stalkMap x).hom.FormallyEtale → Algebra.IsEtaleAt Rq w := by
    intro w _ x hx hxw het
    have h := (formallyEtale_stalkMap_iff_localRingHom F W hW (V : Xs.Opens) V.2 hVW hx).mp
      het
    apply isEtaleAt_of_formallyEtale_localRingHom q w
    refine formallyEtale_localRingHom_congr happ.symm hxw ?_ _ _ h
    have hc := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE W hW (V : Xs.Opens) V.2 hVW hx)
    rw [← hc]
    change Ideal.comap (F.appLE W (V : Xs.Opens) hVW).hom (V.2.primeIdealOf ⟨x, hx⟩).asIdeal = _
    rw [hxw, ← happ]
    rfl
  have hpoint : ∀ (w : Ideal Sq) [w.IsPrime], ∃ (x : Xs) (hx : x ∈ (V : Xs.Opens)),
      (V.2.primeIdealOf ⟨x, hx⟩).asIdeal = w.comap (algebraMap S Sq) := by
    intro w _
    obtain ⟨x, hx, hxP⟩ := affineOpen_exists_point_of_prime V.2
      ⟨w.comap (algebraMap S Sq), Ideal.comap_isPrime _ _⟩
    exact ⟨x, hx, congrArg PrimeSpectrum.asIdeal hxP⟩
  have hgen : (F.stalkMap (genericPoint Xs)).hom.FormallyEtale := by
    have hgp := map_genericPoint_eq_of_isDominant F
    let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
    have hfield : IsField (Y.presheaf.stalk (F (genericPoint Xs))) :=
      e.toMulEquiv.isField (Field.toIsField _)
    letI : Field (Y.presheaf.stalk (F (genericPoint Xs))) := hfield.toField
    letI := (F.stalkMap (genericPoint Xs)).hom.toAlgebra
    haveI : Algebra.QuasiFinite (Y.presheaf.stalk (F (genericPoint Xs)))
        (Xs.presheaf.stalk (genericPoint Xs)) := F.quasiFiniteAt (genericPoint Xs)
    haveI : FiniteDimensional (Y.presheaf.stalk (F (genericPoint Xs)))
        (Xs.presheaf.stalk (genericPoint Xs)) :=
      Algebra.QuasiFinite.iff_of_isArtinianRing.mp inferInstance
    haveI : CharZero (Y.presheaf.stalk (F (genericPoint Xs))) := by
      let φ : k →+* Y.presheaf.stalk (F (genericPoint Xs)) :=
        (Y.presheaf.germ ⊤ (F (genericPoint Xs)) trivial).hom.comp
          ((sY.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
      exact (RingHom.charZero_iff φ.injective).mp inferInstance
    haveI : Algebra.IsSeparable (Y.presheaf.stalk (F (genericPoint Xs)))
        (Xs.presheaf.stalk (genericPoint Xs)) :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    rw [RingHom.FormallyEtale]
    exact Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Nonempty (V : Xs.Opens) := ⟨⟨E₀, hE₀V⟩⟩
  haveI : Module.Finite R S := moduleFinite_finitePreimageAffine F U
  haveI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine F U
  haveI : IsDomain Sq := IsLocalization.isDomain_localization
    (map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective R S)
      q.primeCompl_le_nonZeroDivisors)
  have hSqinj : Function.Injective (algebraMap S Sq) :=
    IsLocalization.injective (M := Algebra.algebraMapSubmonoid S q.primeCompl) Sq
      (map_le_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective R S) q.primeCompl_le_nonZeroDivisors)
  have hcomapq : ∀ (w : Ideal Sq) [w.IsPrime],
      (w.comap (algebraMap S Sq)).comap (algebraMap R S) ≤ q := by
    intro w hw r hr
    by_contra hrq
    have hunit : IsUnit (algebraMap S Sq (algebraMap R S r)) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid S q.primeCompl) Sq
        ⟨algebraMap R S r, Submonoid.mem_map_of_mem _ hrq⟩
    exact hw.ne_top (Ideal.eq_top_of_isUnit_mem _ hr hunit)
  have hη : genericPoint Xs ∈ (V : Xs.Opens) := by
    change F (genericPoint Xs) ∈ W
    rw [map_genericPoint_eq_of_isDominant F]
    exact ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr
      (by simpa using (⟨⟨E, hEW⟩⟩ : Nonempty W))
  have generic_etale : ∀ w : PrimeSpectrum Sq, w.asIdeal.height = 0 →
      Algebra.IsEtaleAt Rq w.asIdeal := by
    intro w hw0
    have hwbot : w.asIdeal = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hw0
    obtain ⟨x, hx, hxP⟩ := hpoint w.asIdeal
    have hxη : x = genericPoint Xs := by
      apply affineOpen_primeIdealOf_injective V.2 hx hη
      apply PrimeSpectrum.ext
      rw [hxP, hwbot, Ideal.comap_bot_of_injective _ hSqinj,
        affineOpen_primeIdealOf_genericPoint V.2 hη]
    subst hxη
    exact hGL w.asIdeal _ hx hxP hgen
  have unramified_codim_one : ∀ w : PrimeSpectrum Sq, w.asIdeal.height = 1 →
      algebraMap Rq Sq a ∉ w.asIdeal → Algebra.IsUnramifiedAt Rq w.asIdeal := by
    intro w hw1 haw
    obtain ⟨x, hx, hxP⟩ := hpoint w.asIdeal
    have hwdisj := hdisj _ (hcomapq w.asIdeal)
    have hcohx : Order.coheight x = 1 := by
      rw [← affineOpen_primeIdealOf_height V.2 x hx, hxP, ← hw1]
      conv_rhs => rw [← IsLocalization.map_under (Algebra.algebraMapSubmonoid S q.primeCompl)
        Sq w.asIdeal]
      exact (IsLocalization.height_map_of_disjoint _ _ hwdisj).symm
    let w' : SchemeDivisorPoint Xs := ⟨x, hcohx⟩
    have hFxW : F x ∈ W := hx
    have hFx : (hW.primeIdealOf ⟨F x, hFxW⟩).asIdeal =
        (w.asIdeal.comap (algebraMap S Sq)).comap (algebraMap R S) := by
      have hc := congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE W hW (V : Xs.Opens) V.2 hVW hx)
      rw [← hc]
      change Ideal.comap (F.appLE W (V : Xs.Opens) hVW).hom (V.2.primeIdealOf ⟨x, hx⟩).asIdeal = _
      rw [hxP, ← happ]
      rfl
    have hFxE : F w'.1 ⤳ E := by
      have h := affineOpen_specializes_fromSpec_of_le hW (hW.primeIdealOf ⟨F x, hFxW⟩) E hEW
        (by rw [hFx]; exact hcomapq w.asIdeal)
      rwa [hW.fromSpec_primeIdealOf] at h
    have hFxd : F w'.1 ≠ d := by
      intro hxd
      have hPdw : Pd ≤ (w.asIdeal.comap (algebraMap S Sq)).comap (algebraMap R S) := by
        rw [← hFx]
        have : (⟨F x, hFxW⟩ : W) = ⟨d, hdW⟩ := Subtype.ext hxd
        rw [this]
      have hmem : algebraMap Rq Sq a ∈
          (w.asIdeal.comap (algebraMap S Sq)).map (algebraMap S Sq) := by
        apply hmap_le Pd _ (Ideal.map_le_iff_le_comap.mpr hPdw)
        apply Ideal.mem_map_of_mem
        rw [hPda]
        exact Ideal.mem_span_singleton_self a
      exact haw (Ideal.map_comap_le hmem)
    haveI := hGL w.asIdeal x hx hxP (hunram w' hFxE hFxd)
    infer_instance
  haveI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  haveI : IsIntegrallyClosed S := IsNormalScheme.component_integrallyClosed V
  -- every positive integer is a unit in `R_q`, which contains `k`
  have hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : Rq) := by
    intro n hn
    let φ : k →+* Rq := (algebraMap R Rq).comp
      ((sY.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    have h : IsUnit (φ (n : k)) := (Ne.isUnit (Nat.cast_ne_zero.mpr hn)).map φ
    simpa only [map_natCast] using h
  have hchart : TameLocalBoundingChart Rq Sq a pS :=
    TameLocalBoundingChart.ofFiniteNormalLocalization q a pS
      regular_base dim_base regular_divisor dim_divisor generic_etale unramified_codim_one
      height_cover_divisor equation_mem
      (Stacks.isTamelyRamifiedInCodimensionOneAlong_of_isUnit_natCast Rq Sq hunit a)
  -- the point `E₀` on the chart divisor
  let 𝔐S : Ideal Sq := 𝔐.map (algebraMap S Sq)
  haveI : 𝔐S.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S q.primeCompl) Sq 𝔐 inferInstance h𝔐disj
  have hp𝔐 : pS ≤ 𝔐S := Ideal.map_mono h𝔓𝔐
  let ξ : Ideal (Sq ⧸ pS) := 𝔐S.map (Ideal.Quotient.mk pS)
  haveI hξprime : ξ.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hp𝔐)
  letI : Algebra (Rq ⧸ Ideal.span {a}) (Sq ⧸ pS) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      hchart.toTameBoundingChart.toBoundingChart.span_le_comap
  have hξmax : ξ.IsMaximal := by
    haveI : Module.Finite Rq Sq := hchart.finite
    have hint : (algebraMap (Rq ⧸ Ideal.span {a}) (Sq ⧸ pS)).IsIntegral := by
      apply RingHom.IsIntegral.tower_top (Ideal.Quotient.mk (Ideal.span {a}))
      have hcomp : (algebraMap (Rq ⧸ Ideal.span {a}) (Sq ⧸ pS)).comp
          (Ideal.Quotient.mk (Ideal.span {a})) =
          (Ideal.Quotient.mk pS).comp (algebraMap Rq Sq) := by
        ext
        rfl
      rw [hcomp]
      exact RingHom.IsIntegral.trans _ _ (algebraMap_isIntegral_iff.mpr inferInstance)
        (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hint
    have hle : maximalIdeal (Rq ⧸ Ideal.span {a}) ≤
        ξ.comap (algebraMap (Rq ⧸ Ideal.span {a}) (Sq ⧸ pS)) := by
      intro y hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hx : x ∈ maximalIdeal Rq := by
        by_contra hx
        exact hy ((IsLocalRing.notMem_maximalIdeal.mp hx).map _)
      change Ideal.Quotient.mk pS (algebraMap Rq Sq x) ∈ ξ
      apply Ideal.mem_map_of_mem
      rw [← Localization.AtPrime.map_eq_maximalIdeal] at hx
      exact hmap_le q 𝔐 (by rw [Ideal.map_le_iff_le_comap, h𝔐q])
        (Ideal.mem_map_of_mem (algebraMap Rq Sq) hx)
    have heq := (IsLocalRing.maximalIdeal.isMaximal (Rq ⧸ Ideal.span {a})).eq_of_le
      (Ideal.comap_isPrime _ ξ).ne_top hle
    rw [← heq]
    infer_instance
  have het : Algebra.IsEtaleAt (Rq ⧸ Ideal.span {a}) ξ :=
    hchart.isEtaleAt_restriction Stacks.existsPrimeOverBoth ⟨ξ, hξprime⟩
  obtain ⟨hdvrξ, -⟩ := hchart.restriction_dvr_ramificationIdx_eq_one ξ
  -- the closure stalk of `d'` at `E₀` as a localization of `S/𝔓`
  letI : Algebra S (Xs.presheaf.stalk E₀) := Xs.presheaf.algebra_section_stalk ⟨E₀, hE₀V⟩
  haveI : IsLocalization.AtPrime (Xs.presheaf.stalk E₀) 𝔐 := V.2.isLocalization_stalk ⟨E₀, hE₀V⟩
  have h𝔭E₀ : stalkGenerizationPrime Xs hdE = 𝔓.map (algebraMap S (Xs.presheaf.stalk E₀)) :=
    affineOpen_stalkGenerizationPrime_eq_map V.2 hdE hE₀V
  have h𝔓le : 𝔓 ≤ (stalkGenerizationPrime Xs hdE).comap (algebraMap S (Xs.presheaf.stalk E₀)) := by
    rw [h𝔭E₀]
    exact Ideal.le_comap_map
  letI : Algebra (S ⧸ 𝔓) (closureStalk Xs hdE) := Ideal.Quotient.algebraQuotientOfLEComap h𝔓le
  haveI : (𝔐.map (Ideal.Quotient.mk 𝔓)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact h𝔓𝔐)
  have hiff : ∀ x : S, Ideal.Quotient.mk 𝔓 x ∈ 𝔐.map (Ideal.Quotient.mk 𝔓) ↔ x ∈ 𝔐 := by
    intro x
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr h𝔓𝔐]
  have hsub : 𝔐.primeCompl.map (Ideal.Quotient.mk 𝔓) =
      (𝔐.map (Ideal.Quotient.mk 𝔓)).primeCompl := by
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    rw [hiff]
    constructor
    · rintro ⟨z, hz, hzx⟩ hx
      exact hz ((hiff z).mp (hzx ▸ (hiff x).mpr hx))
    · intro hx
      exact ⟨x, hx, rfl⟩
  haveI : IsLocalization (𝔐.map (Ideal.Quotient.mk 𝔓)).primeCompl (closureStalk Xs hdE) := by
    rw [← hsub]
    exact IsLocalization.of_surjective 𝔐.primeCompl (Xs.presheaf.stalk E₀) (Ideal.Quotient.mk 𝔓)
      Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (stalkGenerizationPrime Xs hdE))
      Ideal.Quotient.mk_surjective (by ext; rfl) (by rw [Ideal.mk_ker, Ideal.mk_ker, h𝔭E₀])
  -- the chart point as a localization of `S/𝔓`
  letI : Algebra (S ⧸ 𝔓) (Sq ⧸ pS) := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (S ⧸ 𝔓)
      (Algebra.algebraMapSubmonoid S q.primeCompl)) (Sq ⧸ pS) :=
    IsLocalization.of_surjective (Algebra.algebraMapSubmonoid S q.primeCompl) Sq
      (Ideal.Quotient.mk 𝔓) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk pS)
      Ideal.Quotient.mk_surjective (by ext; rfl) (by rw [Ideal.mk_ker, Ideal.mk_ker])
  haveI hξloc : IsLocalization.AtPrime (Localization.AtPrime ξ)
      (ξ.comap (algebraMap (S ⧸ 𝔓) (Sq ⧸ pS))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (S ⧸ 𝔓) (Algebra.algebraMapSubmonoid S q.primeCompl))
      (Localization.AtPrime ξ) ξ
  have hξc : ξ.comap (algebraMap (S ⧸ 𝔓) (Sq ⧸ pS)) = 𝔐.map (Ideal.Quotient.mk 𝔓) :=
    localizedQuotientPrime_comap q 𝔓 𝔐 h𝔓𝔐 h𝔐q
  have hM : (ξ.comap (algebraMap (S ⧸ 𝔓) (Sq ⧸ pS))).primeCompl =
      (𝔐.map (Ideal.Quotient.mk 𝔓)).primeCompl := by
    ext x
    simp only [Ideal.mem_primeCompl_iff, hξc]
  haveI : IsLocalization (𝔐.map (Ideal.Quotient.mk 𝔓)).primeCompl (Localization.AtPrime ξ) :=
    hM ▸ hξloc
  let eB : Localization.AtPrime ξ ≃ₐ[S ⧸ 𝔓] closureStalk Xs hdE :=
    IsLocalization.algEquiv (𝔐.map (Ideal.Quotient.mk 𝔓)).primeCompl _ _
  -- the commuting square of local rings
  let f' := stalkGenerizationQuotientMap F hdE
  let g := algebraMap (Rq ⧸ Ideal.span {a}) (Localization.AtPrime ξ)
  have hsq : f'.comp eA.toRingHom = eB.toRingHom.comp g := by
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (R ⧸ Pd) q.primeCompl)
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp only [RingHom.comp_apply]
    have hL : f' (eA (algebraMap (R ⧸ Pd) (Rq ⧸ Ideal.span {a}) (Ideal.Quotient.mk Pd r))) =
        Ideal.Quotient.mk (stalkGenerizationPrime Xs hdE)
          (algebraMap S (Xs.presheaf.stalk E₀) (algebraMap R S r)) := by
      rw [eA.commutes]
      change Ideal.Quotient.mk _ ((F.stalkMap E₀).hom (Y.presheaf.germ W E hEW r)) = _
      rw [Scheme.Hom.germ_stalkMap_apply]
      rfl
    have h1 : g (algebraMap (R ⧸ Pd) (Rq ⧸ Ideal.span {a}) (Ideal.Quotient.mk Pd r)) =
        algebraMap (S ⧸ 𝔓) (Localization.AtPrime ξ) (Ideal.Quotient.mk 𝔓 (algebraMap R S r)) := by
      change algebraMap (Sq ⧸ pS) (Localization.AtPrime ξ)
          (Ideal.Quotient.mk pS (algebraMap Rq Sq (algebraMap R Rq r))) =
        algebraMap (Sq ⧸ pS) (Localization.AtPrime ξ)
          (Ideal.Quotient.mk pS (algebraMap S Sq (algebraMap R S r)))
      rw [← IsScalarTower.algebraMap_apply R Rq Sq, IsScalarTower.algebraMap_apply R S Sq]
    have hR : eB (g (algebraMap (R ⧸ Pd) (Rq ⧸ Ideal.span {a}) (Ideal.Quotient.mk Pd r))) =
        Ideal.Quotient.mk (stalkGenerizationPrime Xs hdE)
          (algebraMap S (Xs.presheaf.stalk E₀) (algebraMap R S r)) := by
      rw [h1, eB.commutes]
      rfl
    exact hL.trans hR.symm
  -- transport of étaleness
  let B := Rq ⧸ Ideal.span {a}
  haveI : Algebra.FormallyEtale B (Localization.AtPrime ξ) := het
  letI : Algebra B (closureStalk Xs hdE) := (eB.toRingHom.comp g).toAlgebra
  let eB' : Localization.AtPrime ξ ≃ₐ[B] closureStalk Xs hdE :=
    { eB.toRingEquiv with commutes' := fun _ => rfl }
  haveI : Algebra.FormallyEtale B (closureStalk Xs hdE) :=
    Algebra.FormallyEtale.of_equiv (R := B) (A := Localization.AtPrime ξ)
      (B := closureStalk Xs hdE) eB'
  letI : Algebra B (closureStalk Y hdE') := eA.toRingHom.toAlgebra
  let eA' : B ≃ₐ[B] closureStalk Y hdE' := { eA.toRingEquiv with commutes' := fun _ => rfl }
  haveI : Algebra.FormallyEtale B (closureStalk Y hdE') :=
    Algebra.FormallyEtale.of_equiv (R := B) (A := B) (B := closureStalk Y hdE') eA'
  haveI hdvrX : IsDiscreteValuationRing (closureStalk Xs hdE) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eB
  refine ⟨hdvrX, ?_⟩
  -- ramification index one
  letI : Algebra (closureStalk Y hdE') (closureStalk Xs hdE) := f'.toAlgebra
  haveI : IsScalarTower B (closureStalk Y hdE') (closureStalk Xs hdE) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    exact (congrArg (fun φ : B →+* closureStalk Xs hdE => φ x) hsq).symm
  haveI : Algebra.FormallyEtale (closureStalk Y hdE') (closureStalk Xs hdE) :=
    Algebra.FormallyEtale.of_restrictScalars (R := B)
  -- essential finite type
  letI : Algebra (Y.presheaf.stalk E) (Xs.presheaf.stalk E₀) := (F.stalkMap E₀).hom.toAlgebra
  haveI : Algebra.EssFiniteType (Y.presheaf.stalk E) (Xs.presheaf.stalk E₀) :=
    LocallyOfFiniteType.stalkMap F E₀
  letI : Algebra (Y.presheaf.stalk E) (closureStalk Xs hdE) :=
    ((Ideal.Quotient.mk (stalkGenerizationPrime Xs hdE)).comp (F.stalkMap E₀).hom).toAlgebra
  haveI : IsScalarTower (Y.presheaf.stalk E) (Xs.presheaf.stalk E₀) (closureStalk Xs hdE) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType (Xs.presheaf.stalk E₀) (closureStalk Xs hdE) :=
    Algebra.EssFiniteType.of_finiteType _ _
  haveI : Algebra.EssFiniteType (Y.presheaf.stalk E) (closureStalk Xs hdE) :=
    Algebra.EssFiniteType.comp _ (Xs.presheaf.stalk E₀) _
  haveI : IsScalarTower (Y.presheaf.stalk E) (closureStalk Y hdE') (closureStalk Xs hdE) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType (closureStalk Y hdE') (closureStalk Xs hdE) :=
    Algebra.EssFiniteType.of_comp (Y.presheaf.stalk E) _ _
  haveI : Algebra.IsUnramifiedAt (closureStalk Y hdE') (maximalIdeal (closureStalk Xs hdE)) := by
    haveI : Algebra.FormallyUnramified (closureStalk Xs hdE)
        (Localization.AtPrime (maximalIdeal (closureStalk Xs hdE))) :=
      Algebra.FormallyUnramified.of_isLocalization (maximalIdeal (closureStalk Xs hdE)).primeCompl
    exact Algebra.FormallyUnramified.comp _ (closureStalk Xs hdE) _
  exact Ideal.ramificationIdx_eq_one _ _

#print axioms allCodimChartPropertyCharZero

end
end Pcf
