/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Pcf.Stacks.Common.RegularLocalization
public import Pcf.Stacks.Common.RegularNormal
public import Pcf.Stacks.Purity.Completion
public import Pcf.Stacks.Purity.DimensionTwo
public import Pcf.Stacks.Purity.FormalEtaleLift
public import Pcf.Stacks.Purity.FiniteNormalHartogs
public import Pcf.Stacks.Purity.HenselianFiniteEtaleLift
public import Pcf.Stacks.Purity.HypersurfaceLifting
public import Pcf.Stacks.Purity.Tag0BM9Equivalence
public import Pcf.Stacks.Purity.Tag0BMAClauses

/-!
# Hypersurface finite étale lifting over a complete regular local ring

This file proves the complete-regular-local case of the lifting statement in Stacks Tag `0BLM`
(Lemma 58.20.7), which is the input `HypersurfaceFiniteEtaleLifting` of the outer induction in
Tag `0BMA` (`Pcf.Stacks.Purity.OuterInduction`).

## The statement

Let `A` be a complete regular local ring of dimension `d + 1 ≥ 3`, let `f ∈ m \ m²`, so that
`A₀ = A/fA` is regular local of dimension `d ≥ 2`, and let `U`, `U₀` be the punctured spectra.
If `V` is a finite étale cover of `U` whose restriction to `U₀` extends to a finite étale cover of
`Spec A₀`, then `V` extends to a finite étale cover of `Spec A`.

## The proof route (divergence from Stacks)

Stacks proves `0BLM` from `0BLS` (Lemma 58.20.6), whose full-faithfulness input `0BM6` (Lemma
58.19.6) uses the vanishing of the local cohomology groups
`H¹_m(A)`, `H²_m(A)` (depth `≥ 3`) and the theorem on formal functions (`0EKS`).  Local
cohomology is not available at the pinned Mathlib revision, so the proof here is different; the
statement is unchanged.  Informally:

0. (Tag `0BM9`, pcf.) `V ≅ Spec B ×_X U` for a finite, torsion-free, Stacks-normal `A`-algebra
   `B` whose spectrum is étale over `U`.
1. (Tag `09ZL`, `exists_finite_etale_lift_of_henselianLocalRing`.) `A` is henselian, so the
   given extension `Y₀` of `V|_{U₀}` lifts to a finite étale `A`-algebra `C` with
   `Y₀ ≅ Spec (C/fC)`.
2. The isomorphism `V|_{U₀} ≅ Y₀|_{U₀}` is encoded algebraically as an `A`-algebra map
   `φ₀ : B → C/fC` which becomes bijective after inverting any `x ∈ m`
   (restriction of the isomorphism to the affine open `D(xq) ⊆ U₀`).
3. Choose `x, y ∈ m` with `f, x, y` part of a regular system of parameters.  Then `f, x, y` is a
   regular sequence on `A`, hence (flatness) on `C`, so `x, y` is a regular pair on every
   `C/f^(n+1)C` and `x` is regular on `C/fC`.  Since `B` is étale over `U ⊇ D(x) ∪ D(y)`, the
   localizations `B_x`, `B_y`, `B_{xy}` are (formally) étale over `A`.
4. (`Pcf.Stacks.Purity.FormalEtaleLift`.) `φ₀` lifts uniquely to `B → C/f^(n+1)C` for every `n`:
   locally on `D(x)` and `D(y)` by formal étaleness along the nilpotent kernel, glued by the
   depth-two Hartogs lemma for the regular pair `x, y`; the lifts are compatible by uniqueness and
   converge, since `C` is `(f)`-adically complete (`Purity/Completion`), to `φ : B → C` with
   `φ mod f = φ₀`.
5. Let `p = (f)`, a prime of `A` not containing `x`.  Localizing at `p`, `φ_p` is bijective by
   Nakayama's lemma: `φ₀` is bijective after inverting `x`, `f ∈ p A_p` and `f` is a
   nonzerodivisor on `C`.
6. Hence `φ` is injective (`B` is torsion-free) and, since every element of `C` is integral over
   `A` and the Stacks-normal algebra `B` is integrally closed in its total ring of fractions,
   `φ` is surjective.  So `B ≅ C` is finite étale over `A`, and `Y = Spec B` extends `V`.

Step 4 is `exists_algHom_lift_of_isAdicComplete` (in `FormalEtaleLift`); steps 3, 5, 6 are the
algebraic core `exists_algHom_bijective_of_hypersurface_lift` below; steps 0–2 are the
translation from the finite étale covers to algebra (`exists_algHom_of_pullback_iso`,
`hypersurfacePullbackIso`), assembled in `hypersurfaceFiniteEtaleLifting_of_isAdicComplete`.
No local cohomology, no formal functions and no normality of `C` are used.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Limits IsLocalRing RingTheory.Sequence Polynomial
open scoped Pointwise

universe u v w

namespace Pcf.Stacks

/-! ### Regular systems of parameters starting with `f` -/

section RegularTriple

variable {A : Type u} [CommRing A]

/-- Transport of regularity on `QuotSMulTop` across a linear equivalence. -/
theorem isSMulRegular_quotSMulTop_congr {M M' : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M') (r s : A) :
    IsSMulRegular (QuotSMulTop r M) s ↔ IsSMulRegular (QuotSMulTop r M') s := by
  have he : (r • (⊤ : Submodule A M)).map (e : M →ₗ[A] M') = r • (⊤ : Submodule A M') := by
    rw [Submodule.map_pointwise_smul, Submodule.map_top, LinearEquiv.range]
  let e' : QuotSMulTop r M ≃ₗ[A] QuotSMulTop r M' := Submodule.Quotient.equiv _ _ e he
  exact e'.toEquiv.isSMulRegular_congr (fun m ↦ e'.map_smul s m)

/-- `QuotSMulTop r A` is the quotient ring `A / (r)`, as an `A`-module. -/
def quotSMulTopSelfEquiv (r : A) : QuotSMulTop r A ≃ₗ[A] A ⧸ Ideal.span {r} :=
  Submodule.quotEquivOfEq _ _ (by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])

/-- Regularity of a base element on `QuotSMulTop r A`, through the quotient ring. -/
theorem isSMulRegular_quotSMulTop_self_iff (r s : A) :
    IsSMulRegular (QuotSMulTop r A) s ↔ IsSMulRegular (A ⧸ Ideal.span {r}) s :=
  (quotSMulTopSelfEquiv r).toEquiv.isSMulRegular_congr
    (fun m ↦ (quotSMulTopSelfEquiv r).map_smul s m)

variable [IsRegularLocalRing A]

/-- In a regular local ring of dimension `d + 1 ≥ 3`, every `f ∈ m \ m²` is the first member of
a regular sequence `f, x, y` of elements of `m`, with `x ∉ (f)`. -/
theorem exists_isRegular_triple (d : ℕ) (hd : 2 ≤ d) (hdim : ringKrullDim A = d + 1)
    (f : A) (hf : f ∈ maximalIdeal A) (hf2 : f ∉ maximalIdeal A ^ 2) :
    ∃ x y : A, x ∈ maximalIdeal A ∧ y ∈ maximalIdeal A ∧ x ∉ Ideal.span {f} ∧
      IsRegular A [f, x, y] := by
  haveI : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  -- the hypersurface `A₀ = A/(f)`
  let A₀ := A ⧸ Ideal.span {f}
  haveI : Nontrivial A₀ := Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top hf)
  haveI hA₀ : IsRegularLocalRing A₀ := isRegularLocalRing_quotient_minimalGenerator hf hf2
  haveI : IsDomain A₀ := Pcf.Vendor.isDomain_of_isRegularLocalRing A₀
  have hdim₀ : ringKrullDim A₀ = d := ringKrullDim_quotient_minimalGenerator_eq hf hf2 d hdim
  have hdim₀ne : ringKrullDim A₀ ≠ 0 := by
    rw [hdim₀]
    intro h
    have : d = 0 := by exact_mod_cast h
    omega
  obtain ⟨xq, hxq, hxq2, hA₁⟩ := exists_regularLocalRing_quotient_minimalGenerator A₀ hdim₀ne
  -- the second hypersurface `A₁ = A₀/(xq)`
  let A₁ := A₀ ⧸ Ideal.span {xq}
  haveI : Nontrivial A₁ := Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top hxq)
  haveI : IsRegularLocalRing A₁ := hA₁
  haveI : IsDomain A₁ := Pcf.Vendor.isDomain_of_isRegularLocalRing A₁
  have hdim₁ : ringKrullDim A₁ = ((d - 1 : ℕ) : WithBot ℕ∞) := by
    apply ringKrullDim_quotient_minimalGenerator_eq hxq hxq2 (d - 1)
    rw [hdim₀]
    have : (d : WithBot ℕ∞) = ((d - 1 : ℕ) : WithBot ℕ∞) + 1 := by
      norm_cast
      omega
    exact this
  have hdim₁' : 1 ≤ ringKrullDim A₁ := by
    rw [hdim₁]
    exact_mod_cast (by omega : 1 ≤ d - 1)
  obtain ⟨yq, hyq, hyq0⟩ := exists_nonzero_mem_maximalIdeal_of_one_le_ringKrullDim A₁ hdim₁'
  -- lifts
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xq
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective yq
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
  have hxm : x ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal _).mp hxq (hu.map (Ideal.Quotient.mk _))
  have hym : y ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal _).mp hyq ((hu.map (Ideal.Quotient.mk _)).map (Ideal.Quotient.mk _))
  have hxq0 : Ideal.Quotient.mk (Ideal.span {f}) x ≠ 0 := by
    intro h
    apply hxq2
    rw [h]
    exact Ideal.zero_mem _
  have hxf : x ∉ Ideal.span {f} := fun h ↦ hxq0 (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hf0 : f ≠ 0 := by
    intro h
    apply hf2
    rw [h]
    exact Ideal.zero_mem _
  -- membership in `(f) + (x)` is vanishing in `A₁`
  have hmem₁ : ∀ a : A, a ∈ Ideal.span {f} ⊔ Ideal.span {x} ↔
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) x})
        (Ideal.Quotient.mk (Ideal.span {f}) a) = 0 := by
    intro a
    rw [Ideal.Quotient.eq_zero_iff_mem, sup_comm, ← Ideal.mem_quotient_iff_mem_sup,
      Ideal.map_span, Set.image_singleton]
  -- the three regularity conditions
  have hfreg : IsSMulRegular A f := isSMulRegular_self_of_ne_zero A hf0
  have hxreg : IsSMulRegular (QuotSMulTop f A) x := by
    rw [isSMulRegular_quotSMulTop_self_iff]
    apply isSMulRegular_quotient_of_forall
    intro a ha
    rw [smul_eq_mul, ← Ideal.Quotient.eq_zero_iff_mem, map_mul] at ha
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (mul_eq_zero.mp ha).resolve_left hxq0
  have hyreg : IsSMulRegular (QuotSMulTop x (QuotSMulTop f A)) y := by
    rw [isSMulRegular_quotSMulTop_congr (quotSMulTopSelfEquiv f)]
    apply isSMulRegular_quotSMulTop_quotient_of_forall
    intro a ha
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at ha ⊢
    rw [hmem₁] at ha ⊢
    rw [smul_eq_mul, map_mul, map_mul] at ha
    exact (mul_eq_zero.mp ha).resolve_left hyq0
  have hweak : IsWeaklyRegular A [f, x, y] :=
    (isWeaklyRegular_cons_iff A f [x, y]).mpr ⟨hfreg,
      (isWeaklyRegular_cons_iff _ x [y]).mpr ⟨hxreg,
        (isWeaklyRegular_cons_iff _ y []).mpr ⟨hyreg, IsWeaklyRegular.nil _ _⟩⟩⟩
  refine ⟨x, y, hxm, hym, hxf, IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A ?_ hweak⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hf
  · exact hxm
  · exact hym

end RegularTriple

/-! ### From a regular sequence on `C` to the regularity hypotheses on the thickenings -/

section Thickenings

variable {A : Type u} [CommRing A] {C : Type v} [CommRing C] [Algebra A C]

/-- If `f, x` is weakly regular on `C`, then `x` is regular on every `C / f^k C`. -/
theorem isSMulRegular_quotient_span_pow_of_isWeaklyRegular {f x : A}
    (h : IsWeaklyRegular C [f, x]) (k : ℕ) :
    IsSMulRegular (C ⧸ Ideal.span {algebraMap A C f ^ k}) x := by
  obtain ⟨hf, hx⟩ := (isWeaklyRegular_cons_iff C f [x]).mp h
  have hx' : IsSMulRegular (QuotSMulTop f C) x :=
    ((isWeaklyRegular_cons_iff _ x []).mp hx).1
  apply isSMulRegular_quotient_of_forall
  intro c hc
  rw [Ideal.mem_span_singleton'] at hc ⊢
  obtain ⟨a, ha⟩ := hc
  have hcross : x ^ 1 • c = f ^ k • a := by
    rw [pow_one, Algebra.smul_def, Algebra.smul_def, map_pow,
      mul_comm (algebraMap A C f ^ k) a, ha, Algebra.smul_def]
  obtain ⟨c', hc'⟩ := exists_eq_pow_smul_of_regular_pair hf hx' 1 k hcross
  exact ⟨c', by rw [hc', Algebra.smul_def, map_pow, mul_comm]⟩

/-- If `x, f, y` is weakly regular on `C`, then `y` is regular on `(C / f^k C) / x (C / f^k C)`. -/
theorem isSMulRegular_quotSMulTop_quotient_span_pow_of_isWeaklyRegular {f x y : A}
    (h : IsWeaklyRegular C [x, f, y]) (k : ℕ) :
    IsSMulRegular (QuotSMulTop x (C ⧸ Ideal.span {algebraMap A C f ^ k})) y := by
  obtain ⟨hx, h'⟩ := (isWeaklyRegular_cons_iff C x [f, y]).mp h
  obtain ⟨hf, h''⟩ := (isWeaklyRegular_cons_iff (QuotSMulTop x C) f [y]).mp h'
  have hy : IsSMulRegular (QuotSMulTop f (QuotSMulTop x C)) y :=
    ((isWeaklyRegular_cons_iff _ y []).mp h'').1
  apply isSMulRegular_quotSMulTop_quotient_of_forall
  intro c hc
  obtain ⟨j, hj, z, hz, hjz⟩ := Submodule.mem_sup.mp hc
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hj
  obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  -- in `C / xC`: `y • [c] = f^k • [a]`
  have hcross : y ^ 1 • (Submodule.Quotient.mk c : QuotSMulTop x C) =
      f ^ k • (Submodule.Quotient.mk a : QuotSMulTop x C) := by
    rw [pow_one, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq, mem_smul_top_iff_exists]
    refine ⟨e, ?_⟩
    have hjz' : a * algebraMap A C f ^ k + e * algebraMap A C x = algebraMap A C y * c := by
      rw [hjz, Algebra.smul_def]
    simp only [Algebra.smul_def, map_pow]
    rw [← hjz']
    ring
  obtain ⟨c', hc'⟩ := exists_eq_pow_smul_of_regular_pair hf hy 1 k hcross
  obtain ⟨c'', rfl⟩ := Submodule.Quotient.mk_surjective _ c'
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, mem_smul_top_iff_exists] at hc'
  obtain ⟨w, hw⟩ := hc'
  refine Submodule.mem_sup.mpr ⟨f ^ k • c'', ?_, x • w, ?_, ?_⟩
  · rw [Ideal.mem_span_singleton']
    exact ⟨c'', by rw [Algebra.smul_def, map_pow, mul_comm]⟩
  · rw [Ideal.mem_span_singleton']
    exact ⟨w, by rw [Algebra.smul_def, mul_comm]⟩
  · rw [hw]
    abel

end Thickenings

/-! ### Étaleness on basic opens of the punctured spectrum -/

section EtaleAway

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]

/-- A finite algebra étale at every prime over the punctured spectrum is étale after inverting
any element of the maximal ideal. -/
theorem etale_localization_away_of_isEtaleAt
    (hB : ∀ (q : Ideal B) [q.IsPrime], q.under A ≠ maximalIdeal A → Algebra.IsEtaleAt A q)
    {x : A} (hx : x ∈ maximalIdeal A) :
    Algebra.Etale A (Localization.Away (algebraMap A B x)) := by
  letI : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  letI : Algebra.FinitePresentation A B := inferInstance
  rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
  intro q hq
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hq
  rw [Algebra.mem_etaleLocus_iff]
  apply hB q.asIdeal
  intro h
  apply hq
  have : x ∈ q.asIdeal.under A := by
    rw [h]
    exact hx
  exact this

end EtaleAway

/-! ### Nakayama at a prime -/

section Nakayama

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {B : Type v} [AddCommGroup B] [Module A B] [Module.Finite A B]
variable {C : Type w} [AddCommGroup C] [Module A C] [Module.Finite A C]

/-- A linear map which is bijective modulo `f` after localizing at a prime `p ∋ f` is bijective
after localizing at `p`, provided `f` is a nonzerodivisor on the target.  The statement is given
elementwise. -/
theorem localized_bijective_of_mod_isSMulRegular
    (p : Ideal A) [p.IsPrime] {f : A} (hf : f ∈ p) (hfC : IsSMulRegular C f)
    (φ : B →ₗ[A] C)
    (hinj : ∀ b, φ b ∈ f • (⊤ : Submodule A C) → ∃ t ∉ p, t • b ∈ f • (⊤ : Submodule A B))
    (hsurj : ∀ c, ∃ t ∉ p, ∃ b, t • c - φ b ∈ f • (⊤ : Submodule A C)) :
    (∀ b, φ b = 0 → ∃ t ∉ p, t • b = 0) ∧ (∀ c, ∃ t ∉ p, ∃ b, t • c = φ b) := by
  classical
  let S := p.primeCompl
  let Ap := Localization.AtPrime p
  let Bp := LocalizedModule S B
  let Cp := LocalizedModule S C
  let φp : Bp →ₗ[Ap] Cp := LocalizedModule.map S φ
  have hφp : ∀ (b : B) (s : S), φp (LocalizedModule.mk b s) = LocalizedModule.mk (φ b) s :=
    fun b s ↦ LocalizedModule.map_mk S φ b s
  haveI : IsNoetherianRing Ap := IsLocalization.isNoetherianRing S Ap inferInstance
  have hfp : algebraMap A Ap f ∈ maximalIdeal Ap :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Ap p f).mpr hf
  let I : Ideal Ap := Ideal.span {algebraMap A Ap f}
  have hIjac : I ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfp)
  have hfsmul : ∀ (z : Bp), algebraMap A Ap f • z = f • z := fun z ↦ algebraMap_smul Ap f z
  have hfsmulC : ∀ (z : Cp), algebraMap A Ap f • z = f • z := fun z ↦ algebraMap_smul Ap f z
  -- injectivity
  have hker : LinearMap.ker φp = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I _ (IsNoetherian.noetherian _) ?_ hIjac
    intro z hz
    induction z using LocalizedModule.induction_on with
    | h b s =>
      rw [LinearMap.mem_ker, hφp, ← LocalizedModule.zero_mk (1 : S), LocalizedModule.mk_eq] at hz
      obtain ⟨u, hu⟩ := hz
      simp only [one_smul, smul_zero] at hu
      have hu' : φ (u • b) ∈ f • (⊤ : Submodule A C) := by
        rw [Submonoid.smul_def, map_smul, ← Submonoid.smul_def, hu]
        exact Submodule.zero_mem _
      obtain ⟨t, ht, hb'⟩ := hinj _ hu'
      rw [mem_smul_top_iff_exists] at hb'
      obtain ⟨b', hb'⟩ := hb'
      have hb'ker : φ b' = 0 := by
        apply hfC
        change f • φ b' = f • (0 : C)
        rw [smul_zero, ← map_smul, hb', map_smul, Submonoid.smul_def, map_smul,
          ← Submonoid.smul_def, hu, smul_zero]
      have hz' : LocalizedModule.mk b s =
          algebraMap A Ap f • LocalizedModule.mk b' (⟨t, ht⟩ * u * s) := by
        rw [hfsmul, LocalizedModule.smul'_mk, hb',
          ← LocalizedModule.mk_cancel_common_left (⟨t, ht⟩ * u) s b]
        congr 1
        rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul, Submonoid.smul_def]
      rw [hz']
      apply Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _)
      rw [LinearMap.mem_ker, hφp, hb'ker, LocalizedModule.zero_mk]
  -- surjectivity
  have hrange : LinearMap.range φp = ⊤ := by
    let Q := Cp ⧸ LinearMap.range φp
    have hQ : (⊤ : Submodule Ap Q) = ⊥ := by
      apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I _ Module.Finite.fg_top ?_ hIjac
      intro q _
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      induction z using LocalizedModule.induction_on with
      | h c s =>
        obtain ⟨t, ht, b, hb⟩ := hsurj c
        rw [mem_smul_top_iff_exists] at hb
        obtain ⟨c', hc'⟩ := hb
        have h1 : LocalizedModule.mk c s = LocalizedModule.mk (t • c) (⟨t, ht⟩ * s) := by
          rw [← LocalizedModule.mk_cancel_common_left (⟨t, ht⟩ : S) s c]
          rfl
        have h2 : t • c = φ b + f • c' := by
          rw [hc']
          abel
        have key : LocalizedModule.mk c s - LocalizedModule.mk (f • c') (⟨t, ht⟩ * s) =
            φp (LocalizedModule.mk b (⟨t, ht⟩ * s)) := by
          rw [hφp, h1, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk',
            IsLocalizedModule.mk_eq_mk', h2, IsLocalizedModule.mk'_add, add_sub_cancel_right]
        have hz' : (Submodule.Quotient.mk (LocalizedModule.mk c s) : Q) =
            algebraMap A Ap f • Submodule.Quotient.mk (LocalizedModule.mk c' (⟨t, ht⟩ * s)) := by
          rw [← Submodule.Quotient.mk_smul, hfsmulC, LocalizedModule.smul'_mk,
            Submodule.Quotient.eq, key]
          exact LinearMap.mem_range_self _ _
        rw [hz']
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    rw [← Submodule.Quotient.subsingleton_iff]
    exact ⟨fun a b ↦ by
      have ha : a ∈ (⊥ : Submodule Ap Q) := hQ ▸ Submodule.mem_top
      have hb : b ∈ (⊥ : Submodule Ap Q) := hQ ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at ha hb
      rw [ha, hb]⟩
  refine ⟨fun b hb ↦ ?_, fun c ↦ ?_⟩
  · have hz : LocalizedModule.mk b (1 : S) ∈ LinearMap.ker φp := by
      rw [LinearMap.mem_ker, hφp, hb, LocalizedModule.zero_mk]
    rw [hker, Submodule.mem_bot, ← LocalizedModule.zero_mk (1 : S), LocalizedModule.mk_eq] at hz
    obtain ⟨u, hu⟩ := hz
    simp only [one_smul, smul_zero] at hu
    exact ⟨u, u.2, hu⟩
  · have hz : LocalizedModule.mk c (1 : S) ∈ LinearMap.range φp := by
      rw [hrange]
      exact Submodule.mem_top
    obtain ⟨z, hz⟩ := hz
    induction z using LocalizedModule.induction_on with
    | h b s =>
      rw [hφp, LocalizedModule.mk_eq] at hz
      obtain ⟨u, hu⟩ := hz
      simp only [one_smul] at hu
      refine ⟨u * s, (u * s).2, u • b, ?_⟩
      simp only [Submonoid.smul_def] at hu
      rw [mul_smul, Submonoid.smul_def, map_smul]
      exact hu.symm

end Nakayama

/-! ### Stacks-normal algebras are integrally closed in their fractions -/

section IntegrallyClosed

variable {A : Type u} [CommRing A] [IsDomain A]
variable {B : Type v} [CommRing B] [Algebra A B] [Module.IsTorsionFree A B]

/-- In a finite torsion-free Stacks-normal algebra `B` over a domain `A`, an element `b` such
that `b / s` is integral over `A` (for a nonzero `s ∈ A`, in cleared-denominator form) lies in
`s B`. -/
theorem mem_span_of_scaleRoots_aeval_eq_zero_of_isStacksNormalRing
    (hB : IsStacksNormalRing B) {s : A} (hs : s ≠ 0) {b : B} {P : A[X]} (hP : P.Monic)
    (h : aeval b (P.scaleRoots s) = 0) :
    b ∈ Ideal.span {algebraMap A B s} := by
  classical
  have hsreg : IsSMulRegular B s :=
    Module.IsTorsionFree.isSMulRegular (isRegular_iff_ne_zero.mpr hs)
  -- the colon ideal `{a | a • b ∈ (s)}`
  let J : Ideal B :=
    Submodule.comap (LinearMap.toSpanSingleton B B b) (Ideal.span {algebraMap A B s})
  have hJ : ∀ a : B, a ∈ J ↔ a * b ∈ Ideal.span {algebraMap A B s} := fun a ↦ Iff.rfl
  -- at every maximal ideal `q`, some `u ∉ q` lies in `J`
  have hlocal : ∀ (q : Ideal B) [q.IsMaximal], ∃ u ∉ q, u ∈ J := by
    intro q hq
    letI : q.IsPrime := hq.isPrime
    let Bq := Localization.AtPrime q
    haveI : IsDomain Bq := hB.isDomain_atPrime ⟨q, inferInstance⟩
    haveI : IsIntegrallyClosed Bq := hB.isIntegrallyClosed_atPrime ⟨q, inferInstance⟩
    let F := FractionRing Bq
    haveI : IsScalarTower A B F := IsScalarTower.of_algebraMap_eq fun a ↦ by
      rw [IsScalarTower.algebraMap_apply A Bq F, IsScalarTower.algebraMap_apply A B Bq,
        ← IsScalarTower.algebraMap_apply B Bq F]
    have hsq : algebraMap B Bq (algebraMap A B s) ≠ 0 := by
      intro h0
      obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl Bq _).mp h0
      have hu0 : (u : B) = 0 := by
        apply hsreg
        change s • (u : B) = s • (0 : B)
        rw [smul_zero, Algebra.smul_def, mul_comm]
        exact hu
      exact u.2 (hu0 ▸ q.zero_mem)
    have hsF : algebraMap Bq F (algebraMap B Bq (algebraMap A B s)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective Bq F)).mpr hsq
    have hsF' : algebraMap A F s ≠ 0 := by
      rwa [IsScalarTower.algebraMap_apply A B F, IsScalarTower.algebraMap_apply B Bq F]
    let z : F := algebraMap Bq F (algebraMap B Bq b) / algebraMap Bq F (algebraMap B Bq
      (algebraMap A B s))
    have hz : s • z = algebraMap B F b := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B F,
        IsScalarTower.algebraMap_apply B Bq F, IsScalarTower.algebraMap_apply B Bq F b]
      exact mul_div_cancel₀ _ hsF
    have hzP : aeval z P = 0 := by
      have h1 : aeval (algebraMap B F b) (P.scaleRoots s) = 0 := by
        rw [show algebraMap B F b = IsScalarTower.toAlgHom A B F b from rfl, aeval_algHom_apply,
          h, map_zero]
      rw [← hz, scaleRoots_aeval_smul] at h1
      rw [Algebra.smul_def, map_pow] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hsF')
    have hzintA : IsIntegral A z := ⟨P, hP, by rwa [← aeval_def]⟩
    have hzint : IsIntegral Bq z := IsIntegral.tower_top (R := A) (A := Bq) hzintA
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzint
    have hbw : algebraMap B Bq b = algebraMap B Bq (algebraMap A B s) * w := by
      apply IsFractionRing.injective Bq F
      rw [map_mul, hw]
      exact (mul_div_cancel₀ _ hsF).symm
    obtain ⟨⟨b₁, u⟩, hu⟩ := IsLocalization.mk'_surjective q.primeCompl w
    change IsLocalization.mk' Bq b₁ u = w at hu
    rw [← hu, ← IsLocalization.mk'_one (M := q.primeCompl) Bq b,
      ← IsLocalization.mk'_one (M := q.primeCompl) Bq (algebraMap A B s),
      ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq,
      IsLocalization.eq_iff_exists q.primeCompl] at hbw
    obtain ⟨v, hv⟩ := hbw
    simp only [OneMemClass.coe_one, one_mul] at hv
    refine ⟨(v : B) * u, (v * u).2, ?_⟩
    rw [hJ, Ideal.mem_span_singleton']
    exact ⟨(v : B) * b₁, by linear_combination (-1 : B) * hv⟩
  -- hence `J = ⊤`
  have hJtop : J = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨u, hu, huJ⟩ := hlocal q
    exact hu (hJq huJ)
  have h1 : (1 : B) ∈ J := by
    rw [hJtop]
    exact Submodule.mem_top
  rw [hJ, one_mul] at h1
  exact h1

end IntegrallyClosed

/-! ### The algebraic core: the lift is an isomorphism -/

section CoreHelpers

variable (A : Type u) [CommRing A]

/-- Weakly regular sequences restrict to prefixes of length two. -/
theorem isWeaklyRegular_pair_of_triple {M : Type*} [AddCommGroup M] [Module A M]
    {a b c : A} (h : IsWeaklyRegular M [a, b, c]) : IsWeaklyRegular M [a, b] := by
  obtain ⟨ha, h'⟩ := (isWeaklyRegular_cons_iff M a [b, c]).mp h
  obtain ⟨hb, -⟩ := (isWeaklyRegular_cons_iff _ b [c]).mp h'
  exact (isWeaklyRegular_cons_iff M a [b]).mpr ⟨ha, (isWeaklyRegular_cons_iff _ b []).mpr
    ⟨hb, IsWeaklyRegular.nil _ _⟩⟩

/-- Membership in `f • ⊤` is membership in the ideal generated by the image of `f`. -/
theorem mem_smul_top_iff_mem_span {C : Type*} [CommRing C] [Algebra A C] (f : A) (c : C) :
    c ∈ f • (⊤ : Submodule A C) ↔ c ∈ Ideal.span {algebraMap A C f} := by
  rw [mem_smul_top_iff_exists, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c', rfl⟩
    exact ⟨c', by rw [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Algebra.smul_def, mul_comm]⟩

end CoreHelpers

section Core

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A]

/-- **The algebraic core of the complete-regular-local hypersurface lifting.**

Let `A` be a complete regular local ring of dimension `d + 1 ≥ 3` and `f ∈ m \ m²`.  Let `B` be
a finite torsion-free Stacks-normal `A`-algebra which is étale at every prime over the punctured
spectrum, let `C` be a finite étale `A`-algebra, and let `φ₀ : B → C / fC` be an `A`-algebra map
which becomes bijective after inverting any `x ∈ m` (stated elementwise).  Then `φ₀` lifts to an
`A`-algebra isomorphism `B ≅ C`.

The proof route differs from Stacks Tags `0BLM`/`0BM6` (no local cohomology): formally étale
lifting on two basic opens glued by a depth-two Hartogs argument, completeness, Nakayama at the
prime `(f)`, and integral closure. -/
theorem exists_algHom_bijective_of_hypersurface_lift
    (d : ℕ) (hd : 2 ≤ d) (hdim : ringKrullDim A = d + 1)
    (f : A) (hf : f ∈ maximalIdeal A) (hf2 : f ∉ maximalIdeal A ^ 2)
    (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (hBnormal : IsStacksNormalRing B)
    (hBetale : ∀ (q : Ideal B) [q.IsPrime], q.under A ≠ maximalIdeal A → Algebra.IsEtaleAt A q)
    (C : Type u) [CommRing C] [Algebra A C] [Module.Finite A C] [Algebra.Etale A C]
    (φ₀ : B →ₐ[A] C ⧸ Ideal.span {algebraMap A C f})
    (hφ₀inj : ∀ x ∈ maximalIdeal A, ∀ b : B, φ₀ b = 0 →
      ∃ k : ℕ, x ^ k • b ∈ Ideal.span {algebraMap A B f})
    (hφ₀surj : ∀ x ∈ maximalIdeal A, ∀ c : C ⧸ Ideal.span {algebraMap A C f},
      ∃ (k : ℕ) (b : B), x ^ k • c = φ₀ b) :
    ∃ φ : B →ₐ[A] C, Function.Bijective φ ∧
      (Ideal.Quotient.mkₐ A (Ideal.span {algebraMap A C f})).comp φ = φ₀ := by
  haveI : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  obtain ⟨x, y, hxm, hym, hxf, hreg⟩ := exists_isRegular_triple d hd hdim f hf hf2
  -- regular sequences on the flat algebra `C`
  have hweak : ∀ rs : List A, IsRegular A rs → IsWeaklyRegular C rs := fun rs h ↦ by
    rw [← isWeaklyRegular_map_algebraMap_iff (S := C) (M := C)]
    exact h.toIsWeaklyRegular.of_flat
  have hreg_xfy : IsRegular A [x, f, y] :=
    IsLocalRing.isRegular_of_perm hreg (List.Perm.swap x f [y])
  have hreg_fyx : IsRegular A [f, y, x] :=
    IsLocalRing.isRegular_of_perm hreg (List.Perm.cons f (List.Perm.swap y x []))
  have hC_fxy := hweak _ hreg
  have hC_xfy := hweak _ hreg_xfy
  have hC_fyx := hweak _ hreg_fyx
  have hC_fx : IsWeaklyRegular C [f, x] := isWeaklyRegular_pair_of_triple A hC_fxy
  have hC_fy : IsWeaklyRegular C [f, y] := isWeaklyRegular_pair_of_triple A hC_fyx
  have hfC : IsSMulRegular C f := ((isWeaklyRegular_cons_iff C f [x, y]).mp hC_fxy).1
  have hx_n : ∀ n, IsSMulRegular (C ⧸ Ideal.span {algebraMap A C f ^ (n + 1)}) x := fun n ↦
    isSMulRegular_quotient_span_pow_of_isWeaklyRegular hC_fx (n + 1)
  have hy_n : ∀ n, IsSMulRegular (C ⧸ Ideal.span {algebraMap A C f ^ (n + 1)}) y := fun n ↦
    isSMulRegular_quotient_span_pow_of_isWeaklyRegular hC_fy (n + 1)
  have hxy_n : ∀ n,
      IsSMulRegular (QuotSMulTop x (C ⧸ Ideal.span {algebraMap A C f ^ (n + 1)})) y := fun n ↦
    isSMulRegular_quotSMulTop_quotient_span_pow_of_isWeaklyRegular hC_xfy (n + 1)
  have hxN : IsSMulRegular (C ⧸ Ideal.span {algebraMap A C f}) x := by
    have := isSMulRegular_quotient_span_pow_of_isWeaklyRegular hC_fx 1
    rwa [pow_one] at this
  -- étaleness of `B` on the basic opens
  haveI : Algebra.Etale A (Localization.Away (algebraMap A B x)) :=
    etale_localization_away_of_isEtaleAt hBetale hxm
  haveI : Algebra.Etale A (Localization.Away (algebraMap A B y)) :=
    etale_localization_away_of_isEtaleAt hBetale hym
  haveI : Algebra.Etale A (Localization.Away (algebraMap A B (x * y))) :=
    etale_localization_away_of_isEtaleAt hBetale (Ideal.mul_mem_left _ x hym)
  -- completeness of `C`
  haveI : IsAdicComplete (Ideal.span {f}) C := isAdicComplete_span_singleton_of_finite hf C
  -- the lift
  obtain ⟨φ, hφ⟩ := exists_algHom_lift_of_isAdicComplete f hx_n hy_n hxy_n hxN φ₀
  have hφb : ∀ b, Ideal.Quotient.mk (Ideal.span {algebraMap A C f}) (φ b) = φ₀ b := fun b ↦
    AlgHom.congr_fun hφ b
  -- the prime `(f)`
  let p : Ideal A := Ideal.span {f}
  have hp : p.IsPrime := by
    haveI : Nontrivial (A ⧸ p) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top hf)
    haveI : IsRegularLocalRing (A ⧸ p) := isRegularLocalRing_quotient_minimalGenerator hf hf2
    haveI : IsDomain (A ⧸ p) := Pcf.Vendor.isDomain_of_isRegularLocalRing _
    exact (Ideal.Quotient.isDomain_iff_prime p).mp inferInstance
  have hxp : ∀ k : ℕ, x ^ k ∉ p := fun k hk ↦ hxf (hp.mem_of_pow_mem k hk)
  -- Nakayama at `p`
  have hinj : ∀ b, φ b ∈ f • (⊤ : Submodule A C) → ∃ t ∉ p, t • b ∈ f • (⊤ : Submodule A B) := by
    intro b hb
    have h0 : φ₀ b = 0 := by
      rw [← hφb]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_smul_top_iff_mem_span A f _).mp hb)
    obtain ⟨k, hk⟩ := hφ₀inj x hxm b h0
    exact ⟨x ^ k, hxp k, (mem_smul_top_iff_mem_span A f _).mpr hk⟩
  have hsurj : ∀ c, ∃ t ∉ p, ∃ b, t • c - φ b ∈ f • (⊤ : Submodule A C) := by
    intro c
    obtain ⟨k, b, hb⟩ := hφ₀surj x hxm (Ideal.Quotient.mk _ c)
    refine ⟨x ^ k, hxp k, b, (mem_smul_top_iff_mem_span A f _).mpr ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, Ideal.Quotient.mk_smul_base, hb, hφb,
      sub_self]
  haveI : p.IsPrime := hp
  obtain ⟨hinj', hsurj'⟩ :=
    localized_bijective_of_mod_isSMulRegular p (Ideal.mem_span_singleton_self f) hfC
      φ.toLinearMap hinj hsurj
  have htne : ∀ t : A, t ∉ p → t ≠ 0 := fun t ht h0 ↦ ht (h0 ▸ p.zero_mem)
  -- injectivity
  have hφinj : Function.Injective φ := by
    intro b₁ b₂ h
    obtain ⟨t, ht, ht0⟩ := hinj' (b₁ - b₂) (by rw [AlgHom.toLinearMap_apply, map_sub, h, sub_self])
    have hreg : IsSMulRegular B t :=
      Module.IsTorsionFree.isSMulRegular (isRegular_iff_ne_zero.mpr (htne t ht))
    apply sub_eq_zero.mp
    apply hreg
    change t • (b₁ - b₂) = t • (0 : B)
    rw [ht0, smul_zero]
  -- surjectivity, by integral closure
  have hφsurj : Function.Surjective φ := by
    intro c
    obtain ⟨t, ht, b, hb⟩ := hsurj' c
    rw [AlgHom.toLinearMap_apply] at hb
    have ht0 : t ≠ 0 := htne t ht
    have htC : IsSMulRegular C t := by
      have h1 : IsWeaklyRegular A [t] :=
        (isWeaklyRegular_singleton_iff A t).mpr (isSMulRegular_self_of_ne_zero A ht0)
      have h2 : IsWeaklyRegular C [t] := by
        rw [← isWeaklyRegular_map_algebraMap_iff (S := C) (M := C)]
        exact h1.of_flat
      exact (isWeaklyRegular_singleton_iff C t).mp h2
    obtain ⟨P, hP, hPc⟩ := Algebra.IsIntegral.isIntegral (R := A) c
    have h1 : aeval (φ b) (P.scaleRoots t) = 0 := by
      rw [← hb, Algebra.smul_def]
      exact scaleRoots_aeval_eq_zero (by rwa [aeval_def])
    have h2 : aeval b (P.scaleRoots t) = 0 := by
      apply hφinj
      rw [map_zero, ← h1, aeval_algHom_apply]
    have hbt := mem_span_of_scaleRoots_aeval_eq_zero_of_isStacksNormalRing hBnormal ht0 hP h2
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hbt
    refine ⟨a, ?_⟩
    apply htC
    change t • φ a = t • c
    rw [hb, ← ha, map_mul, AlgHom.commutes, Algebra.smul_def, mul_comm]
  exact ⟨φ, ⟨hφinj, hφsurj⟩, hφ⟩

/-- The finite normal algebra `B` of the core theorem is finite étale over `A`. -/
theorem etale_of_hypersurface_lift
    (d : ℕ) (hd : 2 ≤ d) (hdim : ringKrullDim A = d + 1)
    (f : A) (hf : f ∈ maximalIdeal A) (hf2 : f ∉ maximalIdeal A ^ 2)
    (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (hBnormal : IsStacksNormalRing B)
    (hBetale : ∀ (q : Ideal B) [q.IsPrime], q.under A ≠ maximalIdeal A → Algebra.IsEtaleAt A q)
    (C : Type u) [CommRing C] [Algebra A C] [Module.Finite A C] [Algebra.Etale A C]
    (φ₀ : B →ₐ[A] C ⧸ Ideal.span {algebraMap A C f})
    (hφ₀inj : ∀ x ∈ maximalIdeal A, ∀ b : B, φ₀ b = 0 →
      ∃ k : ℕ, x ^ k • b ∈ Ideal.span {algebraMap A B f})
    (hφ₀surj : ∀ x ∈ maximalIdeal A, ∀ c : C ⧸ Ideal.span {algebraMap A C f},
      ∃ (k : ℕ) (b : B), x ^ k • c = φ₀ b) :
    Algebra.Etale A B := by
  obtain ⟨φ, hφ, -⟩ := exists_algHom_bijective_of_hypersurface_lift A d hd hdim f hf hf2 B
    hBnormal hBetale C φ₀ hφ₀inj hφ₀surj
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ hφ).symm

end Core

/-! ### From the geometric isomorphism over the punctured hypersurface to algebra -/

set_option backward.isDefEq.respectTransparency false in
/-- From an isomorphism over the punctured spectrum between the restrictions of `Spec D'` and
`Spec D`, and the Hartogs property for `D'`, produce an `R`-algebra map `D → D'` which becomes
bijective after inverting any element of the maximal ideal (stated elementwise). -/
theorem exists_algHom_of_pullback_iso
    (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]
    (B B' : CommRingCat.{u}) [Algebra R B] [Algebra R B'] [Module.Finite R B]
    (g : Over.mk (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B')))
        (puncturedSpectrum R).ι) ⟶
      Over.mk (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (puncturedSpectrum R).ι)) [IsIso g]
    (hB' : Function.Bijective
      (((Scheme.ΓSpecIso B').inv ≫
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B')))
          (puncturedSpectrum R).ι).appTop).hom)) :
    ∃ φ : B →ₐ[R] B',
      (∀ x ∈ maximalIdeal R, ∀ b : B, φ b = 0 → ∃ k : ℕ, x ^ k • b = 0) ∧
      (∀ x ∈ maximalIdeal R, ∀ c : B', ∃ (k : ℕ) (b : B), x ^ k • c = φ b) := by
  let p : Spec B ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let p' : Spec B' ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B'))
  let i := (puncturedSpectrum R).ι
  let P := pullback p i
  let P' := pullback p' i
  let j : P ⟶ Spec B := pullback.fst p i
  let j' : P' ⟶ Spec B' := pullback.fst p' i
  let q : P ⟶ puncturedSpectrumScheme R := pullback.snd p i
  let q' : P' ⟶ puncturedSpectrumScheme R := pullback.snd p' i
  let W : (Spec B).Opens := j.opensRange
  let γ : B ⟶ Γ(P, ⊤) := (Scheme.ΓSpecIso B).inv ≫ j.appTop
  let γ' : B' ⟶ Γ(P', ⊤) := (Scheme.ΓSpecIso B').inv ≫ j'.appTop
  have hγ' : Function.Bijective γ'.hom := hB'
  let gP : P' ⟶ P := g.left
  have hgq : gP ≫ q = q' := Over.w g
  haveI : IsIso gP := by
    change IsIso ((Over.forget _).map g)
    infer_instance
  let gΓ : Γ(P, ⊤) ⟶ Γ(P', ⊤) := gP.appTop
  have hgΓ : Function.Bijective gΓ.hom :=
    (ConcreteCategory.isIso_iff_bijective gΓ).mp inferInstance
  -- compatibility with the base ring
  have hγR : ∀ r : R, gΓ (γ (algebraMap R B r)) = γ' (algebraMap R B' r) := by
    intro r
    have hp : CommRingCat.ofHom (algebraMap R B) ≫ (Scheme.ΓSpecIso B).inv =
        (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop := by
      exact Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R B))
    have hp' : CommRingCat.ofHom (algebraMap R B') ≫ (Scheme.ΓSpecIso B').inv =
        (Scheme.ΓSpecIso (.of R)).inv ≫ p'.appTop := by
      exact Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R B'))
    have hjp : j ≫ p = q ≫ i := pullback.condition
    have hjp' : j' ≫ p' = q' ≫ i := pullback.condition
    have h1 : γ (algebraMap R B r) =
        ((Scheme.ΓSpecIso (.of R)).inv ≫ (q ≫ i).appTop) r := by
      change (CommRingCat.ofHom (algebraMap R B) ≫ (Scheme.ΓSpecIso B).inv ≫ j.appTop) r = _
      rw [← Category.assoc, hp, Category.assoc, ← Scheme.Hom.comp_appTop, hjp]
    have h1' : γ' (algebraMap R B' r) =
        ((Scheme.ΓSpecIso (.of R)).inv ≫ (q' ≫ i).appTop) r := by
      change (CommRingCat.ofHom (algebraMap R B') ≫ (Scheme.ΓSpecIso B').inv ≫
        j'.appTop) r = _
      rw [← Category.assoc, hp', Category.assoc, ← Scheme.Hom.comp_appTop, hjp']
    rw [h1, h1']
    change ((Scheme.ΓSpecIso (.of R)).inv ≫ (q ≫ i).appTop ≫ gP.appTop) r = _
    rw [← Scheme.Hom.comp_appTop, ← Category.assoc, hgq]
  -- the algebra map
  let γ'e : B' ≃+* Γ(P', ⊤) := RingEquiv.ofBijective γ'.hom hγ'
  let φ₀ : B →+* B' := γ'e.symm.toRingHom.comp (gΓ.hom.comp γ.hom)
  have hφ₀ : ∀ b, γ' (φ₀ b) = gΓ (γ b) := fun b ↦ γ'e.apply_symm_apply _
  let φ : B →ₐ[R] B' :=
    { φ₀ with
      commutes' := fun r ↦ by
        apply hγ'.injective
        change γ' (φ₀ (algebraMap R B r)) = γ' (algebraMap R B' r)
        rw [hφ₀, hγR] }
  have hφ : ∀ b, φ b = φ₀ b := fun _ ↦ rfl
  -- the open `W` and its sections
  have hW : W = p ⁻¹ᵁ puncturedSpectrum R := by
    dsimp only [W, j]
    rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Opens.opensRange_ι]
  have hWcompact : IsCompact W.1 := by
    rw [hW]
    haveI : IsFinite p := by
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr inferInstance
    exact p.isCompact_preimage (isCompact_puncturedSpectrum R)
  letI : Algebra B Γ(Spec B, W) :=
    (((Scheme.ΓSpecIso B).inv ≫
      (Spec B).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op).hom).toAlgebra
  let e := IsOpenImmersion.ΓIsoTop j
  have he : ∀ b : B, e.inv (algebraMap B Γ(Spec B, W) b) = γ b := by
    intro b
    have etop : (⊤ : P.Opens) ≤ j ⁻¹ᵁ W := by
      change (⊤ : P.Opens) ≤ j ⁻¹ᵁ j.opensRange
      rw [← j.image_top_eq_opensRange, j.preimage_image_eq]
    have hcomp : (Spec B).presheaf.map
          (eqToHom j.image_top_eq_opensRange).op ≫
          (j.appIso ⊤).hom =
        j.appLE W ⊤ etop := by
      rw [j.appIso_hom']
      exact j.map_appLE' etop j.image_top_eq_opensRange
    simp only [e, IsOpenImmersion.ΓIsoTop, Iso.trans_inv,
      Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, eqToHom_op,
      Iso.symm_inv]
    change ((Spec B).presheaf.map
          (eqToHom j.image_top_eq_opensRange).op ≫
        (j.appIso ⊤).hom).hom
        (((Scheme.ΓSpecIso B).inv ≫
          (Spec B).presheaf.map
            (homOfLE (show W ≤ ⊤ from le_top)).op).hom b) = _
    rw [← CommRingCat.comp_apply, hcomp]
    change ((Spec B).presheaf.map
        (homOfLE (show W ≤ ⊤ from le_top)).op ≫
      j.appLE W ⊤ etop).hom ((Scheme.ΓSpecIso B).inv b) = _
    rw [j.map_appLE]
    simp [Scheme.Hom.appLE, γ]
  have heinj : Function.Injective e.inv.hom :=
    ((ConcreteCategory.isIso_iff_bijective e.inv).mp inferInstance).injective
  have hehom : ∀ s : Γ(P, ⊤), e.inv (e.hom s) = s := fun s ↦ by
    rw [← CommRingCat.comp_apply, e.hom_inv_id]
    rfl
  -- basic opens inside `W`
  have hDx : ∀ x ∈ maximalIdeal R,
      @LE.le (Spec B).Opens _ (PrimeSpectrum.basicOpen (algebraMap R B x)) W := by
    intro x hxm
    rw [hW]
    intro z hz
    change p.base z ∈ puncturedSpectrum R
    rw [mem_puncturedSpectrum_iff]
    intro heq
    have hxnot : algebraMap R B x ∉ z.asIdeal :=
      (PrimeSpectrum.mem_basicOpen (algebraMap R B x) z).mp hz
    apply hxnot
    change x ∈ (p.base z).asIdeal
    rw [heq]
    exact hxm
  have hD : ∀ x ∈ maximalIdeal R,
      @Eq (Spec B).Opens ((Spec B).basicOpen (algebraMap B Γ(Spec B, W) (algebraMap R B x)))
        (PrimeSpectrum.basicOpen (algebraMap R B x)) := by
    intro x hxm
    change (Spec B).basicOpen ((Spec B).presheaf.map
      (homOfLE (show W ≤ ⊤ from le_top)).op ((Scheme.ΓSpecIso B).inv (algebraMap R B x))) = _
    rw [Scheme.basicOpen_res, basicOpen_eq_of_affine, inf_eq_right.mpr (hDx x hxm)]
  refine ⟨φ, fun x hxm b hb ↦ ?_, fun x hxm c ↦ ?_⟩
  · -- injectivity after inverting `x`
    have h1 : gΓ (γ b) = 0 := by
      rw [← hφ₀, ← hφ, hb, map_zero]
    have h2 : γ b = 0 := hgΓ.injective (by rw [h1, map_zero])
    have h3 : algebraMap B Γ(Spec B, W) b = 0 := heinj (by rw [he, h2, map_zero])
    let Dx : (Spec B).Opens := PrimeSpectrum.basicOpen (algebraMap R B x)
    have h4 : (Spec B).presheaf.map (homOfLE (hDx x hxm)).op (algebraMap B Γ(Spec B, W) b) = 0 := by
      rw [h3, map_zero]
    erw [spec_algebraMap_res] at h4
    obtain ⟨⟨m, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (algebraMap R B x)) Γ(Spec B, Dx) b).mp h4
    refine ⟨n, ?_⟩
    rw [Algebra.smul_def, map_pow]
    exact hm
  · -- surjectivity after inverting `x`
    obtain ⟨s, hs⟩ := hgΓ.surjective (γ' c)
    let t : Γ(Spec B, W) := e.hom s
    have ht : e.inv t = s := hehom s
    let xb : B := algebraMap R B x
    let Dx : (Spec B).Opens := PrimeSpectrum.basicOpen xb
    let r : Γ(Spec B, W) := algebraMap B Γ(Spec B, W) xb
    let tx : Γ(Spec B, Dx) := (Spec B).presheaf.map (homOfLE (hDx x hxm)).op t
    obtain ⟨b, n, hsec⟩ : ∃ (b : B) (n : ℕ),
        tx * algebraMap B Γ(Spec B, Dx) (xb ^ n) = algebraMap B Γ(Spec B, Dx) b :=
      ⟨_, _, IsLocalization.Away.sec_spec xb tx⟩
    let u : Γ(Spec B, W) := r ^ n * t - algebraMap B Γ(Spec B, W) b
    have hu : (Spec B).presheaf.map (homOfLE (hDx x hxm)).op u = 0 := by
      have e1 : (Spec B).presheaf.map (homOfLE (hDx x hxm)).op (algebraMap B Γ(Spec B, W) b) =
          algebraMap B Γ(Spec B, Dx) b := spec_algebraMap_res (hDx x hxm) b
      have e2 : (Spec B).presheaf.map (homOfLE (hDx x hxm)).op r =
          algebraMap B Γ(Spec B, Dx) xb := spec_algebraMap_res (hDx x hxm) xb
      change (Spec B).presheaf.map (homOfLE (hDx x hxm)).op
        (r ^ n * t - algebraMap B Γ(Spec B, W) b) = 0
      rw [map_sub, map_mul, map_pow, e1, e2, ← map_pow, mul_comm]
      change tx * _ - _ = 0
      rw [hsec, sub_self]
    have hu' : u |_ ((Spec B).basicOpen r) = 0 := by
      have hzcast := congrArg
        (fun z : Γ(Spec B, Dx) ↦ (Spec B).presheaf.map (eqToHom (hD x hxm)).op z) hu
      rw [map_zero, ← (Spec B).presheaf.map_comp_apply,
        ← op_comp, eqToHom_comp_homOfLE] at hzcast
      exact hzcast
    obtain ⟨m, hm⟩ :=
      exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (Spec B) hWcompact u r hu'
    have h5 : r ^ (m + n) * t = r ^ m * algebraMap B Γ(Spec B, W) b := by
      rw [pow_add]
      linear_combination hm
    -- transport to `Γ(P, ⊤)`, then to `Γ(P', ⊤)`
    have h6 : γ (xb ^ (m + n)) * s = γ (xb ^ m * b) := by
      have := congrArg e.inv.hom h5
      rw [map_mul, map_mul, ht] at this
      simp only [r, ← map_pow, he] at this
      rw [← map_mul] at this
      simpa only [he] using this
    have h7 : γ' (algebraMap R B' (x ^ (m + n)) * c) = γ' (φ (xb ^ m * b)) := by
      rw [map_mul, hφ, hφ₀, ← h6, map_mul, hs, ← hγR, map_pow, map_pow]
    refine ⟨m + n, x ^ m • b, ?_⟩
    have h8 := hγ'.injective h7
    rw [Algebra.smul_def, h8, Algebra.smul_def, map_pow]

/-! ### Henselian local rings from completeness -/

/-- An `m`-adically complete local ring is henselian local. -/
theorem henselianLocalRing_of_isAdicComplete (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk _))

/-! ### The two pullbacks over the punctured hypersurface -/

section Identifications

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)

local notation "A₀" => A ⧸ Ideal.span (Set.singleton f)

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting `Spec B ×_X U` to the punctured hypersurface `U₀` is the restriction of
`Spec (A₀ ⊗[A] B)` to `U₀`. -/
noncomputable def hypersurfacePullbackIso [IsLocalRing A₀]
    (B : Type u) [CommRing B] [Algebra A B] :
    (Over.pullback (puncturedHypersurfaceMap A f)).obj
        ((Over.pullback (puncturedSpectrum A).ι).obj
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))))) ≅
      Over.mk (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A₀ (A₀ ⊗[A] B))))
        (puncturedSpectrum A₀).ι) := by
  let h := puncturedHypersurfaceMap A f
  let ι := (puncturedSpectrum A).ι
  let ι₀ := (puncturedSpectrum A₀).ι
  let j : Spec (.of A₀) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A A₀))
  let Z : Over (Spec (.of A)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  have hsq : h ≫ ι = ι₀ ≫ j := puncturedHypersurfaceMap_comp_ι A f
  let e1 : (Over.pullback h).obj ((Over.pullback ι).obj Z) ≅ (Over.pullback (h ≫ ι)).obj Z :=
    ((Over.pullbackComp h ι).app Z).symm
  let e2 : (Over.pullback (h ≫ ι)).obj Z ≅ (Over.pullback (ι₀ ≫ j)).obj Z :=
    eqToIso (congrArg (fun m : puncturedSpectrumScheme A₀ ⟶ Spec (.of A) ↦
      (Over.pullback m).obj Z) hsq)
  let e3 : (Over.pullback (ι₀ ≫ j)).obj Z ≅ (Over.pullback ι₀).obj ((Over.pullback j).obj Z) :=
    (Over.pullbackComp ι₀ j).app Z
  let e4 : (Over.pullback j).obj Z ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A₀ (A₀ ⊗[A] B)))) := by
    refine Over.isoMk (pullbackSymmetry _ _ ≪≫ pullbackSpecIso A A₀ B) ?_
    change (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap A B))) j).hom ≫
        (pullbackSpecIso A A₀ B).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap A₀ (A₀ ⊗[A] B))) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) j
    rw [pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]
  exact e1 ≪≫ e2 ≪≫ e3 ≪≫ (Over.pullback ι₀).mapIso e4

end Identifications

/-! ### The hypersurface finite étale lifting -/

section Main

open scoped TensorProduct

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A]

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks Tag 0BLM, complete regular local case.**

Let `A` be a complete regular local ring of dimension `d + 1 ≥ 3` and `f ∈ m \ m²`.  If a finite
étale cover of the punctured spectrum of `A` restricts over the punctured spectrum of `A/(f)` to
a cover which extends over `Spec (A/(f))`, then it extends over `Spec A`.

Divergence from Stacks: the statement is the case of Lemma 58.20.7 (`0BLM`) in which `A` is
complete and regular (depth `≥ 3` being automatic) and `f` is a minimal generator of `m`, which
is the case used in the induction of Tag `0BMA`.  Step 1 of the proof (the lift of `Y₀` by
`09ZL` over the henselian pair `(A, fA)`) is that of the Stacks proof of Lemma 58.20.6 (`0BLS`) in
the complete case; step 0 (the finite normal model of Tag `0BM9`) is a preliminary.  The
full-faithfulness step diverges: Stacks uses Lemma 58.19.6 (`0BM6`: `H¹_𝔪`, `H²_𝔪` annihilated
by a power of `f`, then the formal-functions theorem `0EKS`); here the map is built by
formal-étale lifting and a regular-pair Hartogs argument; see the module docstring. -/
@[stacks 0BLM "complete regular local case, for `f ∉ m²`"]
theorem hypersurfaceFiniteEtaleLifting_of_isAdicComplete
    (d : ℕ) (hd : 2 ≤ d) (hdim : ringKrullDim A = d + 1)
    (f : A) (hf : f ∈ maximalIdeal A) (hf2 : f ∉ maximalIdeal A ^ 2)
    [IsLocalRing (A ⧸ Ideal.span (Set.singleton f))]
    [IsNoetherianRing (A ⧸ Ideal.span (Set.singleton f))] :
    HypersurfaceFiniteEtaleLifting A f := by
  classical
  -- the base rings
  let I : Ideal A := Ideal.span (Set.singleton f)
  have hI : I = Ideal.span {f} := rfl
  haveI : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  haveI hA : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  haveI : HenselianLocalRing A := henselianLocalRing_of_isAdicComplete A
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top hf)
  haveI hA₀reg : IsRegularLocalRing (A ⧸ I) := isRegularLocalRing_quotient_minimalGenerator hf hf2
  haveI : IsDomain (A ⧸ I) := Pcf.Vendor.isDomain_of_isRegularLocalRing _
  haveI hA₀ : IsIntegrallyClosed (A ⧸ I) := isIntegrallyClosed_of_isRegularLocalRing _
  have hdim₀ : ringKrullDim (A ⧸ I) = d := ringKrullDim_quotient_minimalGenerator_eq hf hf2 d hdim
  have hdim₀' : 2 ≤ ringKrullDim (A ⧸ I) := by
    rw [hdim₀]
    exact_mod_cast hd
  have hdim1 : 1 ≤ ringKrullDim A := by
    rw [hdim]
    exact_mod_cast (by omega : 1 ≤ d + 1)
  intro V hV
  obtain ⟨Y₀, ⟨e₀⟩⟩ := hV
  -- Step 0: the finite normal algebra `B` of `V` (Tag 0BM9)
  obtain ⟨Bobj, ⟨eB⟩⟩ := puncturedCover_exists_finiteNormalPuncturedEtaleAlgebra (.of A) hdim1 V
  let B : Type u := Bobj.obj.unop
  letI : CommRing B := inferInstance
  letI : Algebra A B := inferInstance
  haveI : Module.Finite A B := inferInstance
  haveI : Module.IsTorsionFree A B := inferInstance
  have hBnormal : IsStacksNormalRing B := Bobj.isStacksNormalRing
  have hBetale : ∀ (q : Ideal B) [q.IsPrime], q.under A ≠ maximalIdeal A →
      Algebra.IsEtaleAt A q := fun q _ hq ↦
    Algebra.isEtaleAt_of_puncturedSpectrum_pullback_etale Bobj.property.2.2.2 q hq
  -- Step 1: the finite étale `A ⧸ I`-algebra `C₀` of `Y₀`, and its lift `C` (Tag 09ZL)
  let Cop : (CommAlgCat (A ⧸ I))ᵒᵖ :=
    (algΓ (.of (A ⧸ I))).obj ((FiniteEtaleCover.forget _).obj Y₀)
  let C₀ : Type u := Cop.unop
  letI : CommRing C₀ := inferInstance
  letI : Algebra (A ⧸ I) C₀ := inferInstance
  have hC₀ := finiteEtaleCover_sections_finite_etale (A ⧸ I) Y₀
  haveI : Module.Finite (A ⧸ I) C₀ := hC₀.1
  haveI : Algebra.Etale (A ⧸ I) C₀ := hC₀.2
  have hIle : I ≤ maximalIdeal A := by
    rw [hI]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hf)
  obtain ⟨C, _, _, hCfin, hCet, ⟨ψ⟩⟩ := exists_finite_etale_lift_of_henselianLocalRing hIle C₀
  haveI : Module.Finite A C := hCfin
  haveI : Algebra.Etale A C := hCet
  -- Step 2: the isomorphism over `U₀` as an isomorphism of pullbacks of affine schemes
  let ι₀ := (puncturedSpectrum (A ⧸ I)).ι
  let F₀ := FiniteEtaleCover.forget (puncturedSpectrumScheme (A ⧸ I))
  let unitY := (algΓAlgSpecAdjunction (.of (A ⧸ I))).unit.app ((FiniteEtaleCover.forget _).obj Y₀)
  haveI : IsIso unitY := finiteEtaleCover_algGamma_unit_isIso (A ⧸ I) Y₀
  let eY : F₀.obj ((restrictFiniteEtaleToPuncturedSpectrum (A ⧸ I)).obj Y₀) ≅
      Over.mk (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) C₀))) ι₀) :=
    (Over.pullback ι₀).mapIso (asIso unitY)
  let eV : F₀.obj ((restrictFiniteEtaleToPuncturedHypersurface A f).obj V) ≅
      Over.mk (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B))))
        ι₀) :=
    F₀.mapIso ((restrictFiniteEtaleToPuncturedHypersurface A f).mapIso eB.symm) ≪≫
      hypersurfacePullbackIso A f B
  let g := (eY.symm ≪≫ F₀.mapIso e₀ ≪≫ eV).hom
  haveI : IsIso g := inferInstance
  -- Step 3: the algebraic shadow of the isomorphism
  have hHartogs : Function.Bijective
      (((Scheme.ΓSpecIso (.of C₀)).inv ≫
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) C₀))) ι₀).appTop).hom) :=
    finiteEtaleAlgebra_pullbackSections_bijective (.of (A ⧸ I)) hdim₀' Cop
  obtain ⟨φ, hφinj, hφsurj⟩ := exists_algHom_of_pullback_iso (.of (A ⧸ I))
    (.of ((A ⧸ I) ⊗[A] B)) (.of C₀) g hHartogs
  -- Step 4: transport to `φ₀ : B → C / fC`
  letI : Algebra A C₀ := Algebra.compHom C₀ (algebraMap A (A ⧸ I))
  haveI : IsScalarTower A (A ⧸ I) C₀ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let eT : (A ⧸ I) ⊗[A] C ≃ₐ[A] C ⧸ Ideal.span {algebraMap A C f} :=
    (Algebra.TensorProduct.comm A (A ⧸ I) C).trans
      (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).restrictScalars A).symm.trans
        (Ideal.quotientEquivAlgOfEq A (by rw [hI, Ideal.map_span, Set.image_singleton])))
  let ψ' : C₀ ≃ₐ[A] C ⧸ Ideal.span {algebraMap A C f} := (ψ.restrictScalars A).symm.trans eT
  let eBq : (B ⧸ I.map (algebraMap A B)) ≃ₐ[A ⧸ I] (A ⧸ I) ⊗[A] B :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  have hBqmap : I.map (algebraMap A B) = Ideal.span {algebraMap A B f} := by
    rw [hI, Ideal.map_span, Set.image_singleton]
  let φ₀ : B →ₐ[A] C ⧸ Ideal.span {algebraMap A C f} :=
    ψ'.toAlgHom.comp ((φ.restrictScalars A).comp Algebra.TensorProduct.includeRight)
  have hφ₀ : ∀ b : B, φ₀ b = ψ' (φ (1 ⊗ₜ[A] b)) := fun _ ↦ rfl
  haveI : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hxbar : ∀ x ∈ maximalIdeal A, algebraMap A (A ⧸ I) x ∈ maximalIdeal (A ⧸ I) := by
    intro x hx
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal x).mp hx (isUnit_of_map_unit (Ideal.Quotient.mk I) x hu)
  have hφ₀inj : ∀ x ∈ maximalIdeal A, ∀ b : B, φ₀ b = 0 →
      ∃ k : ℕ, x ^ k • b ∈ Ideal.span {algebraMap A B f} := by
    intro x hx b hb
    rw [hφ₀] at hb
    have h1 : φ (1 ⊗ₜ[A] b) = 0 := ψ'.injective (by rw [hb, map_zero])
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (algebraMap A (A ⧸ I) x) ^ k • (1 ⊗ₜ[A] b : (A ⧸ I) ⊗[A] B) = 0 :=
      hφinj _ (hxbar x hx) _ h1
    have h2 : (algebraMap A (A ⧸ I) x) ^ k • (1 ⊗ₜ[A] b : (A ⧸ I) ⊗[A] B) =
        1 ⊗ₜ[A] (x ^ k • b) := by
      rw [← map_pow, algebraMap_smul, TensorProduct.tmul_smul]
    refine ⟨k, ?_⟩
    rw [← hBqmap, ← Ideal.Quotient.eq_zero_iff_mem]
    apply eBq.injective
    rw [map_zero]
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, ← h2, hk]
  have hφ₀surj : ∀ x ∈ maximalIdeal A, ∀ c : C ⧸ Ideal.span {algebraMap A C f},
      ∃ (k : ℕ) (b : B), x ^ k • c = φ₀ b := by
    intro x hx c
    obtain ⟨k, bt, hbt⟩ : ∃ (k : ℕ) (bt : (A ⧸ I) ⊗[A] B),
        (algebraMap A (A ⧸ I) x) ^ k • ψ'.symm c = φ bt :=
      hφsurj _ (hxbar x hx) (ψ'.symm c)
    obtain ⟨bq, hbq⟩ := eBq.surjective bt
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bq
    refine ⟨k, b, ?_⟩
    have h3 : (1 ⊗ₜ[A] b : (A ⧸ I) ⊗[A] B) = bt := by
      rw [← hbq]
      exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk B I b).symm
    rw [hφ₀, h3, ← hbt, ← map_pow, algebraMap_smul, map_smul, AlgEquiv.apply_symm_apply]
  -- Step 5: the core theorem
  have hBet : Algebra.Etale A B :=
    etale_of_hypersurface_lift A d hd hdim f hf hf2 B hBnormal hBetale C φ₀ hφ₀inj hφ₀surj
  -- Step 6: the finite étale cover `Spec B` extends `V`
  let p : Spec (.of B) ⟶ Spec (.of A) := ((algSpec (.of A)).obj Bobj.obj).hom
  have hpFinite : IsFinite p := Bobj.isFinite_algSpec
  have hpEtale : Etale p := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hBet)
  let Y : FiniteEtaleCover (Spec (.of A)) := MorphismProperty.Over.mk ⊤ p ⟨hpFinite, hpEtale⟩
  refine ⟨Y, ⟨?_ ≪≫ eB⟩⟩
  exact MorphismProperty.Comma.isoFromComma (Iso.refl _)

/-- The complete case of the outer induction step of Stacks Tag `0BMA`: for a complete regular
local ring of dimension `d + 1 ≥ 3`, punctured-spectrum purity follows from purity for the
regular hypersurfaces `A/(x)`, `x ∈ m \ m²`, with no further hypothesis.  This records that the
lifting theorem above has exactly the shape consumed by
`regularLocal_puncturedSpectrumPurity_induction_step`. -/
theorem regularLocal_puncturedSpectrumPurity_induction_step_of_isAdicComplete
    (d : ℕ) (hd : 2 ≤ d) (hdim : ringKrullDim A = d + 1)
    (hInduction :
      ∀ (x : A) (_hx : x ∈ maximalIdeal A) (_hx2 : x ∉ maximalIdeal A ^ 2)
        [IsRegularLocalRing (A ⧸ Ideal.span ({x} : Set A))],
        ringKrullDim (A ⧸ Ideal.span ({x} : Set A)) = d →
          PuncturedSpectrumPurity (A ⧸ Ideal.span ({x} : Set A))) :
    PuncturedSpectrumPurity A :=
  regularLocal_puncturedSpectrumPurity_induction_step A d hd hdim hInduction
    (fun x hx hx2 _ ↦ hypersurfaceFiniteEtaleLifting_of_isAdicComplete A d hd hdim x hx hx2)

end Main


#print axioms exists_isRegular_triple
#print axioms etale_localization_away_of_isEtaleAt
#print axioms localized_bijective_of_mod_isSMulRegular
#print axioms mem_span_of_scaleRoots_aeval_eq_zero_of_isStacksNormalRing
#print axioms exists_algHom_bijective_of_hypersurface_lift
#print axioms etale_of_hypersurface_lift
#print axioms exists_algHom_of_pullback_iso
#print axioms henselianLocalRing_of_isAdicComplete
#print axioms hypersurfacePullbackIso
#print axioms hypersurfaceFiniteEtaleLifting_of_isAdicComplete
#print axioms regularLocal_puncturedSpectrumPurity_induction_step_of_isAdicComplete

end Pcf.Stacks
