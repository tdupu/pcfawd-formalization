/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.TameRamification
public import Pcf.Stacks.Abhyankar.StrictHeightOneTransport
public import Pcf.Stacks.Abhyankar.StrictHenselizationDimension
public import Pcf.Stacks.Abhyankar.StrictNormalDecomposition
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Flat.Localization

/-!
# Tame ramification after strict henselization (Stacks Tag `0EYD`, affine form)

Paragraph 2 of the proof of Stacks Tag `0EYG` (Abhyankar's lemma for a regular divisor):

> By Lemma 58.31.1 [`0EYD`] the base change of `Y` to `Spec(A^{sh})` is tamely ramified in
> codimension 1.

This file proves the affine form of that sentence used by the tame proof of `0EYG` in pcf: if
`S` is a finite `R`-algebra which is tamely ramified in codimension one along `V(a)`
(`IsTamelyRamifiedInCodimensionOneAlong R S a`, Stacks `0BSE`/`09E9`), then every normal-domain
factor `N = (Rˢʰ ⊗_R S) ⧸ (1 - e)` of the base change to the strict henselization
`Rˢʰ = LocalColimit R Ω` is tamely ramified over `Rˢʰ` at every height-one prime containing `a`
(`PointedEtaleNeighborhood.isTamelyRamifiedAt_strictBaseChangeFactor`).

## Route (and divergence from Stacks)

Stacks proves `0EYD` through More on Algebra, Lemma 15.116.9: tameness of an extension of
discrete valuation rings is preserved by base change along an unramified extension of discrete
valuation rings.  Here the same conclusion is obtained by a direct comparison of ramification
indices along the ind-étale base change `S → Rˢʰ ⊗_R S`:

1. `isUnramifiedAt_residue_of_etale_cover`: if every finite set of an `S`-algebra `N` lies in
   the image of an étale `S`-algebra, then at every prime `q` of `N` the prime below generates
   the maximal ideal of `N_q` and the residue extension `κ(q)/κ(q ∩ S)` is separable.  (Each
   element comes from an étale stage, where Stacks `00UW` applies.)
2. `PointedEtaleNeighborhood.exists_etale_cover_strictBaseChange`: `Rˢʰ ⊗_R S` is covered in
   this sense by the étale `S`-algebras `S ⊗_R A_λ`, `A_λ` a pointed étale stage of `Rˢʰ`, and
   so is every factor `N = (Rˢʰ ⊗_R S) ⧸ (1 - e)`
   (`isTamelyRamifiedAt_quotient_idempotent_of_etale_cover`).
3. `Module.Flat S N` (`PointedEtaleNeighborhood.module_flat_strictBaseChange`), going down
   (Stacks `00HS`), and heights identify the primes below `q` as
   minimal primes over `a` in `R` and in `S`, so the tameness hypothesis on `S/R` applies at
   `q ∩ S`.
4. Mathlib's `Ideal.ramificationIdx_tower` (multiplicativity of ramification indices along a
   flat tower) with `e(q / q ∩ S) = 1` from step 1 gives `e(q / Rˢʰ) = e(q ∩ S / R)`, which is a
   unit in `κ(q ∩ R)` by tameness, hence in `κ(q ∩ Rˢʰ)`.
   The abstract statement is `isTamelyRamifiedAt_of_etale_cover_of_flat`.
5. Separability of `κ(q) / κ(q ∩ Rˢʰ)` follows from `κ(q)/κ(q ∩ S)` (step 1), `κ(q ∩ S)/κ(q ∩ R)`
   (tameness) and the tower `κ(q ∩ R) ⊂ κ(q ∩ Rˢʰ) ⊂ κ(q)`.
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section EtaleCover

variable {S N : Type u} [CommRing S] [CommRing N] [Algebra S N]

/-- Pulling a prime back along an `S`-algebra map does not change the prime of `S` below it. -/
theorem comap_algHom_under_eq {B : Type u} [CommRing B] [Algebra S B] (g : B →ₐ[S] N)
    (q : Ideal N) : (q.comap g.toRingHom).under S = q.under S := by
  ext s
  simp only [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]

/-- An étale `S`-algebra is unramified at every prime (Stacks `00UW`, pointwise form). -/
theorem isUnramifiedAt_comap_of_etale {B : Type u} [CommRing B] [Algebra S B] [Algebra.Etale S B]
    (g : B →ₐ[S] N) (q : Ideal N) [q.IsPrime] :
    Algebra.IsUnramifiedAt S (q.comap g.toRingHom) := by
  haveI : Algebra.FormallyUnramified S B := inferInstance
  haveI : Algebra.FormallyUnramified B (Localization.AtPrime (q.comap g.toRingHom)) :=
    Algebra.FormallyUnramified.of_isLocalization (q.comap g.toRingHom).primeCompl
  exact Algebra.FormallyUnramified.comp S B _

/-- **Residue transport along an étale stage, uniformizer clause.**  Let `B` be an étale
`S`-algebra, `g : B → N` an `S`-algebra map and `q` a prime of `N`.  An element of `q` in the
image of `g` lies in `(q ∩ S) N_q`: at `Q = g⁻¹(q)` the étale algebra `B` satisfies
`(q ∩ S) B_Q = Q B_Q` (Stacks `00UW`), and this relation is pushed forward along `g`. -/
theorem algebraMap_mem_map_under_of_etale {B : Type u} [CommRing B] [Algebra S B]
    [Algebra.Etale S B] (g : B →ₐ[S] N) (q : Ideal N) [q.IsPrime] (b : B) (hb : g b ∈ q) :
    algebraMap N (Localization.AtPrime q) (g b) ∈
      (q.under S).map (algebraMap S (Localization.AtPrime q)) := by
  set Q := q.comap g.toRingHom with hQdef
  haveI : Q.IsPrime := Ideal.IsPrime.comap _
  have hQS : Q.under S = q.under S := comap_algHom_under_eq g q
  haveI : Q.LiesOver (q.under S) := ⟨hQS.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver (q.under S) Q
  have hunr : Algebra.IsUnramifiedAt S Q := isUnramifiedAt_comap_of_etale g q
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq S (q.under S) Q).mp hunr).2
  have hbQ : b ∈ Q := hb
  have hb' : algebraMap B (Localization.AtPrime Q) b ∈
      ((q.under S).map (algebraMap S B)).map (algebraMap B (Localization.AtPrime Q)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, hmap,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hbQ
  rw [IsLocalization.mem_map_algebraMap_iff Q.primeCompl] at hb'
  obtain ⟨⟨⟨y, hy⟩, u⟩, huy⟩ := hb'
  simp only at huy
  rw [← map_mul] at huy
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists Q.primeCompl (Localization.AtPrime Q)).mp huy
  -- `c * (b * u) = c * y` in `B`, with `u * c ∉ Q`
  have huc : g ((u : B) * c) ∉ q := by
    have : (u : B) * c ∈ Q.primeCompl := Q.primeCompl.mul_mem u.2 c.2
    exact this
  have hunit : IsUnit (algebraMap N (Localization.AtPrime q) (g ((u : B) * c))) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).mpr huc
  have hyc : g (y * c) ∈ (q.under S).map (algebraMap S N) := by
    have h1 : y * c ∈ (q.under S).map (algebraMap S B) := Ideal.mul_mem_right _ _ hy
    have hle : ((q.under S).map (algebraMap S B)).map g.toRingHom ≤
        (q.under S).map (algebraMap S N) := by
      rw [Ideal.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
    exact hle (Ideal.mem_map_of_mem _ h1)
  rw [← Ideal.mul_unit_mem_iff_mem _ hunit, ← map_mul, ← map_mul]
  have heq : b * ((u : B) * c) = y * c := by
    calc b * ((u : B) * c) = c * (b * u) := by ring
      _ = c * y := hc
      _ = y * c := by ring
  rw [heq, IsScalarTower.algebraMap_eq S N (Localization.AtPrime q), ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hyc

/-- The residue-field map `κ(g⁻¹ q) → κ(q)` induced by an `S`-algebra map `g : B → N`, as a
`κ(q ∩ S)`-algebra homomorphism. -/
noncomputable def residueFieldMapₐOfLiesOver {B : Type u} [CommRing B] [Algebra S B]
    (g : B →ₐ[S] N) (q : Ideal N) [q.IsPrime] :
    letI : (q.comap g.toRingHom).IsPrime := Ideal.IsPrime.comap _
    letI : (q.comap g.toRingHom).LiesOver (q.under S) := ⟨(comap_algHom_under_eq g q).symm⟩
    letI := Localization.AtPrime.algebraOfLiesOver (q.under S) (q.comap g.toRingHom)
    letI := Localization.AtPrime.algebraOfLiesOver (q.under S) q
    (q.comap g.toRingHom).ResidueField →ₐ[(q.under S).ResidueField] q.ResidueField :=
  letI : (q.comap g.toRingHom).IsPrime := Ideal.IsPrime.comap _
  letI : (q.comap g.toRingHom).LiesOver (q.under S) := ⟨(comap_algHom_under_eq g q).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver (q.under S) (q.comap g.toRingHom)
  letI := Localization.AtPrime.algebraOfLiesOver (q.under S) q
  { Ideal.ResidueField.map (q.comap g.toRingHom) q g.toRingHom rfl with
    commutes' := fun x ↦ by
      obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective x
      change Ideal.ResidueField.map (q.comap g.toRingHom) q g.toRingHom rfl
        (algebraMap _ _ (residue _ z)) = algebraMap _ _ (residue _ z)
      rw [IsLocalRing.ResidueField.algebraMap_residue, IsLocalRing.ResidueField.algebraMap_residue,
        Ideal.ResidueField.map, IsLocalRing.ResidueField.map_residue,
        RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      congr 1
      rw [← RingHom.comp_apply]
      exact (RingHom.congr_fun (Localization.localRingHom_unique _ _ _ _ fun r ↦ by
        rw [RingHom.comp_apply, Localization.localRingHom_to_map,
          Localization.localRingHom_to_map]
        exact congrArg _ (g.commutes r)) z).symm }

theorem residueFieldMapₐOfLiesOver_apply {B : Type u} [CommRing B] [Algebra S B]
    (g : B →ₐ[S] N) (q : Ideal N) [q.IsPrime] (x) :
    letI : (q.comap g.toRingHom).IsPrime := Ideal.IsPrime.comap _
    residueFieldMapₐOfLiesOver g q x =
      Ideal.ResidueField.map (q.comap g.toRingHom) q g.toRingHom rfl x := rfl

/-- **Residue transport along étale stages (Stacks `00UW` for an ind-étale algebra).**
Let `N` be an `S`-algebra such that every finite set of `N` lies in the image of some étale
`S`-algebra `B → N`.  Then at every prime `q` of `N` the prime `q ∩ S` generates the maximal
ideal of `N_q`, and the residue extension `κ(q)/κ(q ∩ S)` is separable.

Both clauses are checked elementwise on an étale stage `B`, where they hold by
`Algebra.isUnramifiedAt_iff_map_eq`, and are transported along `B → N` (first clause) and along
the induced `κ(q ∩ S)`-embedding `κ(g⁻¹ q) → κ(q)` of residue fields (second clause). -/
theorem isUnramifiedAt_residue_of_etale_cover
    (hcover : ∀ s : Finset N, ∃ (B : Type u) (_ : CommRing B) (_ : Algebra S B)
      (_ : Algebra.Etale S B) (g : B →ₐ[S] N), ∀ x ∈ s, x ∈ Set.range g)
    (q : Ideal N) [q.IsPrime] :
    (q.under S).map (algebraMap S (Localization.AtPrime q)) =
        maximalIdeal (Localization.AtPrime q) ∧
      (letI := Localization.AtPrime.algebraOfLiesOver (q.under S) q;
        Algebra.IsSeparable (q.under S).ResidueField q.ResidueField) := by
  classical
  letI := Localization.AtPrime.algebraOfLiesOver (q.under S) q
  constructor
  · apply le_antisymm
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, IsScalarTower.algebraMap_eq S N
        (Localization.AtPrime q), ← Ideal.map_map]
      apply Ideal.map_mono
      rw [Ideal.map_le_iff_le_comap]
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap]
      obtain ⟨B, _, _, _, g, hg⟩ := hcover {t}
      obtain ⟨b, rfl⟩ := hg t (Finset.mem_singleton_self t)
      exact algebraMap_mem_map_under_of_etale g q b ht
  · refine ⟨fun x ↦ ?_⟩
    -- write `x = f(t) / f(s)` with `t s : N`, `s ∉ q`, `f : N → κ(q)`
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨⟨t, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨B, _, _, _, g, hg⟩ := hcover {t, (s : N)}
    obtain ⟨bt, hbt⟩ := hg t (by simp)
    obtain ⟨bs, hbs⟩ := hg (s : N) (by simp)
    set Q := q.comap g.toRingHom with hQdef
    haveI : Q.IsPrime := Ideal.IsPrime.comap _
    have hQS : Q.under S = q.under S := comap_algHom_under_eq g q
    haveI : Q.LiesOver (q.under S) := ⟨hQS.symm⟩
    letI := Localization.AtPrime.algebraOfLiesOver (q.under S) Q
    haveI : Algebra.IsUnramifiedAt S Q := isUnramifiedAt_comap_of_etale g q
    haveI : Algebra.IsSeparable (q.under S).ResidueField Q.ResidueField := inferInstance
    let ψ := residueFieldMapₐOfLiesOver g q
    have hψ : ∀ b : B, ψ (algebraMap B Q.ResidueField b) = algebraMap N q.ResidueField (g b) :=
      fun b ↦ Ideal.ResidueField.map_algebraMap Q q g.toRingHom rfl b
    have hs0 : algebraMap B Q.ResidueField bs ≠ 0 := by
      rw [Ne, Ideal.algebraMap_residueField_eq_zero]
      intro h
      apply s.2
      change (s : N) ∈ q
      rw [← hbs]
      exact h
    let y : Q.ResidueField := algebraMap B Q.ResidueField bt / algebraMap B Q.ResidueField bs
    have hy : ψ y = residue (Localization.AtPrime q) (IsLocalization.mk' _ t s) := by
      rw [map_div₀, hψ, hψ, hbt, hbs]
      have hs' : algebraMap N q.ResidueField (s : N) ≠ 0 := by
        rw [Ne, Ideal.algebraMap_residueField_eq_zero]
        exact s.2
      rw [div_eq_iff hs',
        IsScalarTower.algebraMap_apply N (Localization.AtPrime q) q.ResidueField t,
        IsScalarTower.algebraMap_apply N (Localization.AtPrime q) q.ResidueField (s : N),
        IsLocalRing.ResidueField.algebraMap_eq, ← map_mul, IsLocalization.mk'_spec]
    rw [← hy]
    exact IsSeparable.map ψ ψ.injective (Algebra.IsSeparable.isSeparable _ y)

end EtaleCover

namespace PointedEtaleNeighborhood

section StrictBaseChange

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- The map `S ⊗_R A_λ → Rˢʰ ⊗_R S` from the base change of a pointed étale stage `A_λ` of the
strict henselization, as a map of `S`-algebras (`S` acting on the right factor of the target). -/
noncomputable def stageToStrictBaseChange (S : Type u) [CommRing S] [Algebra R S]
    (X : PointedEtaleNeighborhood R Ω) :
    letI : Algebra S (LocalColimit R Ω ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    S ⊗[R] X →ₐ[S] LocalColimit R Ω ⊗[R] S :=
  letI : Algebra S (LocalColimit R Ω ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  { ((Algebra.TensorProduct.comm R S (LocalColimit R Ω)).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R S) (toLocalColimitAlgHom X))).toRingHom with
    commutes' := fun s ↦ by
      change Algebra.TensorProduct.comm R S _
        (Algebra.TensorProduct.map (AlgHom.id R S) (toLocalColimitAlgHom X) (s ⊗ₜ 1)) = 1 ⊗ₜ s
      rw [Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.comm_tmul]
      rfl }

theorem stageToStrictBaseChange_tmul (S : Type u) [CommRing S] [Algebra R S]
    (X : PointedEtaleNeighborhood R Ω) (s : S) (x : X) :
    stageToStrictBaseChange S X (s ⊗ₜ x) = toLocalColimitAlgHom X x ⊗ₜ s := rfl

/-- Every finite subset of `Rˢʰ ⊗_R S` lies in the image of `S ⊗_R A_λ` for one pointed étale
stage `A_λ` (`Rˢʰ ⊗_R S` is the filtered colimit of the étale `S`-algebras `S ⊗_R A_λ`). -/
theorem exists_stage_strictBaseChange (S : Type u) [CommRing S] [Algebra R S]
    (s : Finset (LocalColimit R Ω ⊗[R] S)) :
    ∃ X : PointedEtaleNeighborhood R Ω, ∀ x ∈ s, x ∈ Set.range (stageToStrictBaseChange S X) := by
  classical
  choose k m n hmn using fun x : LocalColimit R Ω ⊗[R] S ↦ TensorProduct.exists_sum_tmul_eq x
  let C : Set (LocalColimit R Ω) := ⋃ x : s, Set.range (m x)
  have hC : C.Finite := Set.finite_iUnion fun _ ↦ Set.finite_range _
  obtain ⟨X, hX⟩ := exists_stage_containing_finite_localColimit_set (R := R) (Ω := Ω) C hC
  refine ⟨X, fun x hx ↦ ?_⟩
  choose pre hpre using fun j : Fin (k x) ↦
    hX (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Set.mem_range_self j⟩)
  refine ⟨∑ j, n x j ⊗ₜ pre j, ?_⟩
  rw [map_sum]
  conv_rhs => rw [hmn x]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [stageToStrictBaseChange_tmul, hpre]

/-- **`Rˢʰ ⊗_R S` is ind-étale over `S`.**  Every finite subset of `Rˢʰ ⊗_R S` lies in the image
of an étale `S`-algebra, namely `S ⊗_R A_λ` for a pointed étale stage `A_λ` of `Rˢʰ`. -/
theorem exists_etale_cover_strictBaseChange (S : Type u) [CommRing S] [Algebra R S] :
    letI : Algebra S (LocalColimit R Ω ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    ∀ t : Finset (LocalColimit R Ω ⊗[R] S),
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra S B) (_ : Algebra.Etale S B)
        (g : B →ₐ[S] LocalColimit R Ω ⊗[R] S), ∀ x ∈ t, x ∈ Set.range g := by
  letI : Algebra S (LocalColimit R Ω ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  intro t
  obtain ⟨X, hX⟩ := exists_stage_strictBaseChange S t
  exact ⟨S ⊗[R] X, inferInstance, inferInstance, inferInstance,
    stageToStrictBaseChange S X, hX⟩

/-- `Rˢʰ ⊗_R S` is flat over `S` (base change of the flat `R → Rˢʰ`). -/
theorem module_flat_strictBaseChange (S : Type u) [CommRing S] [Algebra R S] :
    letI : Algebra S (LocalColimit R Ω ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    Module.Flat S (LocalColimit R Ω ⊗[R] S) := by
  letI : Algebra S (LocalColimit R Ω ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Flat R (LocalColimit R Ω) := localColimit_flat (R := R) (Ω := Ω)
  let φ : LocalColimit R Ω ⊗[R] S ≃ₗ[S] S ⊗[R] LocalColimit R Ω :=
    { (Algebra.TensorProduct.comm R (LocalColimit R Ω) S).toLinearEquiv with
      map_smul' := fun s x ↦ by
        change Algebra.TensorProduct.comm R (LocalColimit R Ω) S (s • x) =
          s • Algebra.TensorProduct.comm R (LocalColimit R Ω) S x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1 }
  exact Module.Flat.of_linearEquiv φ

end StrictBaseChange

end PointedEtaleNeighborhood

section Main

/-- A prime of height one in a domain contains no strictly smaller nonzero prime. -/
theorem eq_of_le_of_height_eq_one {D : Type*} [CommRing D] [IsDomain D] {Q P : Ideal D}
    [Q.IsPrime] [P.IsPrime] (hP : P.height = 1) (hQ : Q ≠ ⊥) (hle : Q ≤ P) : Q = P := by
  by_contra hne
  have h := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hP] at h
  have h0 : Q.height = 0 := by
    have hQfin : Q.height ≠ ⊤ := by
      intro htop
      rw [htop] at h
      exact absurd h (by simp)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hQfin
    rw [← hn] at h ⊢
    have : n + 1 ≤ 1 := by exact_mod_cast h
    have : n = 0 := by omega
    simp [this]
  exact hQ (Ideal.height_eq_zero_iff_eq_bot.mp h0)

variable {R S A N : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing N]
  [Algebra R S] [Algebra R A] [Algebra R N] [Algebra S N] [Algebra A N]
  [IsScalarTower R S N] [IsScalarTower R A N]

/-- **Tame ramification along an ind-étale, flat base change (abstract form of Stacks `0EYD`
used in the proof of `0EYG`).**

Let `S` be an `R`-algebra tamely ramified in codimension one along `V(a)`.  Let `A` be a
Noetherian local `R`-algebra, flat over `R`, in which `a` is a nonzerodivisor of the maximal ideal
with `A ⧸ (a)` regular local, and let `N` be a domain, finite and faithful over `A`, receiving
compatible maps from `S` and `A`, flat over `S`, and *ind-étale* over `S` in the sense that every
finite subset of `N` lies in the image of an étale `S`-algebra.  Then `N` is tamely ramified over
`A` (Stacks `09E9`) at every height-one prime `q` containing `a`.

Proof: `q ∩ A = (a)` (`under_eq_of_height_eq_one_of_mem`); going down along `R → A` and `S → N`
makes `q ∩ R` and `q ∩ S` minimal over `a`, so the hypothesis applies at `q ∩ S`; then
`e(q/A) = e(q/R) = e(q ∩ S/R) · e(q/S) = e(q ∩ S/R)` (`Ideal.ramificationIdx_tower`, and
`e(q/S) = 1` by `isUnramifiedAt_residue_of_etale_cover`), and
`κ(q ∩ R) ⊂ κ(q ∩ S) ⊂ κ(q)` is separable, hence so is `κ(q)/κ(q ∩ A)`. -/
theorem isTamelyRamifiedAt_of_etale_cover_of_flat
    [IsLocalRing A] [IsNoetherianRing A] [Module.Flat R A] [Module.Flat S N]
    (a : R) (htame : IsTamelyRamifiedInCodimensionOneAlong R S a)
    (ha : algebraMap R A a ∈ maximalIdeal A) (ha0 : algebraMap R A a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({algebraMap R A a} : Set A))]
    [IsDomain N] [Module.Finite A N] [FaithfulSMul A N]
    (hcover : ∀ s : Finset N, ∃ (B : Type u) (_ : CommRing B) (_ : Algebra S B)
      (_ : Algebra.Etale S B) (g : B →ₐ[S] N), ∀ x ∈ s, x ∈ Set.range g)
    (q : PrimeSpectrum N) (hq : q.asIdeal.height = 1)
    (hqa : algebraMap A N (algebraMap R A a) ∈ q.asIdeal) :
    IsTamelyRamifiedAt A N q := by
  classical
  let P : Ideal N := q.asIdeal
  let aA : A := algebraMap R A a
  -- the base `A`
  haveI : IsRegularLocalRing A := Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor aA ha ha0
  haveI : IsDomain A := isDomain_of_isRegularLocalRing A
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  haveI : IsNoetherianRing N := IsNoetherianRing.of_finite A N
  have haA0 : aA ≠ 0 := nonZeroDivisors.ne_zero ha0
  haveI hprime : (Ideal.span ({aA} : Set A)).IsPrime := divisorPrime_isPrime aA
  have hheight : (Ideal.span ({aA} : Set A)).height = 1 :=
    divisorPrime_height_eq_one aA ha haA0
  have haN0 : algebraMap A N aA ≠ 0 := fun h ↦
    haA0 (FaithfulSMul.algebraMap_injective A N (by rw [h, map_zero]))
  -- (F1) the prime of `A` below `P` is `(a)`
  have hpA : P.under A = Ideal.span {aA} := by
    apply under_eq_of_height_eq_one_of_mem _ hheight P hq
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hqa
  -- the primes below `P`
  let q₀ : Ideal S := P.under S
  let p₀ : Ideal R := q₀.under R
  have hp₀ : p₀ = P.under R := Ideal.under_under P
  have hp₀A : p₀ = (P.under A).under R := by rw [hp₀, Ideal.under_under]
  have hap₀ : a ∈ p₀ := by
    rw [hp₀A, hpA, Ideal.mem_under]
    exact Ideal.subset_span rfl
  -- (F2) `p₀` is minimal over `a` (going down along the flat `R → A`)
  have hmin₀ : p₀ ∈ (Ideal.span ({a} : Set R)).minimalPrimes := by
    refine ⟨⟨inferInstance, by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hap₀⟩,
      fun p' ⟨hp', hap'⟩ hle ↦ ?_⟩
    haveI := hp'
    haveI : (Ideal.span ({aA} : Set A)).LiesOver p₀ := ⟨by rw [hp₀A, hpA]⟩
    obtain ⟨P', hP'le, hP', hP'over⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le (Ideal.span ({aA} : Set A)) hle
    have hP'eq : P' = Ideal.span {aA} := by
      apply le_antisymm hP'le
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have : a ∈ P'.under R := by
        rw [← hP'over.over]
        exact hap' (Ideal.subset_span rfl)
      exact this
    have : p' = p₀ := by
      rw [hP'over.over, hP'eq, hp₀A, hpA]
    exact this.symm.le
  -- (F3) `q₀` is minimal over `a S` (going down along the flat `S → N`)
  have haq₀ : algebraMap R S a ∈ q₀ := by
    change algebraMap S N (algebraMap R S a) ∈ P
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A N]
    exact hqa
  have hmin₁ : q₀ ∈ ((Ideal.span ({a} : Set R)).map (algebraMap R S)).minimalPrimes := by
    rw [Ideal.map_span, Set.image_singleton]
    refine ⟨⟨inferInstance, by rw [Ideal.span_le, Set.singleton_subset_iff]; exact haq₀⟩,
      fun q' ⟨hq', haq'⟩ hle ↦ ?_⟩
    haveI := hq'
    obtain ⟨Q', hQ'le, hQ', hQ'over⟩ := Ideal.exists_ideal_le_liesOver_of_le P hle
    have haQ' : algebraMap A N aA ∈ Q' := by
      have : algebraMap R S a ∈ Q'.under S := by
        rw [← hQ'over.over]
        exact haq' (Ideal.subset_span rfl)
      rw [Ideal.mem_under, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R A N] at this
      exact this
    have hQ'ne : Q' ≠ ⊥ := fun h ↦ haN0 (by rw [h] at haQ'; exact haQ')
    have hQ'eq : Q' = P := eq_of_le_of_height_eq_one hq hQ'ne hQ'le
    have : q' = q₀ := by rw [hQ'over.over, hQ'eq]
    exact this.symm.le
  -- (Step 3) tameness of `S` over `R` at `q₀`
  have ht := htame ⟨q₀, inferInstance⟩ hmin₀ hmin₁
  dsimp only [IsTamelyRamifiedAt] at ht
  obtain ⟨hunit, hsep⟩ := ht
  -- (Step 4) ramification indices
  have hcov := isUnramifiedAt_residue_of_etale_cover hcover P
  have hS : P.ramificationIdx S = 1 := by
    rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
      Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
      IsLocalRing.isMaximal_iff]
    exact hcov.1
  have htower : P.ramificationIdx R = q₀.ramificationIdx R * P.ramificationIdx S :=
    Ideal.ramificationIdx_tower q₀ P
  have hmap : (P.under A).map (algebraMap A (Localization.AtPrime P)) =
      (P.under R).map (algebraMap R (Localization.AtPrime P)) := by
    rw [hpA]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        Ideal.mem_comap, ← IsScalarTower.algebraMap_apply R A (Localization.AtPrime P)]
      exact Ideal.mem_map_of_mem _ (hp₀ ▸ hap₀)
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      have hrA : algebraMap R A r ∈ Ideal.span {aA} := by
        rw [← hpA, Ideal.mem_under, ← IsScalarTower.algebraMap_apply]
        exact hr
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R A (Localization.AtPrime P)]
      exact Ideal.mem_map_of_mem (algebraMap A (Localization.AtPrime P)) hrA
  have hAR : P.ramificationIdx A = P.ramificationIdx R := by
    rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def, hmap]
  have he : P.ramificationIdx A = q₀.ramificationIdx R := by
    rw [hAR, htower, hS, mul_one]
  -- (Step 5) the unit clause
  have hunitA : IsUnit ((P.ramificationIdx A : ℕ) : (P.under A).ResidueField) := by
    rw [he]
    have hnot : ((q₀.ramificationIdx R : ℕ) : R) ∉ p₀ := by
      intro hmem
      have h0 : algebraMap R p₀.ResidueField ((q₀.ramificationIdx R : ℕ) : R) = 0 :=
        Ideal.algebraMap_residueField_eq_zero.mpr hmem
      rw [map_natCast] at h0
      exact hunit.ne_zero h0
    apply isUnit_iff_ne_zero.mpr
    rw [← map_natCast (algebraMap A (P.under A).ResidueField), Ne,
      Ideal.algebraMap_residueField_eq_zero]
    intro hmem
    apply hnot
    rw [hp₀A, Ideal.mem_under, map_natCast]
    exact hmem
  -- (Step 6) the separability clause
  let pA : Ideal A := P.under A
  haveI : pA.LiesOver p₀ := ⟨hp₀A⟩
  letI := Localization.AtPrime.algebraOfLiesOver p₀ P
  letI := Localization.AtPrime.algebraOfLiesOver p₀ pA
  letI := Localization.AtPrime.algebraOfLiesOver p₀ q₀
  letI := Localization.AtPrime.algebraOfLiesOver q₀ P
  letI := Localization.AtPrime.algebraOfLiesOver pA P
  haveI : IsScalarTower (Localization.AtPrime p₀) (Localization.AtPrime q₀)
      (Localization.AtPrime P) := IsScalarTower.of_algebraMap_eq' (by
    rw [Localization.AtPrime.algebraMap_eq p₀ P, Localization.AtPrime.algebraMap_eq q₀ P,
      Localization.AtPrime.algebraMap_eq p₀ q₀]
    exact Localization.localRingHom_unique _ _ _ _ fun x ↦ by
      rw [RingHom.comp_apply, Localization.localRingHom_to_map, Localization.localRingHom_to_map,
        ← IsScalarTower.algebraMap_apply R S N])
  haveI : IsScalarTower (Localization.AtPrime p₀) (Localization.AtPrime pA)
      (Localization.AtPrime P) := IsScalarTower.of_algebraMap_eq' (by
    rw [Localization.AtPrime.algebraMap_eq p₀ P, Localization.AtPrime.algebraMap_eq pA P,
      Localization.AtPrime.algebraMap_eq p₀ pA]
    exact Localization.localRingHom_unique _ _ _ _ fun x ↦ by
      rw [RingHom.comp_apply, Localization.localRingHom_to_map, Localization.localRingHom_to_map,
        ← IsScalarTower.algebraMap_apply R A N])
  haveI := hsep
  haveI : Algebra.IsSeparable q₀.ResidueField P.ResidueField := hcov.2
  haveI : Algebra.IsSeparable p₀.ResidueField P.ResidueField :=
    Algebra.IsSeparable.trans p₀.ResidueField q₀.ResidueField P.ResidueField
  exact ⟨hunitA, Algebra.isSeparable_tower_top_of_isSeparable p₀.ResidueField pA.ResidueField
    P.ResidueField⟩

/-- **Factors by an idempotent.**  If `T` is flat over `S` and every finite subset of `T` lies in
the image of an étale `S`-algebra, the same holds for every factor `N = T ⧸ (1 - e)` cut out by an
idempotent `e` (`N = T[1/e]` is a localization of `T`); hence
`isTamelyRamifiedAt_of_etale_cover_of_flat` applies to `N`.  This is the form in which the tame
`0EYD` input enters the per-component analysis of `0EYG`. -/
theorem isTamelyRamifiedAt_quotient_idempotent_of_etale_cover
    {T : Type u} [CommRing T] [Algebra R T] [Algebra S T] [Algebra A T]
    [IsScalarTower R S T] [IsScalarTower R A T]
    [IsLocalRing A] [IsNoetherianRing A] [Module.Flat R A] [Module.Flat S T]
    (a : R) (htame : IsTamelyRamifiedInCodimensionOneAlong R S a)
    (ha : algebraMap R A a ∈ maximalIdeal A) (ha0 : algebraMap R A a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({algebraMap R A a} : Set A))]
    (hcover : ∀ s : Finset T, ∃ (B : Type u) (_ : CommRing B) (_ : Algebra S B)
      (_ : Algebra.Etale S B) (g : B →ₐ[S] T), ∀ x ∈ s, x ∈ Set.range g)
    (e : T) (he : IsIdempotentElem e)
    [IsDomain (T ⧸ Ideal.span {1 - e})] [Module.Finite A (T ⧸ Ideal.span {1 - e})]
    [FaithfulSMul A (T ⧸ Ideal.span {1 - e})]
    (q : PrimeSpectrum (T ⧸ Ideal.span {1 - e})) (hq : q.asIdeal.height = 1)
    (hqa : algebraMap A (T ⧸ Ideal.span {1 - e}) (algebraMap R A a) ∈ q.asIdeal) :
    IsTamelyRamifiedAt A (T ⧸ Ideal.span {1 - e}) q := by
  classical
  haveI : IsLocalization.Away e (T ⧸ Ideal.span {1 - e}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  haveI : Module.Flat T (T ⧸ Ideal.span {1 - e}) := IsLocalization.flat _ (Submonoid.powers e)
  haveI : Module.Flat S (T ⧸ Ideal.span {1 - e}) := Module.Flat.trans S T _
  refine isTamelyRamifiedAt_of_etale_cover_of_flat a htame ha ha0 (fun t ↦ ?_) q hq hqa
  choose lift hlift using fun x : T ⧸ Ideal.span {1 - e} ↦ Ideal.Quotient.mk_surjective x
  obtain ⟨B, _, _, _, g, hg⟩ := hcover (t.image lift)
  refine ⟨B, inferInstance, inferInstance, inferInstance,
    (Ideal.Quotient.mkₐ S _).comp g, fun x hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := hg (lift x) (Finset.mem_image_of_mem lift hx)
  exact ⟨y, by rw [AlgHom.comp_apply, hy, Ideal.Quotient.mkₐ_eq_mk, hlift]⟩

/-- **Tame ramification survives the base change to the strict henselization (Stacks `0EYD`,
affine form used in paragraph 2 of the proof of `0EYG`).**

Let `R` be Noetherian, `S` a finite `R`-algebra tamely ramified in codimension one along `V(a)`
(`IsTamelyRamifiedInCodimensionOneAlong R S a`), and `Rˢʰ = LocalColimit R Ω` a Noetherian strict
henselization in which `a` is a nonzerodivisor of the maximal ideal with `Rˢʰ ⧸ (a)` regular local.
Let `N = (Rˢʰ ⊗_R S) ⧸ (1 - e)` be a domain factor, finite and faithful over `Rˢʰ`.  Then `N` is
tamely ramified over `Rˢʰ` (Stacks `09E9`: ramification index invertible in the residue field,
separable residue extension) at every height-one prime `q` containing `a`.

The hypotheses `hq`, `hqa` are written with the ring of `Ideal.height` given explicitly and with
`Ideal.Quotient.mk` in place of `algebraMap Rˢʰ N`: both are definitionally the expected
statements, and this form avoids an expensive instance unification for the quotient of
`Rˢʰ ⊗_R S`.

**Divergence from Stacks.**  Stacks deduces `0EYD` from More on Algebra, Lemma 15.116.9 (tame
extensions of discrete valuation rings stay tame after an unramified base change).  Here the
ramification indices are compared directly (`isTamelyRamifiedAt_of_etale_cover_of_flat`):
`Rˢʰ ⊗_R S` is flat over `S`, so Mathlib's `Ideal.ramificationIdx_tower` gives
`e(q/R) = e(q ∩ S/R) · e(q/S)`; every element of `N` comes from an étale `S`-algebra `S ⊗_R A_λ`
(`exists_etale_cover_strictBaseChange`), so `e(q/S) = 1` and `κ(q)/κ(q ∩ S)` is separable
(`isUnramifiedAt_residue_of_etale_cover`); and `q ∩ Rˢʰ = (a)` is generated by the image of
`q ∩ R`, so `e(q/Rˢʰ) = e(q/R)`.  Going down along the flat maps `R → Rˢʰ` and `S → N` shows that
`q ∩ R` and `q ∩ S` are minimal over `a`, which is where the tameness hypothesis applies.
`[Module.Finite R S]` and `[IsNoetherianRing R]` are not used by the proof but are kept to match
the setting of `0EYG`. -/
@[stacks 0EYD "affine form: a domain factor of the base change to the strict henselization, at \
  the height-one primes over a regular divisor"]
theorem PointedEtaleNeighborhood.isTamelyRamifiedAt_strictBaseChangeFactor
    {R Ω S : Type u} [CommRing R] [Field Ω] [CommRing S] [Algebra R Ω] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (a : R)
    (htame : IsTamelyRamifiedInCodimensionOneAlong R S a)
    [IsNoetherianRing (LocalColimit R Ω)]
    (ha : algebraMap R (LocalColimit R Ω) a ∈ IsLocalRing.maximalIdeal (LocalColimit R Ω))
    (ha0 : algebraMap R (LocalColimit R Ω) a ∈ nonZeroDivisors (LocalColimit R Ω))
    [IsRegularLocalRing (LocalColimit R Ω ⧸
      Ideal.span ({algebraMap R (LocalColimit R Ω) a} : Set (LocalColimit R Ω)))]
    (e : LocalColimit R Ω ⊗[R] S) (he : IsIdempotentElem e)
    [IsDomain (LocalColimit R Ω ⊗[R] S ⧸ Ideal.span {1 - e})]
    [Module.Finite (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] S ⧸ Ideal.span {1 - e})]
    [FaithfulSMul (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] S ⧸ Ideal.span {1 - e})]
    (q : PrimeSpectrum (LocalColimit R Ω ⊗[R] S ⧸ Ideal.span {1 - e}))
    (hq : Ideal.height (R := LocalColimit R Ω ⊗[R] S ⧸ Ideal.span {1 - e}) q.asIdeal = 1)
    (hqa : Ideal.Quotient.mk _ (algebraMap (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] S)
      (algebraMap R (LocalColimit R Ω) a)) ∈ q.asIdeal) :
    IsTamelyRamifiedAt (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] S ⧸ Ideal.span {1 - e}) q := by
  letI : Algebra S (LocalColimit R Ω ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Flat R (LocalColimit R Ω) := localColimit_flat (R := R) (Ω := Ω)
  haveI : Module.Flat S (LocalColimit R Ω ⊗[R] S) :=
    PointedEtaleNeighborhood.module_flat_strictBaseChange S
  exact isTamelyRamifiedAt_quotient_idempotent_of_etale_cover a htame ha ha0
    (PointedEtaleNeighborhood.exists_etale_cover_strictBaseChange S) e he q hq hqa

end Main

#print axioms comap_algHom_under_eq
#print axioms isUnramifiedAt_comap_of_etale
#print axioms algebraMap_mem_map_under_of_etale
#print axioms residueFieldMapₐOfLiesOver
#print axioms residueFieldMapₐOfLiesOver_apply
#print axioms isUnramifiedAt_residue_of_etale_cover
#print axioms PointedEtaleNeighborhood.stageToStrictBaseChange
#print axioms PointedEtaleNeighborhood.stageToStrictBaseChange_tmul
#print axioms PointedEtaleNeighborhood.exists_stage_strictBaseChange
#print axioms PointedEtaleNeighborhood.exists_etale_cover_strictBaseChange
#print axioms PointedEtaleNeighborhood.module_flat_strictBaseChange
#print axioms eq_of_le_of_height_eq_one
#print axioms isTamelyRamifiedAt_of_etale_cover_of_flat
#print axioms isTamelyRamifiedAt_quotient_idempotent_of_etale_cover
#print axioms PointedEtaleNeighborhood.isTamelyRamifiedAt_strictBaseChangeFactor

end Pcf.Stacks
