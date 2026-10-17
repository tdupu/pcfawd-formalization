/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictGenericPresentation
public import Pcf.Stacks.Abhyankar.StrictHenselizationLocalize
public import Pcf.Stacks.Abhyankar.StrictStandardConclusion
public import Pcf.Palomar.Statement

/-!
# Abhyankar's lemma for a regular divisor (Stacks Tags `0EYG`, `0EYH`)

The main theorem: `Pcf.Stacks.abhyankarLemma`, an unconditional
proof of `Pcf.Stacks.AbhyankarLemma R S a` for all `R S a`, and its Palomar-facing form
`palomar_abhyankarLemma`.

* `henselianLocalRing_of_ringEquiv`: transport of henselianity along a ring equivalence;
* `PointedEtaleNeighborhood.geometricPointAt p = κ(p)ˢᵉᵖ`, with `R → κ(p)ˢᵉᵖ` of kernel `p`;
* `hasAbhyankarStandardCoverAt_of_mem_divisor`: the conclusion at a point `y ∈ V(a)`, by comparing
  `LocalColimit R Ω` with `LocalColimit R_y Ω` (`localColimitAtPrimeRingEquiv`, Stacks `04GW`),
  applying the strictly henselian case
  `isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian`, and descending with
  `hasAbhyankarStandardCoverAt_of_strict`;
* `abhyankarLemma`, `palomar_abhyankarLemma`.
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section Transport

variable {B B' : Type u} [CommRing B] [CommRing B']

/-- Henselianity is invariant under ring equivalence. -/
theorem henselianLocalRing_of_ringEquiv [HenselianLocalRing B'] (e : B' ≃+* B) :
    HenselianLocalRing B := by
  let _ : Nontrivial B := e.symm.toEquiv.nontrivial
  let _ : IsLocalRing B := IsLocalRing.of_surjective' e.toRingHom e.surjective
  apply ((HenselianLocalRing.TFAE B).out 3 1).mp
  intro K _ φ hφ f hf a₀ ha₀ hda₀
  let q : B' →+* B := e.toRingHom
  have hlifts : f ∈ Polynomial.lifts q := Polynomial.mem_lifts_of_surjective e.surjective f
  obtain ⟨F, hF, -, hFmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hf
  let ψ : B' →+* K := φ.comp q
  have hψ : Function.Surjective ψ := hφ.comp e.surjective
  have hroot : F.eval₂ ψ a₀ = 0 := by
    rw [← Polynomial.eval₂_map, hF]
    exact ha₀
  have hderiv : F.derivative.eval₂ ψ a₀ ≠ 0 := by
    rw [← Polynomial.eval₂_map, ← Polynomial.derivative_map, hF]
    exact hda₀
  have hhens := ((HenselianLocalRing.TFAE B').out 1 3).mp (inferInstance : HenselianLocalRing B')
  obtain ⟨a, ha, hφa⟩ := hhens (K := K) ψ hψ F hFmonic a₀ hroot hderiv
  refine ⟨q a, ?_, hφa⟩
  change f.eval (q a) = 0
  rw [← hF, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha.eq_zero, map_zero]

end Transport

namespace PointedEtaleNeighborhood

open Pcf.Stacks.PointedEtaleNeighborhood

/-- The separably closed geometric point at a prime `p` of `R`: `Ω = κ(p)ˢᵉᵖ`, where `κ(p)` is
the residue field of `R_p`. -/
abbrev geometricPointAt {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] : Type u :=
  SeparableClosure (ResidueField (Localization.AtPrime p))

/-- The structure map `R → κ(p)ˢᵉᵖ`. -/
@[instance_reducible]
noncomputable def geometricPointAtAlgebra {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Algebra R (geometricPointAt p) :=
  ((algebraMap (ResidueField (Localization.AtPrime p)) (geometricPointAt p)).comp
    ((residue (Localization.AtPrime p)).comp (algebraMap R (Localization.AtPrime p)))).toAlgebra

theorem ker_geometricPointAtAlgebra {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    letI := geometricPointAtAlgebra p
    RingHom.ker (algebraMap R (geometricPointAt p)) = p := by
  letI := geometricPointAtAlgebra p
  ext r
  change (algebraMap (ResidueField (Localization.AtPrime p)) (geometricPointAt p))
    (residue _ (algebraMap R (Localization.AtPrime p) r)) = 0 ↔ r ∈ p
  rw [map_eq_zero, residue_eq_zero_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p]

end PointedEtaleNeighborhood

open PointedEtaleNeighborhood in
/-- **Abhyankar's lemma at a point of the divisor (Stacks Tags `0EYG`, `0EYH`).**  The unpacked
form of `abhyankarLemma`: with `Ω = κ(y)ˢᵉᵖ`, the strict henselization `Rˢʰ = LocalColimit R Ω`
is identified with that of `R_y` (`04GW`), which transports Noetherianity, strict henselianity and
regularity of `Rˢʰ ⧸ (a)`; then `Rˢʰ ⊗_R S` is a finite product of standard root covers
(`isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian`), which descends to a pointed
étale neighbourhood (`05N9`, `hasAbhyankarStandardCoverAt_of_strict`). -/
theorem hasAbhyankarStandardCoverAt_of_mem_divisor
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R)
    [IsNoetherianRing R] (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))] [Module.Finite R S]
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal →
      Algebra.IsEtaleAt R w.asIdeal)
    [IsIntegralClosure S R (Localization.Away (algebraMap R S a))]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (y : PrimeSpectrum R) (hy : a ∈ y.asIdeal) :
    HasAbhyankarStandardCoverAt R S a y := by
  let p := y.asIdeal
  let Rp := Localization.AtPrime p
  let Ω := geometricPointAt p
  letI : Algebra R Ω := geometricPointAtAlgebra p
  have hΩ : RingHom.ker (algebraMap R Ω) = p := ker_geometricPointAtAlgebra p
  letI : Algebra Rp Ω := atPrimeAlgebra p hΩ
  haveI hRpΩ : IsScalarTower R Rp Ω := atPrimeAlgebra_isScalarTower p hΩ
  haveI : IsScalarTower Rp (ResidueField Rp) Ω := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    apply IsLocalization.ringHom_ext p.primeCompl
    rw [← IsScalarTower.algebraMap_eq, RingHom.comp_assoc,
      IsLocalRing.ResidueField.algebraMap_eq]
    rfl
  -- the strict henselizations of `R` at `Ω` and of `R_p`
  let B := LocalColimit R Ω
  let B' := LocalColimit Rp Ω
  let φ : B ≃+* B' := localColimitAtPrimeRingEquiv p hΩ
  have hφ : ∀ r : R, φ (algebraMap R B r) = algebraMap Rp B' (algebraMap R Rp r) :=
    localColimitAtPrimeRingEquiv_algebraMap p hΩ
  -- facts about `R_p`
  have haRp : algebraMap R Rp a ∈ maximalIdeal Rp := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff Rp p]
    exact hy
  haveI : IsRegularLocalRing (Rp ⧸ Ideal.span ({algebraMap R Rp a} : Set Rp)) := by
    have := isRegularLocalRing_quotient_localization (Ideal.span ({a} : Set R)) p
      ((Ideal.span_singleton_le_iff_mem p).mpr hy)
    rwa [Ideal.map_span, Set.image_singleton] at this
  -- transport the strict-local facts from `B'` to `B`
  haveI : IsNoetherianRing B := isNoetherianRing_of_ringEquiv B' φ.symm
  haveI : HenselianLocalRing B := henselianLocalRing_of_ringEquiv φ.symm
  haveI : IsSepClosed (ResidueField B) :=
    isSepClosed_of_ringEquiv (IsLocalRing.ResidueField.mapEquiv φ.symm)
  let aB : B := algebraMap R B a
  have hφa : φ aB = algebraMap Rp B' (algebraMap R Rp a) := hφ a
  have haB : aB ∈ maximalIdeal B := by
    have h' : algebraMap Rp B' (algebraMap R Rp a) ∈ maximalIdeal B' :=
      map_le_maximalIdeal_localColimit (Ideal.span {algebraMap R Rp a})
        (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact haRp)
        (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton _)))
    rw [← hφa, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff] at h'
    exact h'
  have ha0B : aB ∈ nonZeroDivisors B := algebraMap_mem_nonZeroDivisors_localColimit ha
  haveI : IsRegularLocalRing (B ⧸ Ideal.span ({aB} : Set B)) := by
    haveI : IsRegularLocalRing (B' ⧸ Ideal.span
        ({algebraMap Rp B' (algebraMap R Rp a)} : Set B')) :=
      quotient_span_localColimit_isRegularLocalRing (Ω := Ω) (algebraMap R Rp a)
    exact IsRegularLocalRing.of_ringEquiv (Ideal.quotientEquiv (Ideal.span ({aB} : Set B))
      (Ideal.span ({algebraMap Rp B' (algebraMap R Rp a)} : Set B')) φ (by
        rw [Ideal.map_span, Set.image_singleton]
        exact congrArg (fun x ↦ Ideal.span {x}) hφa.symm)).symm
  have hnatB : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B) := fun n hn ↦ by
    simpa only [map_natCast] using (hnat n hn).map (algebraMap R B)
  -- the normalization after base change
  haveI : Algebra.Etale B (Localization.Away (algebraMap B (B ⊗[R] S) aB)) :=
    etale_localizationAway_baseChange (S := S) B a hetale
  haveI : IsIntegralClosure (B ⊗[R] S) B (Localization.Away (algebraMap B (B ⊗[R] S) aB)) :=
    localColimit_isIntegralClosure_localizationAway (Ω := Ω) (S := S) a
  have hstrict : IsFiniteDisjointUnionOfStandardTameCovers B (B ⊗[R] S) aB :=
    isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian aB haB ha0B hnatB
  exact hasAbhyankarStandardCoverAt_of_strict a y hΩ ha hnat hstrict

/-- **Abhyankar's lemma for a regular divisor (Stacks Tags `0EYG` and `0EYH`)**, unconditionally,
in pcf's affine form `Pcf.Stacks.AbhyankarLemma`.

Comparison with the tags (restrictions, all already part of the statement
`Pcf.Stacks.AbhyankarLemma`, not introduced here).
* *Affine form*: `X = Spec R` with `R` Noetherian and `D = V(a)`, `a` a nonzerodivisor with
  `R ⧸ (a)` regular (`D` an effective Cartier divisor which is a regular scheme).
* *Tameness*: every positive integer is invertible in `R` (a `ℚ`-algebra), which is stronger
  than the tags' hypothesis "tamely ramified in codimension one".
* *Conclusion shape*: instead of `Y → X ∖ D`, the input is its normalization `S` (finite over
  `R`, étale away from `a`, the integral closure of `R` in `S[1/a]`), and the conclusion is the
  `0EYH` local-structure form: at every point `y ∈ V(a)` there is an étale neighbourhood
  `R → R'` over `y` with `R'` Noetherian, `a` a nonzerodivisor with `R' ⧸ (a)` regular, and
  `R' ⊗_R S` a finite product of `R'[x]/(x^e - u a)` with `e` invertible (here even `u = 1`).
  Points outside `D` (the tag's trivial case) are not treated.

Proof route: follows the proof of `0EYG` (reduction to the strict henselization at `κ(y)ˢᵉᵖ`,
decomposition into normal domains, root cover of exponent a common multiple `E` of the
ramification indices, `0BRM`, `0EYE` with Zariski–Nagata purity, strict splitting, `09EV`), with
two differences: the strict henselization of `R` is compared to that of `R_y` (Stacks `04GW`,
`localColimitAtPrimeRingEquiv`), and the normalization step is carried out on the integral
models (`strictRootCoverEquivOfFractionRingEquiv`) rather than over `A_f`, which gives the
`0EYH` conclusion directly. -/
@[stacks 0EYG "affine; all positive integers invertible; normalization (0EYH) form at points \
    of D; pieces R'[x]/(x^e - f), f = u_i a",
  stacks 0EYH "affine; all positive integers invertible; local structure clause at points of D; \
    pieces R'[x]/(x^e - f), f = u_i a"]
theorem abhyankarLemma (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    AbhyankarLemma R S a := by
  intro _ ha hreg hfin hetale hint hnat y hy
  haveI := hreg
  haveI := hfin
  haveI := hint
  exact hasAbhyankarStandardCoverAt_of_mem_divisor R S a ha hetale hnat y hy

/-- The Palomar-facing form `Pcf.Palomar.AbhyankarLemma` (definitionally the same statement). -/
theorem palomar_abhyankarLemma (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    Pcf.Palomar.AbhyankarLemma R S a :=
  abhyankarLemma R S a

#print axioms henselianLocalRing_of_ringEquiv
#print axioms PointedEtaleNeighborhood.ker_geometricPointAtAlgebra
#print axioms hasAbhyankarStandardCoverAt_of_mem_divisor
#print axioms abhyankarLemma
#print axioms palomar_abhyankarLemma

#check @hasAbhyankarStandardCoverAt_of_mem_divisor
#check @abhyankarLemma
#check @palomar_abhyankarLemma

end Pcf.Stacks
