/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Tame.Defs
public import Pcf.Stacks.Abhyankar.Tame.GenericPresentation
public import Pcf.Stacks.Abhyankar.Tame.StrictBaseChangeTame
public import Pcf.Stacks.Abhyankar.Tame.StandardDescent
public import Pcf.Stacks.Abhyankar.Tag0EYG

/-!
# Abhyankar's lemma for a regular divisor, tame case (Stacks Tags `0EYG`, `0EYH`)

The second proof of Abhyankar's lemma for a regular divisor in pcf: the hypothesis of the tag
("tamely ramified in codimension `1`", any characteristic) instead of the characteristic-zero
hypothesis of `Pcf.Stacks.abhyankarLemma`.  Main theorem: `Pcf.Stacks.abhyankarLemma_tame :
∀ R S a, AbhyankarLemmaTame R S a`, with the unpacked form
`hasAbhyankarStandardCoverAt_of_mem_divisor_tame`.

## Stacks correspondence (proof of `0EYG`, Lemma 58.31.5)

Stacks step → Lean:
* "We will assume `x ∈ D`" — the statement is for `y ∈ V(a)`.
* "`X = Spec(A)`, `D` given by a nonzerodivisor `f`; `Y = Spec(B)`" — affine form: `R`, `a`, `S`
  (with `S` the normalization, `0EYH` form).
* "Let `A^{sh}` be the strict henselization of `𝒪_{X,x}`" — `LocalColimit R Ω`, `Ω = κ(y)ˢᵉᵖ`,
  compared with that of `R_y` by `04GW` (`localColimitAtPrimeRingEquiv`).
* "`A → A^{sh}` is flat … `f` maps to a nonzerodivisor of the maximal ideal of `A^{sh}`" —
  `algebraMap_mem_nonZeroDivisors_localColimit`, `map_le_maximalIdeal_localColimit`.
* "`A^{sh}/fA^{sh} = (A/fA)^{sh}` (10.156.4) is a regular local ring (15.46.10)" —
  `quotient_span_localColimit_isRegularLocalRing` (`05WS`, `06LN`).
* "By Lemma 58.31.1 (`0EYD`) the base change of `Y` to `Spec(A^{sh})` is tamely ramified in
  codimension `1`" — `isTamelyRamifiedAt_quotient_idempotent_of_etale_cover` instantiated at
  `Rˢʰ ⊗_R S` (`PointedEtaleNeighborhood.isTamelyRamifiedAt_strictBaseChangeFactor`).
* "Assume we've proven the assertion for the base change … `A^{sh} ⊗_A B ≅ ∏ A^{sh}_f[x]/(x^{e_i} - f)`"
  — `isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian_tame` (integral `0EYH` form).
* "The displayed isomorphism descends … (10.127.8). After increasing `λ` … `e_i` is invertible in
  `A_λ`" — `hasAbhyankarStandardCoverAt_of_strict_tame` (`05N9` descent, `exists_stage_natCast_isUnit`).

Divergences from Stacks: the strict henselization of `R` at `κ(y)ˢᵉᵖ` is compared with that of
`R_y` (`04GW`) rather than working with `𝒪_{X,x}` directly; the normalization step is carried out on
the integral models, so the conclusion is the `0EYH` form `R' ⊗_R S ≅ ∏ R'[x]/(x^{e_i} - a)`
directly; `0EYD` is proved by comparing ramification indices along the ind-étale base change
instead of via More on Algebra 15.116.9.  The points `x ∉ D` of the tag are not treated.
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

namespace Pcf.Stacks

set_option linter.style.haveILetI false

open PointedEtaleNeighborhood in
/-- **Abhyankar's lemma at a point of the divisor, tame case (Stacks Tags `0EYG`, `0EYH`).**  The
unpacked form of `abhyankarLemma_tame`: with `Ω = κ(y)ˢᵉᵖ`, the strict henselization
`Rˢʰ = LocalColimit R Ω` is identified with that of `R_y` (`04GW`), which transports
Noetherianity, strict henselianity and regularity of `Rˢʰ ⧸ (a)`; tameness of `S[1/a]` over `R` in
codimension one is transported to each normal-domain component of `Rˢʰ ⊗_R S` (`0EYD`,
`isTamelyRamifiedAt_strictBaseChangeFactor`); then `Rˢʰ ⊗_R S` is a finite product of standard root
covers with invertible exponents (`isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian_tame`),
which descends to a pointed étale neighbourhood (`05N9`, `hasAbhyankarStandardCoverAt_of_strict_tame`).

The proof is that of `hasAbhyankarStandardCoverAt_of_mem_divisor` (phase 1) with the two uses of
"every positive integer is a unit" replaced by the tame inputs. -/
theorem hasAbhyankarStandardCoverAt_of_mem_divisor_tame
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R)
    [IsNoetherianRing R] (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))] [Module.Finite R S]
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal →
      Algebra.IsEtaleAt R w.asIdeal)
    [IsIntegralClosure S R (Localization.Away (algebraMap R S a))]
    (htame : IsTamelyRamifiedInCodimensionOneAlong R S a)
    (y : PrimeSpectrum R) (hy : a ∈ y.asIdeal) :
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
  -- the normalization after base change
  haveI : Algebra.Etale B (Localization.Away (algebraMap B (B ⊗[R] S) aB)) :=
    etale_localizationAway_baseChange (S := S) B a hetale
  haveI : IsIntegralClosure (B ⊗[R] S) B (Localization.Away (algebraMap B (B ⊗[R] S) aB)) :=
    localColimit_isIntegralClosure_localizationAway (Ω := Ω) (S := S) a
  -- `0EYD`: tameness of each normal-domain component of `B ⊗[R] S` over `B`
  -- (`isTamelyRamifiedAt_quotient_idempotent_of_etale_cover`, instantiated at the strict base
  -- change with its étale-stage cover and flatness over `S`)
  letI : Algebra S (B ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Flat R B := localColimit_flat (R := R) (Ω := Ω)
  haveI : Module.Flat S (B ⊗[R] S) := module_flat_strictBaseChange (R := R) (Ω := Ω) S
  have hstrict : IsFiniteDisjointUnionOfStandardTameCovers B (B ⊗[R] S) aB := by
    refine isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian_tame aB haB ha0B ?_
    intro e he _ _ _ q hq hqa
    exact isTamelyRamifiedAt_quotient_idempotent_of_etale_cover a htame haB ha0B
      (exists_etale_cover_strictBaseChange (R := R) (Ω := Ω) S) e he q hq hqa
  exact hasAbhyankarStandardCoverAt_of_strict_tame a y hΩ ha hstrict

/-- **Abhyankar's lemma for a regular divisor, tame case (Stacks Tags `0EYG` and `0EYH`)**, in
pcf's affine form `Pcf.Stacks.AbhyankarLemmaTame`: the hypothesis of the tag, "tamely ramified in
codimension `1`" (`IsTamelyRamifiedInCodimensionOneAlong`, Stacks `0BSE` with `09E9`; see
`isTamelyRamifiedInCodimensionOneAlong_iff` for the fidelity check), in any characteristic.

Comparison with the tags (restrictions, all part of the statement `AbhyankarLemmaTame`):
* *Affine form*: `X = Spec R` with `R` Noetherian and `D = V(a)`, `a` a nonzerodivisor with
  `R ⧸ (a)` regular (`D` an effective Cartier divisor which is a regular scheme).
* *Conclusion shape*: instead of `Y → X ∖ D`, the input is its normalization `S` (finite over
  `R`, étale away from `a`, the integral closure of `R` in `S[1/a]`), and the conclusion is the
  `0EYH` local-structure form: at every point `y ∈ V(a)` there is an étale neighbourhood
  `R → R'` over `y` with `R'` Noetherian, `a` a nonzerodivisor with `R' ⧸ (a)` regular, and
  `R' ⊗_R S` a finite product of `R'[x]/(x^e - u a)` with `e` invertible in `R'` (here even
  `u = 1`).  Points outside `D` (the tag's trivial case) are not treated.

This is the second proof of the tag in pcf; the first, `Pcf.Stacks.abhyankarLemma`, assumes that
every positive integer is invertible and is unchanged.  Proof route: that of `0EYG`, see the module
docstring and `hasAbhyankarStandardCoverAt_of_mem_divisor_tame`; the divergences from the Stacks
proof are recorded at each declaration of `Pcf.Stacks.Abhyankar.Tame`. -/
@[stacks 0EYG "affine form; tamely ramified in codimension 1, any characteristic; normalization \
    (0EYH) form at points of D; pieces R'[x]/(x^e - f), f = u_i a",
  stacks 0EYH "affine local-structure clause at points of D; tamely ramified in codimension 1, \
    any characteristic; pieces R'[x]/(x^e - f), f = u_i a"]
theorem abhyankarLemma_tame (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    AbhyankarLemmaTame R S a := by
  intro _ ha hreg hfin hetale hint htame y hy
  haveI := hreg
  haveI := hfin
  haveI := hint
  exact hasAbhyankarStandardCoverAt_of_mem_divisor_tame R S a ha hetale htame y hy

/-- The characteristic-zero theorem of phase 1 is recovered from the tame theorem (a consistency
check; `Pcf.Stacks.abhyankarLemma` keeps its own proof). -/
theorem abhyankarLemma_of_tame (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    AbhyankarLemma R S a :=
  AbhyankarLemma.of_tame (abhyankarLemma_tame R S a)

#print axioms hasAbhyankarStandardCoverAt_of_mem_divisor_tame
#print axioms abhyankarLemma_tame
#print axioms abhyankarLemma_of_tame

#check @hasAbhyankarStandardCoverAt_of_mem_divisor_tame
#check @abhyankarLemma_tame

end Pcf.Stacks
