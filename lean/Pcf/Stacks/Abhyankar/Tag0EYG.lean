/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Tame.Tag0EYGTame
public import Pcf.Palomar.Statement

/-!
# Abhyankar's lemma for a regular divisor (Stacks Tags `0EYG`, `0EYH`)

The main theorem: `Pcf.Stacks.abhyankarLemma_of_finite`, an unconditional
proof of `Pcf.Stacks.AbhyankarLemmaOfFinite R S a` (the normalization `S` assumed finite over `R`)
for all `R S a`, and its Palomar-facing form `palomar_abhyankarLemma`.  The public statement
`Pcf.Stacks.abhyankarLemma`, which proves that finiteness (Stacks `0EYH`), is in
`Pcf.Stacks.Abhyankar.FiniteNormalization`.

* `hasAbhyankarStandardCoverAt_of_mem_divisor`: the conclusion at a point `y ∈ V(a)`.  Every
  positive integer being a unit of `R`, `S` is tamely ramified in codimension one
  (`isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit`), so this is the tame case
  `hasAbhyankarStandardCoverAt_of_mem_divisor_tame` (`Tame/Tag0EYGTame.lean`);
* `abhyankarLemma_of_finite`, `palomar_abhyankarLemma`.
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

namespace Pcf.Stacks

set_option linter.style.haveILetI false

/-- **Abhyankar's lemma at a point of the divisor (Stacks Tags `0EYG`, `0EYH`).**  The unpacked
form of `abhyankarLemma_of_finite`.  If every positive integer is a unit of `R`, then `S` is
tamely ramified over `R` in codimension one
(`isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit`), and the conclusion is the tame case
`hasAbhyankarStandardCoverAt_of_mem_divisor_tame`. -/
theorem hasAbhyankarStandardCoverAt_of_mem_divisor
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R)
    [IsNoetherianRing R] (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))] [Module.Finite R S]
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal →
      Algebra.IsEtaleAt R w.asIdeal)
    [IsIntegralClosure S R (Localization.Away (algebraMap R S a))]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (y : PrimeSpectrum R) (hy : a ∈ y.asIdeal) :
    HasAbhyankarStandardCoverAt R S a y :=
  hasAbhyankarStandardCoverAt_of_mem_divisor_tame R S a ha hetale
    (isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit R S hnat a) y hy

/-- **Abhyankar's lemma for a regular divisor (Stacks Tags `0EYG` and `0EYH`)**, unconditionally,
in pcf's affine form `Pcf.Stacks.AbhyankarLemmaOfFinite` (normalization assumed finite).

Comparison with the tags (restrictions, all already part of the statement
`Pcf.Stacks.AbhyankarLemmaOfFinite`, not introduced here).
* *Affine form*: `X = Spec R` with `R` Noetherian and `D = V(a)`, `a` a nonzerodivisor with
  `R ⧸ (a)` regular (`D` an effective Cartier divisor which is a regular scheme).
* *Tameness*: every positive integer is invertible in `R` (a `ℚ`-algebra), which is stronger
  than the tags' hypothesis "tamely ramified in codimension one".
* *Conclusion shape*: instead of `Y → X ∖ D`, the input is its normalization `S` (assumed finite
  over `R` here, étale away from `a`, the integral closure of `R` in `S[1/a]`; the public
  `Pcf.Stacks.abhyankarLemma` assumes only `S[1/a]` finite over `R[1/a]` and proves the finiteness
  of `S`, Stacks `0EYH`), and the conclusion is the
  `0EYH` local-structure form: at every point `y ∈ V(a)` there is an étale neighbourhood
  `R → R'` over `y` with `R'` Noetherian, `a` a nonzerodivisor with `R' ⧸ (a)` regular, and
  `R' ⊗_R S` a finite product of `R'[x]/(x^e - u a)` with `e` invertible (here even `u = 1`).
  Points outside `D` (the tag's trivial case) are not treated.

Proof route: every positive integer being invertible in `R`, `S` is tamely ramified over `R` in
codimension one (`isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit`: the ramification
indices are units and the residue extensions are separable in characteristic zero), and the proof
is that of the tame case, `Pcf.Stacks.abhyankarLemma_tame_of_finite` (`Tame/Tag0EYGTame.lean`), whose
lemmas are shared by both theorems: reduction to the strict henselization at `κ(y)ˢᵉᵖ`,
decomposition into normal domains, root cover, `0BRM`, `0EYE` with Zariski–Nagata purity, strict
splitting, `09EV`, the exponent is a unit, descent to an étale stage.  The divergences from the
Stacks proof are recorded there and at the shared lemmas.  The scheme-level statements of the
tags are `Pcf.Stacks.SchemeLevel.tag0EYG` and `Pcf.Stacks.SchemeLevel.tag0EYH`
(`Scheme/Tag0EYG.lean`, `Scheme/Tag0EYH.lean`). -/
@[stacks 0EYG "affine; all positive integers invertible; normalization (0EYH) form at points \
    of D, normalization assumed finite over R; pieces R'[x]/(x^e - f), f = u_i a",
  stacks 0EYH "affine; all positive integers invertible; local structure clause at points of D, \
    normalization assumed finite over R; pieces R'[x]/(x^e - f), f = u_i a"]
theorem abhyankarLemma_of_finite (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    AbhyankarLemmaOfFinite R S a := by
  intro _ ha hreg hfin hetale hint hnat y hy
  haveI := hreg
  haveI := hfin
  haveI := hint
  exact hasAbhyankarStandardCoverAt_of_mem_divisor R S a ha hetale hnat y hy

/-- The Palomar-facing form `Pcf.Palomar.AbhyankarLemma` (definitionally
`Pcf.Stacks.AbhyankarLemmaOfFinite`: the Palomar statement assumes the normalization finite). -/
theorem palomar_abhyankarLemma (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    Pcf.Palomar.AbhyankarLemma R S a :=
  abhyankarLemma_of_finite R S a

end Pcf.Stacks
