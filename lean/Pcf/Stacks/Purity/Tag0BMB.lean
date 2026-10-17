/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.DimensionOne
public import Pcf.Stacks.Purity.Tag0BMBLocalModel

/-!
# Zariski--Nagata purity (Stacks Tag `0BMB`), affine pointwise form

This file assembles the affine pointwise form of purity of the branch locus,
`Pcf.Stacks.ZariskiNagataPurity`, by strong induction on the height of the point `w`:

* height `0` is vacuous, since the inputs require `1 ≤ height w`;
* height `1` is `hasZariskiNagataPurityAt_of_height_eq_one`;
* height `≥ 2` is `hasZariskiNagataPurityAt_of_lowerHeight`, fed with the induction hypothesis
  over all Noetherian finite-type pairs in `Type u`.

Heights are finite because the source is Noetherian.

The reduction takes two inputs as hypotheses: `EtaleNormalAscent` (Stacks Tag `033C`) and
finite normal punctured-spectrum étale purity for regular local rings of dimension at least two
(Stacks Tag `0BMA`). Both are proved, and the unconditional theorem is
`Pcf.Stacks.zariskiNagataPurity` in `Pcf.Stacks.Purity.Tag0BMA`.
-/

@[expose] public section

universe u

namespace Pcf.Stacks

/-- **Zariski--Nagata purity (Stacks Tag `0BMB`), affine pointwise form, from its inputs.**

For a finite-type map `R → S` of Noetherian rings and `w ∈ Spec S` with `S_w` a normal domain,
`R_{w ∩ R}` regular, `R → S` quasi-finite at `w`, `dim S_w = dim R_{w ∩ R} ≥ 1`, and `R → S`
unramified at every height-one generization of `w`, the map is étale at `w`. This matches Stacks
Lemma 58.21.4 specialized to affine schemes (finite type expresses the Stacks meaning of
quasi-finite).

Proof route: strong induction on `height w`, as in the Stacks proof, with the height-one base case
from `DimensionOne` and the inductive step from `Tag0BMBLocalModel`.

The hypotheses `h033C` (Stacks Tag `033C`, normality ascends along étale maps, in the form
`EtaleNormalAscent`) and `h0BMA` (Stacks Tag `0BMA`, finite normal punctured étale purity over
regular local rings of dimension `≥ 2`) are both proved; `zariskiNagataPurity` (in
`Pcf.Stacks.Purity.Tag0BMA`) discharges them and carries the Stacks `0BMB` attribute. -/
theorem zariskiNagataPurity_of_etaleNormalAscent
    (h033C : EtaleNormalAscent.{u})
    (h0BMA : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A],
      2 ≤ ringKrullDim A → FiniteNormalPuncturedEtalePurity A)
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    ZariskiNagataPurity R S := by
  suffices key : ∀ n : ℕ, ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
      IsNoetherianRing R → IsNoetherianRing S → Algebra.FiniteType R S →
      ∀ w : PrimeSpectrum S, w.asIdeal.height = n → HasZariskiNagataPurityAt R S w by
    intro hR hS hft w
    have hne : w.asIdeal.height ≠ ⊤ := Ideal.height_ne_top w.isPrime.ne_top
    exact key _ R S hR hS hft w (ENat.natCast_toNat hne).symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R S _ _ _ hR hS hft w hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · intro h
        have := h.positiveDimension
        rw [hn] at this
        exact absurd this (by norm_num)
      · exact hasZariskiNagataPurityAt_of_height_eq_one R S w (by exact_mod_cast hn)
    · refine hasZariskiNagataPurityAt_of_lowerHeight h033C h0BMA R S w
        (by rw [hn]; exact_mod_cast hge) ?_
      intro R₁ S₁ _ _ _ hR₁ hS₁ hft₁ w₁ hlt
      have hne : w₁.asIdeal.height ≠ ⊤ := Ideal.height_ne_top w₁.isPrime.ne_top
      have hlt' : w₁.asIdeal.height.toNat < n := by
        rw [hn] at hlt
        rw [← ENat.natCast_lt_natCast, ENat.natCast_toNat hne]
        exact hlt
      exact ih _ hlt' R₁ S₁ hR₁ hS₁ hft₁ w₁ (ENat.natCast_toNat hne).symm

end Pcf.Stacks
