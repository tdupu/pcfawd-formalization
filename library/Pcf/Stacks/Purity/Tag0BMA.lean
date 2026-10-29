/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Common.EtaleNormal
public import Pcf.Stacks.Common.RegularLocalization
public import Pcf.Stacks.Common.RegularNormal
public import Pcf.Stacks.Purity.Completion
public import Pcf.Stacks.Purity.CompletionDescent
public import Pcf.Stacks.Purity.DimensionTwo
public import Pcf.Stacks.Purity.HypersurfaceLiftingComplete
public import Pcf.Stacks.Purity.Tag0BM9
public import Pcf.Stacks.Purity.Tag0BMAClauses
public import Pcf.Stacks.Purity.Tag0BMB

/-!
# Purity for regular local rings (Stacks Tag `0BMA`) and unconditional Zariski--Nagata purity

Stacks Lemma 58.21.3 (`0BMA`): for a regular local ring `A` of dimension `d ≥ 2`,

1. every finite étale cover of the punctured spectrum extends over `Spec A`
   (`PuncturedSpectrumPurity A`), and
2. every finite normal `A`-algebra which is étale over the punctured spectrum is étale
   (`FiniteNormalPuncturedEtalePurity A`, pcf's finite, torsion-free, Stacks-normal form).

The assembly here:

* `puncturedSpectrumPurity_of_finiteNormalPuncturedEtalePurity`: clause (2) ⇒ clause (1), via
  essential surjectivity in Tag `0BM9`; the converse is the existing
  `finiteNormalPuncturedEtalePurity_of_puncturedSpectrumPurity`.
* `puncturedSpectrumPurity_of_isRegularLocalRing_of_isAdicComplete`: clause (1) for complete
  regular local rings, by induction on the dimension. The base case `d = 2` is `DimensionTwo`;
  the step uses the complete-case hypersurface lifting theorem (`0BLM`, complete regular case)
  for `A/(x)`, which is again complete regular local of one less dimension.
* `finiteNormalPuncturedEtalePurity_of_isRegularLocalRing`: clause (2) in general, by descent
  from the completion (`CompletionDescent`).
* `puncturedSpectrumPurity_of_isRegularLocalRing`: clause (1) in general.
* `zariskiNagataPurity`: Stacks Tag `0BMB` with no hypotheses.

Proof route diverges from Stacks: the induction runs over complete rings and replaces the
local-cohomology argument of `0BM6`/`0EKS` (behind `0BLM`) by an elementary formal lifting, and
the passage from `A` to its completion replaces `0BLL`/`0BLH` by a Hartogs plus fpqc-descent
argument.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Pcf.Stacks

/-- Clause (2) of Stacks Tag `0BMA` implies clause (1).

Every finite étale cover `V` of the punctured spectrum comes from a finite torsion-free normal
algebra `B` (essential surjectivity in Tag `0BM9`); clause (2) makes `B` étale, so `Spec B` is a
finite étale cover of `Spec R` restricting to `V` (the "if" direction of the last sentence of
Tag `0BM9`). -/
theorem puncturedSpectrumPurity_of_finiteNormalPuncturedEtalePurity
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (hdim : 1 ≤ ringKrullDim R)
    (hpurity : FiniteNormalPuncturedEtalePurity R) :
    PuncturedSpectrumPurity R := by
  constructor
  intro V
  obtain ⟨Bobj, ⟨eB⟩⟩ := puncturedCover_exists_finiteNormalPuncturedEtaleAlgebra (.of R) hdim V
  have hBet : Algebra.Etale R Bobj.obj.unop := hpurity Bobj.obj Bobj.property
  let p : Spec (.of Bobj.obj.unop) ⟶ Spec (.of R) := ((algSpec (.of R)).obj Bobj.obj).hom
  have hpFinite : IsFinite p := Bobj.isFinite_algSpec
  have hpEtale : Etale p := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap R Bobj.obj.unop)))
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hBet)
  let Y : FiniteEtaleCover (Spec (.of R)) := MorphismProperty.Over.mk ⊤ p ⟨hpFinite, hpEtale⟩
  refine ⟨Y, ⟨?_ ≪≫ eB⟩⟩
  exact MorphismProperty.Comma.isoFromComma (Iso.refl _)

/-- Clause (1) of Stacks Tag `0BMA` in dimension two. -/
theorem puncturedSpectrumPurity_of_isRegularLocalRing_dimension_two
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    PuncturedSpectrumPurity A := by
  have : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  have : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  exact puncturedSpectrumPurity_of_finiteNormalPuncturedEtalePurity A
    (by rw [hdim]; norm_num)
    (finiteNormalPuncturedEtalePurity_of_isRegularLocalRing_of_isIntegrallyClosed_dimension_two
      A hdim)

/-- **Stacks Tag `0BMA`, clause (1), complete case.** Every finite étale cover of the punctured
spectrum of a complete regular local ring of dimension `≥ 2` extends over the whole spectrum.

Proof: induction on the dimension, as in Stacks. The base case `d = 2` is `DimensionTwo`
(via clause (2) ⇒ clause (1)). In the step, `A/(x)` for `x ∈ m \ m²` is again a complete
regular local ring, of one less dimension.

Proof route diverges from Stacks.  Stacks runs the induction over all regular local rings and
applies `0BLM`, whose proof (`0BLS`) reduces to the completion by `0BLL`, lifts with `09ZL`, and
gets full faithfulness from local cohomology (`0BM6`, `0EKS`).  Here the induction runs over
complete regular local rings only (the passage to arbitrary `A` is
`finiteNormalPuncturedEtalePurity_of_isRegularLocalRing`), and the step uses
`hypersurfaceFiniteEtaleLifting_of_isAdicComplete`, which replaces `0BM6`/`0EKS` by an
elementary formal lifting. -/
@[stacks 0BMA "clause (1), complete regular local case"]
theorem puncturedSpectrumPurity_of_isRegularLocalRing_of_isAdicComplete
    (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (hdim : 2 ≤ ringKrullDim A) :
    PuncturedSpectrumPurity A := by
  suffices key : ∀ d : ℕ, 2 ≤ d → ∀ (B : Type u) [CommRing B] [IsRegularLocalRing B]
      [IsAdicComplete (maximalIdeal B) B], ringKrullDim B = d → PuncturedSpectrumPurity B by
    have hfin : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
    have hbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim A = n := by
      induction h : ringKrullDim A using WithBot.recBotCoe with
      | bot => exact absurd h hbot
      | coe e =>
        induction e using ENat.recTopCoe with
        | top => exact absurd h hfin
        | coe n => exact ⟨n, rfl⟩
    refine key n ?_ A hn
    rw [hn] at hdim
    exact_mod_cast hdim
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
    intro B _ _ _ hB
    exact puncturedSpectrumPurity_of_isRegularLocalRing_dimension_two B (by exact_mod_cast hB)
  | succ d hd ih =>
    intro B _ _ _ hB
    refine regularLocal_puncturedSpectrumPurity_induction_step_of_isAdicComplete B d hd
      (by exact_mod_cast hB) ?_
    intro x hx hx2 _ hdimx
    have : IsAdicComplete (maximalIdeal (B ⧸ Ideal.span ({x} : Set B)))
        (B ⧸ Ideal.span ({x} : Set B)) :=
      isAdicComplete_maximalIdeal_quotient _
    exact ih _ hdimx

/-- **Stacks Tag `0BMA`, clause (2)**, in pcf's finite-normal form: for a regular local ring `A`
of dimension `≥ 2`, every finite, torsion-free, Stacks-normal `A`-algebra which is étale over the
punctured spectrum is étale.

Divergence from Stacks (deliberate, statement-level): Stacks' literal clause (2) says that any
finite `A → B` with `B` normal which induces a finite étale morphism on punctured spectra is
étale.  This is false as stated.  Take `B = A × κ(𝔪)`: it is finite over `A` and normal (a product
of normal domains), and the `κ(𝔪)` factor lies over the closed point, so `Spec B` restricted to
the punctured spectrum `U` is `U → U`, which is étale.  But `κ(𝔪)` is not flat over `A` (as
`dim A ≥ 2`), so `B` is not flat, hence not étale.  The Lean statement therefore adds the
hypothesis "`B` is torsion-free over `A`" (equivalently, no irreducible component of `Spec B` lies
over the closed point), which is exactly what the Stacks proof uses (it takes `B` to be the global
sections `Γ(V, 𝒪_V)` of a cover of `U`, as in Tag `0BM9`).  The counterexample `B = A × κ(𝔪)` is
reported in Stacks comment #11774 on Tag `0BMA`.

Concretely, "finite `A → B`, `B` normal" is made precise as `FiniteNormalPuncturedEtalePurity`
(finite, torsion-free, Stacks-normal), the target category of Tag `0BM9`.

Proof route diverges from Stacks (phase-1 proof, not re-proved).  Stacks proves `0BMA` by
induction on `d` for `A` itself, through `0BLM`, whose proof (`0BLS`) passes to the completion by
`0BLL` (which uses `0BLH`) and gets full faithfulness from `0BM6`/`0EKS`.  Here clause (1) is
proved for the completion `A^∧` (complete case above, using the elementary formal lifting in
place of `0BM6`/`0EKS`), and clause (2) for `A` then follows by completion descent (Hartogs for a
regular pair plus fpqc descent of étaleness, in place of `0BLL`/`0BLH`). -/
@[stacks 0BMA "clause (2), with B torsion-free over A added; literal clause (2) is false for
  B = A × κ(𝔪)"]
theorem finiteNormalPuncturedEtalePurity_of_isRegularLocalRing
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : 2 ≤ ringKrullDim A) :
    FiniteNormalPuncturedEtalePurity A :=
  finiteNormalPuncturedEtalePurity_of_completion_puncturedSpectrumPurity A hdim
    (puncturedSpectrumPurity_of_isRegularLocalRing_of_isAdicComplete _
      ((ringKrullDim_adicCompletion A).symm ▸ hdim))

/-- **Stacks Tag `0BMA`, clause (1)**: for a regular local ring of dimension `≥ 2`, every finite
étale cover of the punctured spectrum extends to a finite étale cover of the spectrum.

Proof: from clause (2) (`finiteNormalPuncturedEtalePurity_of_isRegularLocalRing`) through the
equivalence of Tag `0BM9` (Lemma 58.20.3), which is also how the Stacks proof passes between the
two clauses.  The proof route diverges from Stacks only inside clause (2); see that theorem. -/
@[stacks 0BMA "clause (1)"]
theorem puncturedSpectrumPurity_of_isRegularLocalRing
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : 2 ≤ ringKrullDim A) :
    PuncturedSpectrumPurity A := by
  have : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  have : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  exact puncturedSpectrumPurity_of_finiteNormalPuncturedEtalePurity A
    (le_trans (by norm_num) hdim) (finiteNormalPuncturedEtalePurity_of_isRegularLocalRing A hdim)

/-- **Zariski--Nagata purity, Stacks Tag `0BMB`**, affine pointwise form, with no hypotheses.

This discharges the two inputs of `zariskiNagataPurity_of_etaleNormalAscent`: `033C` by
`IsStacksNormalRing.of_etale` and `0BMA` by
`finiteNormalPuncturedEtalePurity_of_isRegularLocalRing`.
Proof route: the strong induction on the height and the étale-local finite model of the Stacks
proof (`zariskiNagataPurity_of_etaleNormalAscent`, `hasZariskiNagataPurityAt_of_lowerHeight`). It
diverges from Stacks in two places: the final descent of étaleness is done on local rings (Kähler
differentials and Tor-free tensor products) instead of with Descent, Lemma 35.23.31 / Tag `02VN`,
and inside `0BMA`, whose input here is not proved by the Stacks proof (completion descent and an
elementary formal lifting replace `0BLL`/`0BLH` and `0BM6`/`0EKS`); see
`finiteNormalPuncturedEtalePurity_of_isRegularLocalRing` and `AXIOMS.md`. -/
@[stacks 0BMB "affine, pointwise"]
theorem zariskiNagataPurity (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    ZariskiNagataPurity R S :=
  zariskiNagataPurity_of_etaleNormalAscent (fun _ C _ _ _ _ h ↦ IsStacksNormalRing.of_etale C h)
    (fun A _ _ h ↦ finiteNormalPuncturedEtalePurity_of_isRegularLocalRing A h) R S

#print axioms puncturedSpectrumPurity_of_finiteNormalPuncturedEtalePurity
#print axioms puncturedSpectrumPurity_of_isRegularLocalRing_of_isAdicComplete
#print axioms finiteNormalPuncturedEtalePurity_of_isRegularLocalRing
#print axioms puncturedSpectrumPurity_of_isRegularLocalRing
#print axioms zariskiNagataPurity

#check @puncturedSpectrumPurity_of_finiteNormalPuncturedEtalePurity
#check @puncturedSpectrumPurity_of_isRegularLocalRing_dimension_two
#check @puncturedSpectrumPurity_of_isRegularLocalRing_of_isAdicComplete
#check @finiteNormalPuncturedEtalePurity_of_isRegularLocalRing
#check @puncturedSpectrumPurity_of_isRegularLocalRing
#check @zariskiNagataPurity

end Pcf.Stacks
