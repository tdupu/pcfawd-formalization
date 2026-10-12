/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Fiber
import Pcf.Stacks.Abhyankar.DVR

/-!
# The local DVR conclusion in Abhyankar's lemma

Stacks Project Tag `0BRM` starts with an extension of DVRs, makes a finite ramified base
change whose ramification index is divisible by the original tame index, and concludes
formal smoothness for the adic topology.  In the final reduced diagram, multiplicativity
of ramification indices gives index one and the residue extension is separable.

Mathlib does not currently express formal smoothness for an adic topology.  This file proves
the strongest algebraic conclusion available from the literal final-diagram hypotheses:
the resulting finite extension of local DVRs is finite étale.  The proof passes through the
actual top prime, not through a global unramifiedness assumption:

1. cancel the two total ramification indices;
2. use residue separability to obtain `Algebra.IsUnramifiedAt`;
3. combine finite presentation and flatness to obtain `Algebra.IsEtaleAt`;
4. use locality of the target to promote étaleness at its closed point to global étaleness.

This formalizes the last implication of `0BRM`.  The preceding reductions adjoining an
`e`th root of the unit and passing through the standard root DVR remain separate steps.
-/

open IsLocalRing

universe u v w

namespace Pcf.Stacks

/-- For a finitely presented algebra whose target is local, étaleness at the closed point
already implies étaleness everywhere.  Indeed, the étale locus is open and every open
neighbourhood of the closed point of a local spectrum is the whole spectrum. -/
theorem etale_of_isEtaleAt_maximalIdeal
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] [Algebra.FinitePresentation R S]
    [Algebra.IsEtaleAt R (maximalIdeal S)] :
    Algebra.Etale R S := by
  rw [← Algebra.etaleLocus_eq_univ_iff_etale]
  let U : TopologicalSpace.Opens (PrimeSpectrum S) :=
    ⟨Algebra.etaleLocus R S, Algebra.isOpen_etaleLocus⟩
  have hclosed : IsLocalRing.closedPoint S ∈ U := by
    exact (inferInstance : Algebra.IsEtaleAt R (maximalIdeal S))
  have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hclosed
  change (U : Set (PrimeSpectrum S)) = Set.univ
  rw [hU]
  rfl

/-- The flat, finitely presented strengthening of the local unramified conclusion already
proved in `DVR.lean`: equality of the total and intermediate ramification indices gives
étaleness at the actual top prime. -/
theorem isEtaleAt_of_ramificationIdx_total_eq_intermediate
    (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Finite R S] [Module.Flat S T] [Algebra.FinitePresentation S T]
    (r : Ideal T) [r.IsPrime]
    [Algebra.HasSeparableResidueFieldsAt S T (r.under S)]
    (h : r.ramificationIdx R = (r.under S).ramificationIdx R) :
    Algebra.IsEtaleAt S r := by
  let _ : Algebra.IsUnramifiedAt S r :=
    isUnramifiedAt_of_ramificationIdx_total_eq_intermediate R S T r h
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat r

/-- The faithful finite-DVR final step of Stacks Tag `0BRM`.

Here `R → S → T` is the final tower of local DVRs.  The displayed equality is exactly
the ramification-index equality obtained in the tag from the two tower formulas.  Locality
identifies the prime under `maximalIdeal T` with `maximalIdeal S`; separability at that
closed point is the tag's residue-field hypothesis.  Finiteness supplies finite
presentation, while injectivity of the DVR extension supplies torsion-freeness and hence
flatness.  The conclusion is algebraic finite étaleness, which in particular supplies
ordinary formal smoothness and formal unramifiedness. -/
theorem etale_of_dvr_ramificationIdx_total_eq
    (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [IsDomain R] [IsDomain S] [IsDomain T]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Finite R S] [Module.Finite S T] [FaithfulSMul S T]
    [IsLocalHom (algebraMap S T)]
    [Algebra.HasSeparableResidueFieldsAt S T ((maximalIdeal T).under S)]
    (h : (maximalIdeal T).ramificationIdx R =
      (maximalIdeal S).ramificationIdx R) :
    Algebra.Etale S T := by
  let _ : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let _ : Module.Flat S T := inferInstance
  have hunder : (maximalIdeal T).under S = maximalIdeal S :=
    IsLocalRing.maximalIdeal_comap (algebraMap S T)
  let _ : Algebra.IsEtaleAt S (maximalIdeal T) :=
    isEtaleAt_of_ramificationIdx_total_eq_intermediate R S T (maximalIdeal T) <| by
      simpa only [hunder] using h
  exact etale_of_isEtaleAt_maximalIdeal S T

#print axioms etale_of_isEtaleAt_maximalIdeal
#print axioms isEtaleAt_of_ramificationIdx_total_eq_intermediate
#print axioms etale_of_dvr_ramificationIdx_total_eq

end Pcf.Stacks
