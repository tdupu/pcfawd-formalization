/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperCuspGeometry

/-!
# The source line of `ex:cusp` in `paper.tex` is the closed subscheme `V(v)`

`CharZeroPaperCuspGeometry.sourceLine` is the scheme morphism `Spec k[t] → 𝔸²`,
`t ↦ (t, 0)`. Its pullback `k[u, v] → k[t]` is surjective with kernel `(v)`, so the
morphism is a closed immersion whose image is exactly `V(v)`.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperCuspSourceLine

open CategoryTheory AlgebraicGeometry Polynomial
open Pcf.Examples.CharZeroPaperCuspGeometry

universe u
variable (k : Type u) [Field k]

/-- The pullback `u ↦ t, v ↦ 0` of the source line. -/
def sourceLinePullback : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval ![(X : Polynomial k), 0]

/-- The ideal `(v)` of the source line. -/
def sourceLineIdeal : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {MvPolynomial.X 1}

theorem sourceLinePullback_surjective : Function.Surjective (sourceLinePullback k) := by
  intro p
  refine ⟨Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) p, ?_⟩
  rw [← AlgHom.comp_apply]
  have : (sourceLinePullback k).comp
      (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k)) = AlgHom.id k _ := by
    apply Polynomial.algHom_ext
    simp [sourceLinePullback]
  rw [this, AlgHom.id_apply]

/-- Every polynomial differs from the lift of its restriction to the line by a
multiple of `v`. -/
theorem sub_mem_sourceLineIdeal (p : MvPolynomial (Fin 2) k) :
    p - Polynomial.aeval (MvPolynomial.X 0) (sourceLinePullback k p) ∈ sourceLineIdeal k := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sourceLinePullback]
  | add p q hp hq =>
    convert Ideal.add_mem _ hp hq using 1
    simp only [map_add]; ring
  | mul_X p i hp =>
    have h1 := Ideal.mul_mem_right (MvPolynomial.X i) _ hp
    fin_cases i
    · convert h1 using 1
      simp [sourceLinePullback]; ring
    · have h2 : Polynomial.aeval (MvPolynomial.X 0) (sourceLinePullback k p) *
          (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈ sourceLineIdeal k :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      convert Ideal.add_mem _ h1 h2 using 1
      simp [sourceLinePullback]; ring

theorem sourceLinePullback_ker :
    RingHom.ker (sourceLinePullback k).toRingHom = sourceLineIdeal k := by
  apply le_antisymm
  · intro p hp
    have := sub_mem_sourceLineIdeal k p
    change sourceLinePullback k p = 0 at hp
    rwa [hp, map_zero, sub_zero] at this
  · rw [sourceLineIdeal, Ideal.span_le, Set.singleton_subset_iff]
    change sourceLinePullback k _ = 0
    simp [sourceLinePullback]

theorem sourceLine_eq :
    sourceLine k = Spec.map (CommRingCat.ofHom (sourceLinePullback k).toRingHom) := rfl

/-- The source line `t ↦ (t, 0)` of `ex:cusp` is a closed immersion. -/
instance sourceLine_isClosedImmersion : IsClosedImmersion (sourceLine k) :=
  IsClosedImmersion.spec_of_surjective _ (sourceLinePullback_surjective k)

/-- `ex:cusp`: the source line `Spec k[t] → 𝔸²`, `t ↦ (t, 0)`, is a closed immersion
with image exactly `V(v)`.

Manuscript: `ex:cusp` (Example 6.5). -/
theorem sourceLine_isClosedImmersion_range :
    IsClosedImmersion (sourceLine k) ∧
      Set.range (sourceLine k) =
        PrimeSpectrum.zeroLocus {(MvPolynomial.X 1 : MvPolynomial (Fin 2) k)} := by
  refine ⟨inferInstance, ?_⟩
  change Set.range (PrimeSpectrum.comap (sourceLinePullback k).toRingHom) = _
  rw [_root_.range_comap_of_surjective _ _ (sourceLinePullback_surjective k),
    sourceLinePullback_ker, sourceLineIdeal, PrimeSpectrum.zeroLocus_span]

end Pcf.Examples.CharZeroPaperCuspSourceLine

#print axioms Pcf.Examples.CharZeroPaperCuspSourceLine.sourceLinePullback_ker
#print axioms Pcf.Examples.CharZeroPaperCuspSourceLine.sourceLine_isClosedImmersion
#print axioms Pcf.Examples.CharZeroPaperCuspSourceLine.sourceLine_isClosedImmersion_range
