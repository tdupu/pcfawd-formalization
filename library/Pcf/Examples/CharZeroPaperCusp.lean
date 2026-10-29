module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Point-level cusp calculations for `paper.tex`, Example `ex:cusp`

The parametrization is bijective on field-valued points, including over fields
that are not algebraically closed. This does not make it a scheme isomorphism.
Normalization, finiteness and normalized branch loci require additional bridges.
-/

@[expose] public section

namespace Pcf.Examples.CharZeroPaperCusp

variable {K : Type*} [Field K]

/-- The affine map in `paper.tex`, Example `ex:cusp`. -/
def ambient (p : K × K) : K × K := (p.1 ^ 2, p.1 ^ 3 + p.2)

/-- Its restriction to the line `v = 0`. -/
def param (u : K) : K × K := (u ^ 2, u ^ 3)

def cusp : Set (K × K) := {p | p.2 ^ 2 = p.1 ^ 3}

theorem restriction (u : K) : ambient (u, 0) = param u := by
  simp [ambient, param]

theorem param_mem_cusp (u : K) : param u ∈ cusp := by
  change (u ^ 3) ^ 2 = (u ^ 2) ^ 3
  ring

/-- Every field-valued cusp point has a parameter; when `x ≠ 0` it is `y / x`. -/
theorem param_range : Set.range (param (K := K)) = cusp := by
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    exact param_mem_cusp u
  · rcases p with ⟨x, y⟩
    intro h
    change y ^ 2 = x ^ 3 at h
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 := by simpa using h
      subst y
      exact ⟨0, by simp [param]⟩
    · refine ⟨y / x, ?_⟩
      apply Prod.ext
      · change (y / x) ^ 2 = x
        field_simp
        linear_combination h
      · change (y / x) ^ 3 = y
        field_simp
        linear_combination y * h

/-- Bijectivity of normalization on points does not assert it is a scheme isomorphism. -/
theorem param_injective : Function.Injective (param (K := K)) := by
  intro u v huv
  have hs : u ^ 2 = v ^ 2 := congrArg Prod.fst huv
  have hc : u ^ 3 = v ^ 3 := congrArg Prod.snd huv
  by_cases hu : u = 0
  · subst u
    exact (by simpa using hs.symm : v = 0).symm
  · have hmul : (u - v) * u ^ 2 = 0 := by
      linear_combination hc - v * hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (pow_ne_zero _ hu))

/-- The intersection calculation in `ex:cusp`, with no geometric branch claim hidden in it. -/
theorem cusp_inter_coordinate : cusp (K := K) ∩ {p | p.1 = 0} = {(0, 0)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, cusp, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨rfl, by simpa using h⟩
  · rintro ⟨rfl, rfl⟩
    simp

end Pcf.Examples.CharZeroPaperCusp

#print axioms Pcf.Examples.CharZeroPaperCusp.restriction
#print axioms Pcf.Examples.CharZeroPaperCusp.param_mem_cusp
#print axioms Pcf.Examples.CharZeroPaperCusp.param_range
#print axioms Pcf.Examples.CharZeroPaperCusp.param_injective
#print axioms Pcf.Examples.CharZeroPaperCusp.cusp_inter_coordinate

-- Explicit types, including all implicit field hypotheses, for the evidence audit.
#check @Pcf.Examples.CharZeroPaperCusp.restriction
#check @Pcf.Examples.CharZeroPaperCusp.param_mem_cusp
#check @Pcf.Examples.CharZeroPaperCusp.param_range
#check @Pcf.Examples.CharZeroPaperCusp.param_injective
#check @Pcf.Examples.CharZeroPaperCusp.cusp_inter_coordinate
