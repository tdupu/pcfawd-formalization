/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeMaximalSeparableNormalizationFactor

/-!
# Semilinear stability of the maximal separable subextension

The source's construction of the intermediate self-map in
`paper-p.tex`, Lemma `lem:pcf-transfer-charp`, requires that a
function-field endomorphism `h*` preserving the base field via `g*`
also preserves the maximal separable subfield. The proof maps a
separable annihilating polynomial through `g*`; its image annihilates
`h* a` over `g* K`, so `h* a` is separable over `K`.
-/

@[expose] public section

namespace Pcf

noncomputable section

theorem separableClosure_stable_under_commuting_fieldEndomorphisms
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (g : K →+* K) (h : E →+* E)
    (hcomm : h.comp (algebraMap K E) = (algebraMap K E).comp g)
    (x : separableClosure K E) :
    h (x : E) ∈ separableClosure K E := by
  let F := g.fieldRange
  let φ : K →+* F := g.rangeRestrictField
  have hsq : (algebraMap F E).comp φ = h.comp (algebraMap K E) := by
    ext a
    change algebraMap K E (g a) = h (algebraMap K E a)
    exact (congrArg (fun u : K →+* E => u a) hcomm).symm
  have hroot : Polynomial.aeval (h (x : E)) ((minpoly K (x : E)).map φ) = 0 := by
    rw [← Polynomial.map_aeval_eq_aeval_map hsq]
    rw [minpoly.aeval, map_zero]
  have hsepF : IsSeparable F (h (x : E)) :=
    Polynomial.Separable.of_dvd
      ((Polynomial.separable_map φ).mpr x.2)
      (minpoly.dvd F (h (x : E)) hroot)
  exact (mem_separableClosure_iff).mpr
    (IsSeparable.tower_top K hsepF)

/-- The restriction of a commuting function-field endomorphism to
the maximal separable intermediate field. -/
def separableClosureEndomorphism
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (g : K →+* K) (h : E →+* E)
    (hcomm : h.comp (algebraMap K E) = (algebraMap K E).comp g) :
    separableClosure K E →+* separableClosure K E where
  toFun x := ⟨h (x : E),
    separableClosure_stable_under_commuting_fieldEndomorphisms K E g h hcomm x⟩
  map_one' := Subtype.ext h.map_one
  map_mul' x y := Subtype.ext (h.map_mul x y)
  map_zero' := Subtype.ext h.map_zero
  map_add' x y := Subtype.ext (h.map_add x y)

/-- The restricted endomorphism agrees with the original one after
inclusion into the full function field. -/
theorem separableClosureEndomorphism_to_extension
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (g : K →+* K) (h : E →+* E)
    (hcomm : h.comp (algebraMap K E) = (algebraMap K E).comp g) :
    (algebraMap (separableClosure K E) E).comp
        (separableClosureEndomorphism K E g h hcomm) =
      h.comp (algebraMap (separableClosure K E) E) := by
  ext x
  rfl

/-- The restricted endomorphism covers the base-field
endomorphism in the actual intermediate-field tower. -/
theorem separableClosureEndomorphism_to_base
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (g : K →+* K) (h : E →+* E)
    (hcomm : h.comp (algebraMap K E) = (algebraMap K E).comp g) :
    (separableClosureEndomorphism K E g h hcomm).comp
        (algebraMap K (separableClosure K E)) =
      (algebraMap K (separableClosure K E)).comp g := by
  apply RingHom.ext
  intro a
  apply (algebraMap (separableClosure K E) E).injective
  change h (algebraMap K E a) = algebraMap K E (g a)
  exact congrArg (fun u : K →+* E => u a) hcomm

#print axioms separableClosure_stable_under_commuting_fieldEndomorphisms
#print axioms separableClosureEndomorphism
#print axioms separableClosureEndomorphism_to_extension
#print axioms separableClosureEndomorphism_to_base

end
end Pcf
