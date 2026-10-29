/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.BasilicaAffine
public import Pcf.Examples.PaperP.QuadricConeSquaringEtale
/-!
# The exact affine étale locus of the basilica map

For the finite affine chart in `paper-p.tex`, Example `ex:basilica`, the
actual scheme map is étale precisely away from the scheme point `0`; the
image of that non-étale locus is the scheme point `-1`. The proof transports
the standard étale squaring presentation through the target translation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial
namespace Pcf.Examples.PaperP.BasilicaAffine
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
variable (k : Type*) [Field k] [CharZero k]
/-- Target translation by `-1` is an affine scheme isomorphism. -/
noncomputable def translationIso : Spec (.of k[X]) ≅ Spec (.of k[X]) :=
  Scheme.Spec.mapIso (algEquivAevalXAddC (-1 : k)).toRingEquiv.toCommRingCatIso.op

omit [CharZero k] in
/-- The actual affine basilica map factors through squaring and translation. -/
theorem schemeMap_factor :
    schemeMap k = QuadricConeRestriction.schemeMap k ≫ (translationIso k).hom := by
  unfold schemeMap QuadricConeRestriction.schemeMap translationIso
  change Spec.map _ = Spec.map _ ≫ Spec.map
    (CommRingCat.ofHom (algEquivAevalXAddC (-1 : k)).toRingEquiv.toRingHom)
  rw [← Spec.map_comp]
  exact congrArg Spec.map (congrArg (fun f : k[X] →ₐ[k] k[X] => CommRingCat.ofHom f.toRingHom)
    (coordinateMap_eq_square_comp_translation k))

/-- The map restricted to the source open `D(t)` is étale. -/
theorem schemeMap_sourceAway_etale :
    Etale ((QuadricConeRestriction.sourceOpen k).ι ≫ schemeMap k) := by
  rw [schemeMap_factor, ← Category.assoc]
  letI : Etale ((QuadricConeRestriction.sourceOpen k).ι ≫
      QuadricConeRestriction.schemeMap k) :=
    QuadricConeRestriction.schemeMap_sourceAway_etale k
  infer_instance

omit [CharZero k] in
/-- The only prime of the affine line containing `t` is the origin. -/
theorem X_mem_iff_eq_zero (p : Spec (.of k[X])) :
    X ∈ p.asIdeal ↔ p = closedPoint k 0 := by
  have hmax : (closedPoint k 0).asIdeal.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (evalRingHom (0 : k)) (fun a => ⟨C a, by simp⟩)
  constructor
  · intro hx
    apply PrimeSpectrum.ext
    symm
    apply hmax.eq_of_le p.isPrime.ne_top
    change RingHom.ker (evalRingHom (0 : k)) ≤ p.asIdeal
    rw [ker_evalRingHom]
    simp only [map_zero, sub_zero]
    exact (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hx
  · rintro rfl
    change eval (0 : k) X = 0
    simp

/-- Every scheme point outside the origin is étale. -/
theorem etaleAt_of_ne_zero (p : Spec (.of k[X])) (hp : p ≠ closedPoint k 0) :
    Pcf.Stacks.IsStacksEtaleAt (schemeMap k) p := by
  have hpX : X ∉ p.asIdeal := fun h => hp ((X_mem_iff_eq_zero k p).mp h)
  let U := QuadricConeRestriction.sourceOpen k
  exact (Pcf.Stacks.isStacksEtaleAt_comp_iff_of_isOpenImmersion
    (f := schemeMap k) U.ι ⟨p, hpX⟩).mp
      (Pcf.Stacks.forall_isStacksEtaleAt_iff.mpr (schemeMap_sourceAway_etale k) ⟨p, hpX⟩)

omit [CharZero k] in
/-- The nonreduced fibre over `-1` excludes global étaleness. -/
theorem schemeMap_not_etale : ¬ Etale (schemeMap k) := by
  intro he
  have hr := (HasRingHomProperty.Spec_iff (P := @Etale)).mp he
  change (coordinateMap k).toRingHom.Etale at hr
  letI : Algebra k[X] k[X] := (coordinateMap k).toRingHom.toAlgebra
  haveI : Algebra.Etale k[X] k[X] := RingHom.etale_algebraMap.mp hr
  haveI : Algebra.EssFiniteType k[X] k[X] := (coordinateMap_finite k).finiteType.essFiniteType
  haveI : (RingHom.ker (evalRingHom (-1 : k))).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨C a, by simp⟩)
  have hrad := Algebra.FormallyUnramified.isRadical_map_isMaximal
    k[X] k[X] (RingHom.ker (evalRingHom (-1 : k)))
  exact minusOne_fiber_not_isReduced k ((Ideal.isRadical_iff_quotient_reduced _).mp hrad)

/-- The origin is a non-étale point of the actual scheme map. -/
theorem not_etaleAt_zero : ¬ Pcf.Stacks.IsStacksEtaleAt (schemeMap k) (closedPoint k 0) := by
  intro h0
  apply schemeMap_not_etale k
  apply Pcf.Stacks.forall_isStacksEtaleAt_iff.mp
  intro p
  by_cases hp : p = closedPoint k 0
  · simpa [hp] using h0
  · exact etaleAt_of_ne_zero k p hp

/-- The actual affine scheme map is étale exactly off the origin. -/
theorem etaleAt_iff_ne_zero (p : Spec (.of k[X])) :
    Pcf.Stacks.IsStacksEtaleAt (schemeMap k) p ↔ p ≠ closedPoint k 0 := by
  constructor
  · intro h hp
    exact not_etaleAt_zero k (hp ▸ h)
  · exact etaleAt_of_ne_zero k p

/-- The full pointwise non-étale locus is the singleton origin.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem nonEtaleLocus_eq_zero :
    {p : Spec (.of k[X]) | ¬ Pcf.Stacks.IsStacksEtaleAt (schemeMap k) p} =
      {closedPoint k 0} := by
  ext p
  simp [etaleAt_iff_ne_zero]

/-- The image of the non-étale locus is the singleton `-1`. -/
theorem nonEtaleImage_eq_minusOne :
    schemeMap k '' {p | ¬ Pcf.Stacks.IsStacksEtaleAt (schemeMap k) p} =
      {closedPoint k (-1)} := by
  rw [nonEtaleLocus_eq_zero, Set.image_singleton, zero_to_minusOne]
#print axioms schemeMap_factor
#print axioms schemeMap_sourceAway_etale
#print axioms etaleAt_iff_ne_zero
#print axioms nonEtaleLocus_eq_zero
#print axioms nonEtaleImage_eq_minusOne

end Pcf.Examples.PaperP.BasilicaAffine
