/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeSemilinearIntegralClosureMap

/-!
# Semilinear maps between integral-closure charts

For an affine open `U` and its affine inverse image under a finite
self-map, the two coordinate rings differ. A commuting map of the
base rings and common function field carries the integral closure
on `U` to the integral closure on its inverse image. The map is
finite when the base affine map and the target integral-closure
chart are finite. These are the local maps that must be glued to
construct the intermediate normalization self-map in
`paper-p.tex`, Lemma `lem:pcf-transfer-charp`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Pcf

noncomputable section

/-- A semilinear field endomorphism carries integral elements over
`R` to integral elements over `S`. -/
theorem semilinear_integralClosure_map_mem
    (R S L : Type*) [CommRing R] [CommRing S] [Field L]
    [Algebra R L] [Algebra S L]
    (φ : R →+* S) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap S L).comp φ)
    (x : integralClosure R L) :
    IsIntegral S (h (x : L)) :=
  IsIntegral.map_of_comp_eq φ h hcomm.symm x.2

/-- The local map between the integral-closure rings of two affine
charts, induced by the generic-field endomorphism. -/
def semilinearIntegralClosureBaseChange
    (R S L : Type*) [CommRing R] [CommRing S] [Field L]
    [Algebra R L] [Algebra S L]
    (φ : R →+* S) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap S L).comp φ) :
    integralClosure R L →+* integralClosure S L where
  toFun x := ⟨h (x : L), semilinear_integralClosure_map_mem R S L φ h hcomm x⟩
  map_one' := Subtype.ext h.map_one
  map_mul' x y := Subtype.ext (h.map_mul x y)
  map_zero' := Subtype.ext h.map_zero
  map_add' x y := Subtype.ext (h.map_add x y)

/-- The local integral-closure map agrees with `h` in the common
function field. -/
theorem semilinearIntegralClosureBaseChange_to_field
    (R S L : Type*) [CommRing R] [CommRing S] [Field L]
    [Algebra R L] [Algebra S L]
    (φ : R →+* S) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap S L).comp φ) :
    (algebraMap (integralClosure S L) L).comp
        (semilinearIntegralClosureBaseChange R S L φ h hcomm) =
      h.comp (algebraMap (integralClosure R L) L) := by
  ext x
  rfl

/-- The local integral-closure map lies over the base affine map. -/
theorem semilinearIntegralClosureBaseChange_to_base
    (R S L : Type*) [CommRing R] [CommRing S] [Field L]
    [Algebra R L] [Algebra S L]
    (φ : R →+* S) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap S L).comp φ) :
    (semilinearIntegralClosureBaseChange R S L φ h hcomm).comp
        (algebraMap R (integralClosure R L)) =
      (algebraMap S (integralClosure S L)).comp φ := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  change h (algebraMap R L r) = algebraMap S L (φ r)
  exact congrArg (fun u : R →+* L => u r) hcomm

/-- The chart maps respect composition. In particular, maps on
overlapping affine charts agree after restriction, the algebraic
compatibility required for gluing. -/
theorem semilinearIntegralClosureBaseChange_comp
    (R S T L : Type*) [CommRing R] [CommRing S] [CommRing T] [Field L]
    [Algebra R L] [Algebra S L] [Algebra T L]
    (φ : R →+* S) (ψ : S →+* T) (h k : L →+* L)
    (hφ : h.comp (algebraMap R L) = (algebraMap S L).comp φ)
    (hψ : k.comp (algebraMap S L) = (algebraMap T L).comp ψ) :
    let hcomp : (k.comp h).comp (algebraMap R L) =
        (algebraMap T L).comp (ψ.comp φ) := by
      apply RingHom.ext
      intro r
      change k (h (algebraMap R L r)) = algebraMap T L (ψ (φ r))
      have hh := congrArg (fun u : R →+* L => u r) hφ
      change h (algebraMap R L r) = algebraMap S L (φ r) at hh
      rw [hh]
      have hk := congrArg (fun u : S →+* L => u (φ r)) hψ
      exact hk
    semilinearIntegralClosureBaseChange R T L (ψ.comp φ) (k.comp h) hcomp =
      (semilinearIntegralClosureBaseChange S T L ψ k hψ).comp
        (semilinearIntegralClosureBaseChange R S L φ h hφ) := by
  dsimp only
  apply RingHom.ext
  intro x
  apply Subtype.ext
  rfl

/-- The local integral-closure chart map is finite if the base chart
map is finite and the source normalization chart is module-finite. -/
theorem semilinearIntegralClosureBaseChange_finite
    (R S L : Type*) [CommRing R] [CommRing S] [Field L]
    [Algebra R L] [Algebra S L]
    [Module.Finite S (integralClosure S L)]
    (φ : R →+* S) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap S L).comp φ)
    (hφ : φ.Finite) :
    (semilinearIntegralClosureBaseChange R S L φ h hcomm).Finite := by
  let iR := algebraMap R (integralClosure R L)
  let iS := algebraMap S (integralClosure S L)
  have hiS : iS.Finite := RingHom.finite_algebraMap.mpr inferInstance
  have hc : ((semilinearIntegralClosureBaseChange R S L φ h hcomm).comp iR).Finite := by
    rw [semilinearIntegralClosureBaseChange_to_base]
    exact RingHom.Finite.comp hiS hφ
  exact RingHom.Finite.of_comp_finite hc

/-- Hence its map of affine normalization charts is a finite scheme
morphism. -/
theorem semilinearIntegralClosureBaseChange_spec_isFinite
    (R S L : Type*) [CommRing R] [CommRing S] [Field L]
    [Algebra R L] [Algebra S L]
    [Module.Finite S (integralClosure S L)]
    (φ : R →+* S) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap S L).comp φ)
    (hφ : φ.Finite) :
    IsFinite (Spec.map (CommRingCat.ofHom
      (semilinearIntegralClosureBaseChange R S L φ h hcomm))) := by
  exact (IsFinite.SpecMap_iff (CommRingCat.ofHom
    (semilinearIntegralClosureBaseChange R S L φ h hcomm))).mpr
      (semilinearIntegralClosureBaseChange_finite R S L φ h hcomm hφ)

#print axioms semilinear_integralClosure_map_mem
#print axioms semilinearIntegralClosureBaseChange
#print axioms semilinearIntegralClosureBaseChange_to_field
#print axioms semilinearIntegralClosureBaseChange_to_base
#print axioms semilinearIntegralClosureBaseChange_comp
#print axioms semilinearIntegralClosureBaseChange_finite
#print axioms semilinearIntegralClosureBaseChange_spec_isFinite

end
end Pcf
