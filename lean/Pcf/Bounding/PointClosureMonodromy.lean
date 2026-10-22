/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PointClosureFunctionField

/-!
# Prime-to-characteristic monodromy on actual point-closure fields

This file transports an all-centre monodromy certificate across the
canonical field equivalences from affine quotient fraction fields to
the generic stalk fields of the reduced point closures.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- Prime-to-`p` monodromy is invariant under an isomorphism of field
extensions. The two field isomorphisms are required to commute with
the extension embeddings. -/
theorem isPrimeToPMonodromy_of_equiv_equiv
    (p : ℕ) (F E F' E' : Type u)
    [Field F] [Field E] [Field F'] [Field E']
    [Algebra F E] [Algebra F' E']
    (f : F ≃+* F') (g : E ≃+* E')
    (hcomp : (algebraMap F' E').comp f.toRingHom =
      g.toRingHom.comp (algebraMap F E))
    (hmono : IsPrimeToPMonodromy.{u, u, u} p F E) :
    IsPrimeToPMonodromy.{u, u, u} p F' E' := by
  obtain ⟨C⟩ := hmono
  letI : Field C.Closure := C.field
  letI : Algebra F C.Closure := C.algebra
  letI : FiniteDimensional F C.Closure := C.finiteClosure
  letI : IsGalois F C.Closure := C.isGaloisClosure
  letI : Algebra F' C.Closure :=
    ((algebraMap F C.Closure).comp f.symm.toRingHom).toAlgebra
  have hcompC : (algebraMap F' C.Closure).comp f.toRingHom =
      (RingEquiv.refl C.Closure).toRingHom.comp
        (algebraMap F C.Closure) := by
    ext x
    change (algebraMap F C.Closure) (f.symm (f x)) =
      (algebraMap F C.Closure) x
    rw [f.symm_apply_apply]
  letI : IsGalois F' C.Closure :=
    IsGalois.of_equiv_equiv (F := F) (E := C.Closure)
      (M := F') (N := C.Closure)
      (f := f) (g := RingEquiv.refl C.Closure) hcompC
  have hrank : Module.finrank F C.Closure =
      Module.finrank F' C.Closure :=
    Algebra.finrank_eq_of_equiv_equiv f (RingEquiv.refl C.Closure) hcompC
  letI : FiniteDimensional F' C.Closure :=
    FiniteDimensional.of_finrank_pos (hrank ▸ Module.finrank_pos)
  let emb : E' →ₐ[F'] C.Closure :=
    { toRingHom := C.embedding.toRingHom.comp g.symm.toRingHom
      commutes' := by
        intro x
        have hc : algebraMap F' E' x =
            g (algebraMap F E (f.symm x)) := by
          have hh := congrArg
            (fun h : F →+* E' => h (f.symm x)) hcomp
          change algebraMap F' E' (f (f.symm x)) =
            g (algebraMap F E (f.symm x)) at hh
          simpa only [f.apply_symm_apply] using hh
        have hcf : algebraMap F C.Closure (f.symm x) =
            algebraMap F' C.Closure x := by
          rfl
        change C.embedding (g.symm (algebraMap F' E' x)) =
          algebraMap F' C.Closure x
        rw [hc, g.symm_apply_apply]
        rw [C.embedding.commutes]
        exact hcf }
  exact isPrimeToPMonodromy_of_embedding_into_galois
    p F' E' C.Closure emb (hrank ▸ C.coprimeDegree)

/-- The restriction of a morphism to reduced point closures sends the
source generic point to the image closure's generic point. -/
theorem pointClosureSubschemeMap_map_genericPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (pointClosureSubschemeMap f x (f x) rfl)
      (genericPoint (pointClosureIdealSheaf x).subscheme) =
    genericPoint (pointClosureIdealSheaf (f x)).subscheme := by
  let I := pointClosureIdealSheaf x
  let J := pointClosureIdealSheaf (f x)
  let g := pointClosureSubschemeMap f x (f x) rfl
  apply J.subschemeι.isEmbedding.injective
  have hcomm := congrArg
    (fun h : I.subscheme ⟶ Y => h (genericPoint I.subscheme))
    (pointClosureSubschemeMap_subschemeι f x (f x) rfl)
  change J.subschemeι (g (genericPoint I.subscheme)) =
    J.subschemeι (genericPoint J.subscheme)
  rw [pointClosureSubschemeι_genericPoint]
  calc
    J.subschemeι (g (genericPoint I.subscheme)) =
        f (I.subschemeι (genericPoint I.subscheme)) := by
      simpa only [Scheme.Hom.comp_apply] using hcomm
    _ = f x := by rw [pointClosureSubschemeι_genericPoint]

/-- The actual generic stalk map on reduced point closures agrees with
the quotient of the ambient affine coordinate map. -/
theorem pointClosure_genericStalk_quotient_square
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (U : Y.affineOpens) (x : X)
    (hx : x ∈ (finitePreimageAffine f U : X.Opens)) :
    let V := finitePreimageAffine f U
    let I := pointClosureIdealSheaf x
    let J := pointClosureIdealSheaf (f x)
    let H : J ≤ I.map f := pointClosureIdealSheaf_le_map_of_apply_eq f x (f x) rfl
    let g := I.subschemeMap J f H
    let hle := I.subschemeMap_ideal_le J f H U V le_rfl
    let hX : genericPoint I.subscheme ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens) := by
      change I.subschemeι (genericPoint I.subscheme) ∈ (V : X.Opens)
      rw [pointClosureSubschemeι_genericPoint]
      exact hx
    let hY : g (genericPoint I.subscheme) ∈
        J.subschemeι ⁻¹ᵁ (U : Y.Opens) := by
      exact (I.subschemeMap_preimage_le J f H U V le_rfl) hX
    letI : Algebra (Γ(Y, U) ⧸ J.ideal U)
        (J.subscheme.presheaf.stalk (g (genericPoint I.subscheme))) :=
      J.quotientStalkAlgebra U (g (genericPoint I.subscheme)) hY
    letI : Algebra (Γ(X, V) ⧸ I.ideal V)
        I.subscheme.functionField :=
      I.quotientStalkAlgebra V (genericPoint I.subscheme) hX
    (g.stalkMap (genericPoint I.subscheme)).hom.comp
        (algebraMap (Γ(Y, U) ⧸ J.ideal U)
          (J.subscheme.presheaf.stalk (g (genericPoint I.subscheme)))) =
      (algebraMap (Γ(X, V) ⧸ I.ideal V)
        I.subscheme.functionField).comp
        (Ideal.quotientMap (I.ideal V) (f.appLE U V le_rfl).hom hle) := by
  let V := finitePreimageAffine f U
  let I := pointClosureIdealSheaf x
  let J := pointClosureIdealSheaf (f x)
  let H : J ≤ I.map f := pointClosureIdealSheaf_le_map_of_apply_eq f x (f x) rfl
  let g := I.subschemeMap J f H
  let hle := I.subschemeMap_ideal_le J f H U V le_rfl
  let map_le := I.subschemeMap_preimage_le J f H U V le_rfl
  have hX : genericPoint I.subscheme ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens) := by
    change I.subschemeι (genericPoint I.subscheme) ∈ (V : X.Opens)
    rw [pointClosureSubschemeι_genericPoint]
    exact hx
  have hY : g (genericPoint I.subscheme) ∈
      J.subschemeι ⁻¹ᵁ (U : Y.Opens) := map_le hX
  letI : Algebra (Γ(Y, U) ⧸ J.ideal U)
      (J.subscheme.presheaf.stalk (g (genericPoint I.subscheme))) :=
    J.quotientStalkAlgebra U (g (genericPoint I.subscheme)) hY
  letI : Algebra (Γ(X, V) ⧸ I.ideal V)
      I.subscheme.functionField :=
    I.quotientStalkAlgebra V (genericPoint I.subscheme) hX
  have hsquare := J.stalkMap_comp_quotientStalkAlgebraMap I g U V
    map_le (genericPoint I.subscheme) hX hY
  rw [J.quotientAppLE_subschemeMap_eq_quotientMap I f H U V le_rfl]
    at hsquare
  simpa only [Scheme.functionField] using hsquare

#print axioms isPrimeToPMonodromy_of_equiv_equiv
#print axioms pointClosureSubschemeMap_map_genericPoint
#print axioms pointClosure_genericStalk_quotient_square

end Pcf
