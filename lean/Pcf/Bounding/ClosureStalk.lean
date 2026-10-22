/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimCoreDefs
public import Pcf.Bounding.RegularLocus
public import Pcf.Bounding.SchemeBridge

/-!
# Stalks of reduced point closures

For a point `d` of a scheme `X`, the reduced closure `D` of `d` has, at a
point `E_D` over `E`, the stalk `𝒪_{X,E} / 𝔭_d`, where `𝔭_d` is the prime of
the generization `d ⤳ E` (`closureStalk`). The identification is given by the
stalk map of the closed immersion, whose kernel is exactly `𝔭_d`. These are the
stalks of the exceptional divisors and of the periodic subvariety in the proof
of `latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

noncomputable section

set_option linter.style.haveILetI false

variable {X : Scheme.{u}} (d : X)


/-- A stalk specialization map between equal points preserves membership in
the maximal ideal. -/
theorem stalkSpecializes_mem_maximalIdeal_iff_of_eq {x x' : X} (hx : x = x')
    (h : x ⤳ x') (r : X.presheaf.stalk x') :
    (X.presheaf.stalkSpecializes h).hom r ∈ maximalIdeal (X.presheaf.stalk x) ↔
      r ∈ maximalIdeal (X.presheaf.stalk x') := by
  subst hx
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The kernel of the closed-immersion stalk map of a reduced point closure is
the prime of the generization. -/
theorem ker_pointClosure_stalkMap (E : (pointClosureIdealSheaf d).subscheme)
    (h : d ⤳ (pointClosureIdealSheaf d).subschemeι E) :
    RingHom.ker ((pointClosureIdealSheaf d).subschemeι.stalkMap E).hom =
      stalkGenerizationPrime X h := by
  let η := genericPoint (pointClosureIdealSheaf d).subscheme
  have hη : (pointClosureIdealSheaf d).subschemeι η = d :=
    pointClosureSubschemeι_genericPoint d
  have hηE : η ⤳ E :=
    (genericPoint_spec (pointClosureIdealSheaf d).subscheme).specializes trivial
  -- the specialization in `D` into the function field is injective
  have hinj : Function.Injective
      ((pointClosureIdealSheaf d).subscheme.presheaf.stalkSpecializes hηE).hom :=
    IsFractionRing.injective ((pointClosureIdealSheaf d).subscheme.presheaf.stalk E)
      (pointClosureIdealSheaf d).subscheme.functionField
  -- the closed-immersion stalk map at the generic point has kernel the maximal ideal
  have hker_gen : ∀ s : X.presheaf.stalk ((pointClosureIdealSheaf d).subschemeι η),
      ((pointClosureIdealSheaf d).subschemeι.stalkMap η).hom s = 0 ↔
        s ∈ maximalIdeal (X.presheaf.stalk ((pointClosureIdealSheaf d).subschemeι η)) := by
    intro s
    constructor
    · intro hs hunit
      have := hunit.map ((pointClosureIdealSheaf d).subschemeι.stalkMap η).hom
      rw [hs] at this
      exact not_isUnit_zero this
    · intro hs
      have hm := map_nonunit ((pointClosureIdealSheaf d).subschemeι.stalkMap η).hom s hs
      have hbot : maximalIdeal ((pointClosureIdealSheaf d).subscheme.presheaf.stalk η) = ⊥ := by
        change maximalIdeal (pointClosureIdealSheaf d).subscheme.functionField = ⊥
        exact maximalIdeal_eq_bot
      rw [hbot] at hm
      exact hm
  ext r
  rw [RingHom.mem_ker]
  change _ ↔ (X.presheaf.stalkSpecializes h).hom r ∈ maximalIdeal (X.presheaf.stalk d)
  have hsplit : X.presheaf.stalkSpecializes h =
      X.presheaf.stalkSpecializes (hηE.map (pointClosureIdealSheaf d).subschemeι.continuous) ≫
        X.presheaf.stalkSpecializes (specializes_of_eq hη.symm) :=
    (TopCat.Presheaf.stalkSpecializes_comp _ _ _).symm
  rw [hsplit, CommRingCat.comp_apply,
    stalkSpecializes_mem_maximalIdeal_iff_of_eq hη.symm, ← hker_gen,
    Scheme.Hom.stalkSpecializes_stalkMap_apply _ _ _ hηE]
  constructor
  · intro hr
    rw [hr, map_zero]
  · intro hr
    apply hinj
    rw [hr, map_zero]

/-- The stalk of the reduced closure of `d` at a point over `E` is
`closureStalk X h`. -/
def pointClosureStalkEquiv (E : (pointClosureIdealSheaf d).subscheme)
    (h : d ⤳ (pointClosureIdealSheaf d).subschemeι E) :
    closureStalk X h ≃+* (pointClosureIdealSheaf d).subscheme.presheaf.stalk E :=
  (Ideal.quotEquivOfEq (ker_pointClosure_stalkMap d E h).symm).trans
    ((pointClosureIdealSheaf d).subschemeι.stalkQuotientKerEquiv E)

@[simp]
theorem pointClosureStalkEquiv_mk (E : (pointClosureIdealSheaf d).subscheme)
    (h : d ⤳ (pointClosureIdealSheaf d).subschemeι E)
    (r : X.presheaf.stalk ((pointClosureIdealSheaf d).subschemeι E)) :
    pointClosureStalkEquiv d E h (Ideal.Quotient.mk _ r) =
      ((pointClosureIdealSheaf d).subschemeι.stalkMap E).hom r := by
  simp [pointClosureStalkEquiv]
  rfl

/-- The point-closure stalk equivalence at a point given up to equality. -/
def pointClosureStalkEquiv' (E : (pointClosureIdealSheaf d).subscheme) {E' : X}
    (hE : (pointClosureIdealSheaf d).subschemeι E = E') (h : d ⤳ E') :
    closureStalk X h ≃+* (pointClosureIdealSheaf d).subscheme.presheaf.stalk E := by
  subst hE
  exact pointClosureStalkEquiv d E h

theorem pointClosureStalkEquiv'_mk (E : (pointClosureIdealSheaf d).subscheme) {E' : X}
    (hE : (pointClosureIdealSheaf d).subschemeι E = E') (h : d ⤳ E')
    (r : X.presheaf.stalk E') :
    pointClosureStalkEquiv' d E hE h (Ideal.Quotient.mk _ r) =
      ((pointClosureIdealSheaf d).subschemeι.stalkMap E).hom
        ((X.presheaf.stalkCongr (.of_eq hE)).inv.hom r) := by
  subst hE
  simp only [pointClosureStalkEquiv', pointClosureStalkEquiv_mk]
  congr 1
  simp [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.stalkSpecializes_refl]

/-- **Naturality.** Under the point-closure stalk equivalences, the stalk map of
the induced map of reduced closures is `stalkGenerizationQuotientMap`. -/
theorem pointClosureStalkEquiv_naturality {Y : Scheme.{u}} (f : X ⟶ Y)
    (E : (pointClosureIdealSheaf d).subscheme)
    (h : d ⤳ (pointClosureIdealSheaf d).subschemeι E)
    (x : closureStalk Y (h.map f.continuous)) :
    ((pointClosureSubschemeMap f d (f d) rfl).stalkMap E).hom
        (pointClosureStalkEquiv' (f d) (pointClosureSubschemeMap f d (f d) rfl E)
          (by rw [← Scheme.Hom.comp_apply, pointClosureSubschemeMap_subschemeι,
            Scheme.Hom.comp_apply]) (h.map f.continuous) x) =
      pointClosureStalkEquiv d E h (stalkGenerizationQuotientMap f h x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [pointClosureStalkEquiv'_mk]
  change _ = pointClosureStalkEquiv d E h (Ideal.Quotient.mk _ ((f.stalkMap _).hom r))
  rw [pointClosureStalkEquiv_mk]
  have hcomm := pointClosureSubschemeMap_subschemeι f d (f d) rfl
  have key := Scheme.Hom.stalkMap_congr_hom _ _ hcomm E
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at key
  have key2 := congrArg (fun φ => (Y.presheaf.stalkCongr (.of_eq (by
      rw [← Scheme.Hom.comp_apply, pointClosureSubschemeMap_subschemeι,
        Scheme.Hom.comp_apply] :
      (pointClosureIdealSheaf (f d)).subschemeι
        (pointClosureSubschemeMap f d (f d) rfl E) =
        f ((pointClosureIdealSheaf d).subschemeι E)))).inv ≫ φ) key
  erw [Iso.inv_hom_id_assoc] at key2
  have := congrArg (fun φ => φ.hom r) key2
  simpa only [CommRingCat.comp_apply] using this

#print axioms ker_pointClosure_stalkMap
#print axioms pointClosureStalkEquiv
#print axioms pointClosureStalkEquiv_mk
#print axioms pointClosureStalkEquiv'_mk
#print axioms pointClosureStalkEquiv_naturality

end
end Pcf
