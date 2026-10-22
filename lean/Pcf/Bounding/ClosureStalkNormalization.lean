/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalization
public import Pcf.Bounding.SchemeDynamics

/-!
# The normalization is an isomorphism at normal points

Let `ν : N ⟶ D` be an integral dominant morphism of integral schemes inducing
an isomorphism of generic stalks (for instance the absolute normalization
`Palomar.normalizationMap D`). At a point `z` whose image has an integrally
closed local ring, the stalk map of `ν` is an isomorphism: every germ of `N`
is a quotient of germs integral over the base, and integral elements of the
common function field already lie in the normal local ring. In the proof of
`latex/paper-p.tex`, Theorem `thm:allcodim-normal`, this identifies the local
ring of the normalized exceptional component with that of the component
itself at a point where the component is regular.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

noncomputable section

set_option linter.style.haveILetI false

variable {N D : Scheme.{u}} [IsIntegral N] [IsIntegral D] (ν : N ⟶ D)
  [IsIntegralHom ν] [IsDominant ν] [IsIso (ν.stalkMap (genericPoint N))]

omit [IsIntegralHom ν] in
/-- Elements of the stalk of `N` integral over a normal stalk of `D` come from
that stalk. -/
theorem stalkMap_exists_of_isIntegral (z : N)
    [IsIntegrallyClosed (D.presheaf.stalk (ν z))] (y : N.presheaf.stalk z)
    (hy : letI := (ν.stalkMap z).hom.toAlgebra
      IsIntegral (D.presheaf.stalk (ν z)) y) :
    ∃ σ, (ν.stalkMap z).hom σ = y := by
  let ηN := genericPoint N
  have hη : ν ηN = genericPoint D := map_genericPoint_eq_of_isDominant ν
  let g := ν.stalkMap ηN
  let Θ : N.presheaf.stalk ηN ⟶ D.presheaf.stalk (genericPoint D) :=
    inv g ≫ (D.presheaf.stalkCongr (.of_eq hη)).hom
  have hz : ηN ⤳ z := (genericPoint_spec N).specializes trivial
  have hcompat : ν.stalkMap z ≫ N.presheaf.stalkSpecializes hz ≫ Θ =
      D.presheaf.stalkSpecializes ((genericPoint_spec D).specializes trivial) := by
    rw [← Category.assoc, ← Scheme.Hom.stalkSpecializes_stalkMap]
    simp only [Θ, g, Category.assoc, IsIso.hom_inv_id_assoc,
      TopCat.Presheaf.stalkCongr_hom]
    exact TopCat.Presheaf.stalkSpecializes_comp _ _ _
  letI : Algebra (D.presheaf.stalk (ν z)) (N.presheaf.stalk z) := (ν.stalkMap z).hom.toAlgebra
  have hinjΘ : Function.Injective Θ.hom := by
    have : IsIso Θ := inferInstance
    exact (ConcreteCategory.bijective_of_isIso Θ).1
  have hinjS : Function.Injective (N.presheaf.stalkSpecializes hz).hom :=
    IsFractionRing.injective (N.presheaf.stalk z) N.functionField
  let ψ : N.presheaf.stalk z →+* D.functionField :=
    Θ.hom.comp (N.presheaf.stalkSpecializes hz).hom
  have hψ : (algebraMap (D.presheaf.stalk (ν z)) D.functionField).comp (RingHom.id _) =
      ψ.comp (algebraMap (D.presheaf.stalk (ν z)) (N.presheaf.stalk z)) := by
    rw [RingHom.comp_id]
    change (D.presheaf.stalkSpecializes ((genericPoint_spec D).specializes trivial)).hom = _
    rw [← hcompat]
    rfl
  have hint : IsIntegral (D.presheaf.stalk (ν z)) (ψ y) :=
    IsIntegral.map_of_comp_eq (RingHom.id _) ψ hψ hy
  obtain ⟨σ, hσ⟩ := (IsIntegrallyClosed.isIntegral_iff (K := D.functionField)).mp hint
  refine ⟨σ, ?_⟩
  apply hinjS
  apply hinjΘ
  change ψ ((ν.stalkMap z).hom σ) = ψ y
  rw [← hσ]
  exact (congrArg (fun φ => φ σ) hψ).symm

/-- Germs of sections over the preimage of an affine open come from a normal
stalk of the base. -/
theorem stalkMap_exists_germ {U : D.Opens} (hU : IsAffineOpen U) (z : N)
    (hzU : ν z ∈ U) [IsIntegrallyClosed (D.presheaf.stalk (ν z))] (c : Γ(N, ν ⁻¹ᵁ U)) :
    ∃ σ, (ν.stalkMap z).hom σ = N.presheaf.germ (ν ⁻¹ᵁ U) z hzU c := by
  apply stalkMap_exists_of_isIntegral ν z
  letI : Algebra Γ(D, U) Γ(N, ν ⁻¹ᵁ U) := (ν.app U).hom.toAlgebra
  have hc : IsIntegral Γ(D, U) c := ν.isIntegral_app U hU c
  letI := (ν.stalkMap z).hom.toAlgebra
  refine IsIntegral.map_of_comp_eq (D.presheaf.germ U (ν z) hzU).hom
    (N.presheaf.germ (ν ⁻¹ᵁ U) z hzU).hom ?_ hc
  ext a
  exact (Scheme.Hom.germ_stalkMap_apply ν U z hzU a).trans rfl

/-- **The stalk map is bijective at a normal point.** -/
theorem stalkMap_bijective_of_isIntegrallyClosed (z : N)
    [IsIntegrallyClosed (D.presheaf.stalk (ν z))] :
    Function.Bijective (ν.stalkMap z).hom := by
  refine ⟨stalkMap_injective_of_dominant_integral ν z, ?_⟩
  intro y
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show ν z ∈ (⊤ : D.Opens) from trivial)
  let V := ν ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage ν
  let zV : V := ⟨z, hzU⟩
  letI : Algebra Γ(N, V) (N.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk N.presheaf zV
  haveI : IsLocalization.AtPrime (N.presheaf.stalk z) (hV.primeIdealOf zV).asIdeal :=
    hV.isLocalization_stalk zV
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective
    (hV.primeIdealOf zV).asIdeal.primeCompl y
  have hgerm (c : Γ(N, V)) : ∃ σ, (ν.stalkMap z).hom σ = algebraMap Γ(N, V) _ c :=
    stalkMap_exists_germ ν hU z hzU c
  obtain ⟨β, hβ⟩ := hgerm b
  obtain ⟨σ, hσ⟩ := hgerm s
  have hsu : IsUnit ((ν.stalkMap z).hom σ) := by
    rw [hσ]
    exact IsLocalization.map_units (N.presheaf.stalk z) s
  have hσu : IsUnit σ := (isUnit_map_iff (ν.stalkMap z).hom σ).mp hsu
  refine ⟨β * hσu.unit⁻¹, ?_⟩
  rw [← hbs]
  change _ = IsLocalization.mk' (N.presheaf.stalk z) b s
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, map_mul, hβ, ← hσ, mul_assoc,
    ← map_mul, hσu.val_inv_mul, map_one, mul_one]

omit [IsIntegral D] [IsIntegralHom ν] [IsDominant ν]
  [IsIso (ν.stalkMap (genericPoint N))] in
/-- The map from a stalk of `D` to the function field of `N` through the
generic stalk isomorphism. -/
theorem stalkMap_comp_stalkSpecializes_genericPoint (z : N) :
    ν.stalkMap z ≫ N.presheaf.stalkSpecializes ((genericPoint_spec N).specializes trivial) =
      D.presheaf.stalkSpecializes
          (((genericPoint_spec N).specializes trivial).map ν.continuous) ≫
        ν.stalkMap (genericPoint N) :=
  (Scheme.Hom.stalkSpecializes_stalkMap _ _ _ _).symm

/-- A point of the base with an integrally closed local ring has at most one
point above it. -/
theorem eq_of_apply_eq_of_isIntegrallyClosed (z z' : N) (h : ν z = ν z')
    [IsIntegrallyClosed (D.presheaf.stalk (ν z))] : z = z' := by
  haveI : IsIntegrallyClosed (D.presheaf.stalk (ν z')) := h ▸ inferInstance
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show ν z ∈ (⊤ : D.Opens) from trivial)
  have hz'U : ν z' ∈ U := h ▸ hzU
  let V := ν ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage ν
  let ηN := genericPoint N
  have hηV : ηN ∈ V := (genericPoint_spec N).specializes trivial |>.mem_open V.isOpen hzU
  -- membership in the prime of a point over `e`, expressed through `e` alone
  let τ (e : D) (he : ν ηN ⤳ e) : D.presheaf.stalk e →+* N.functionField :=
    (ν.stalkMap ηN).hom.comp (D.presheaf.stalkSpecializes he).hom
  have key (w : N) (hwU : ν w ∈ U) [IsIntegrallyClosed (D.presheaf.stalk (ν w))]
      (c : Γ(N, V)) :
      c ∈ (hV.primeIdealOf ⟨w, hwU⟩).asIdeal ↔
        ∃ β ∈ maximalIdeal (D.presheaf.stalk (ν w)),
          τ (ν w) (((genericPoint_spec N).specializes trivial).map ν.continuous) β =
            N.presheaf.germ V ηN hηV c := by
    let wV : V := ⟨w, hwU⟩
    letI : Algebra Γ(N, V) (N.presheaf.stalk w) :=
      TopCat.Presheaf.algebra_section_stalk N.presheaf wV
    haveI : IsLocalization.AtPrime (N.presheaf.stalk w) (hV.primeIdealOf wV).asIdeal :=
      hV.isLocalization_stalk wV
    have hw : ηN ⤳ w := (genericPoint_spec N).specializes trivial
    have hψ : Function.Injective (N.presheaf.stalkSpecializes hw).hom :=
      IsFractionRing.injective (N.presheaf.stalk w) N.functionField
    have hτ (β : D.presheaf.stalk (ν w)) :
        τ (ν w) (hw.map ν.continuous) β =
          (N.presheaf.stalkSpecializes hw).hom ((ν.stalkMap w).hom β) := by
      have := congrArg (fun φ => φ.hom β) (stalkMap_comp_stalkSpecializes_genericPoint ν w)
      exact this.symm
    have hgermK : (N.presheaf.stalkSpecializes hw).hom
        (N.presheaf.germ V w hwU c) = N.presheaf.germ V ηN hηV c :=
      TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (N.presheaf.stalk w)
      (hV.primeIdealOf wV).asIdeal c]
    obtain ⟨σ, hσ⟩ := stalkMap_exists_germ ν hU w hwU c
    change N.presheaf.germ V w hwU c ∈ _ ↔ _
    constructor
    · intro hc
      refine ⟨σ, ?_, ?_⟩
      · by_contra hσm
        have hu : IsUnit σ := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hσm
        exact hc (hσ ▸ hu.map _)
      · rw [hτ, hσ, hgermK]
    · rintro ⟨β, hβm, hβ⟩
      rw [hτ, ← hgermK] at hβ
      rw [← hψ hβ]
      exact map_nonunit (ν.stalkMap w).hom β hβm
  apply (hV.fromSpec_primeIdealOf ⟨z, hzU⟩).symm.trans
  apply Eq.trans _ (hV.fromSpec_primeIdealOf ⟨z', hz'U⟩)
  congr 1
  apply PrimeSpectrum.ext
  ext c
  rw [key z hzU c, key z' hz'U c]
  have hP : ∀ (e e' : D) (_ : e = e') (he : ν ηN ⤳ e) (he' : ν ηN ⤳ e'),
      (∃ β ∈ maximalIdeal (D.presheaf.stalk e),
          τ e he β = N.presheaf.germ V ηN hηV c) ↔
        ∃ β ∈ maximalIdeal (D.presheaf.stalk e'),
          τ e' he' β = N.presheaf.germ V ηN hηV c := by
    intro e e' hee he he'
    subst hee
    rfl
  exact hP _ _ h _ _

instance normalizationMap_stalkMap_isIso_of_isIntegrallyClosed
    (D : Scheme.{u}) [IsIntegral D] (z : Palomar.normalization D)
    [IsIntegrallyClosed (D.presheaf.stalk (Palomar.normalizationMap D z))] :
    IsIso ((Palomar.normalizationMap D).stalkMap z) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (stalkMap_bijective_of_isIntegrallyClosed (Palomar.normalizationMap D) z)

theorem normalizationMap_eq_of_apply_eq_of_isIntegrallyClosed
    (D : Scheme.{u}) [IsIntegral D] (z z' : Palomar.normalization D)
    (h : Palomar.normalizationMap D z = Palomar.normalizationMap D z')
    [IsIntegrallyClosed (D.presheaf.stalk (Palomar.normalizationMap D z))] : z = z' :=
  eq_of_apply_eq_of_isIntegrallyClosed (Palomar.normalizationMap D) z z' h

#print axioms stalkMap_exists_of_isIntegral
#print axioms stalkMap_bijective_of_isIntegrallyClosed
#print axioms eq_of_apply_eq_of_isIntegrallyClosed
#print axioms normalizationMap_stalkMap_isIso_of_isIntegrallyClosed
#print axioms normalizationMap_eq_of_apply_eq_of_isIntegrallyClosed

end
end Pcf
