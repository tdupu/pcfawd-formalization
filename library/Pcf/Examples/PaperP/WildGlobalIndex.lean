/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.WildNotAllTheWayDown
public import Pcf.Examples.PaperP.WildAffineIndex
public import Pcf.Bounding.PaperPJacobianProjectiveVanishing
public import Pcf.Bounding.PointRamificationIdx
public import Pcf.Bounding.AffineSchemeRamification
public import Pcf.Bounding.SchemePrimeToPTameDivisor

/-!
# The global ramification index of the wild example along `H₀`

For `latex/paper-p.tex`, Example `ex:wild`, and the paragraph after it, this
module transports the affine index computation of `WildAffineIndex` to the
actual global projective morphism. The standard chart `D₊(z)` is identified
with the affine plane in coordinates `(y/z, x/z)`. Under this identification
the global morphism restricts to `affineCoordinateMap`, and the generic point
of `H₀` corresponds to the prime `(x/z)`. Open immersions preserve stalk
ramification indices, so the actual stalk index at `H₀` is `p`. In
particular `F` is wildly ramified along `H₀`, and its function-field
extension does not have prime-to-`p` monodromy.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization IsLocalRing
namespace Pcf.Examples.PaperP.Wild
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Open immersions preserve stalk ramification indices -/

section OpenImmersion

universe u

/-- Precomposition with an open immersion does not change the stalk index. -/
theorem ramificationIndexAt_comp_openImmersion_left {U X Y : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (f : X ⟶ Y) (x : U) :
    Pcf.Palomar.ramificationIndexAt (j ≫ f) x = Pcf.Palomar.ramificationIndexAt f (j x) := by
  let e := asIso (j.stalkMap x)
  have h := Pcf.ramificationIdx_maximalIdeal_eq_of_ringEquiv
    (f.stalkMap (j x)).hom ((j ≫ f).stalkMap x).hom (RingEquiv.refl _)
    e.commRingCatIsoToRingEquiv (by
      rw [Scheme.Hom.stalkMap_comp]
      rfl)
  exact h.symm

/-- Postcomposition with an open immersion does not change the stalk index. -/
theorem ramificationIndexAt_comp_openImmersion_right {U V Y : Scheme.{u}} (g : U ⟶ V)
    (i : V ⟶ Y) [IsOpenImmersion i] (x : U) :
    Pcf.Palomar.ramificationIndexAt (g ≫ i) x = Pcf.Palomar.ramificationIndexAt g x := by
  let e := asIso (i.stalkMap (g x))
  have h := Pcf.ramificationIdx_maximalIdeal_eq_of_ringEquiv
    ((g ≫ i).stalkMap x).hom (g.stalkMap x).hom e.commRingCatIsoToRingEquiv
    (RingEquiv.refl _) (by
      rw [Scheme.Hom.stalkMap_comp]
      rfl)
  exact h

/-- A commuting square of open immersions identifies the two stalk indices. -/
theorem ramificationIndexAt_of_openSquare {U V X Y : Scheme.{u}} (j : U ⟶ X) (i : V ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion i] (g : U ⟶ V) (f : X ⟶ Y)
    (h : j ≫ f = g ≫ i) (x : U) :
    Pcf.Palomar.ramificationIndexAt f (j x) = Pcf.Palomar.ramificationIndexAt g x := by
  rw [← ramificationIndexAt_comp_openImmersion_left j f x, h,
    ramificationIndexAt_comp_openImmersion_right]

/-- The stalk index of `Spec S → Spec R` at a prime `q` is Mathlib's
`Ideal.ramificationIdx`, when the contracted local ring is a discrete
valuation ring and the stalk map is injective. Unlike
`FrobeniusPinching.specAlgebraMap_ramificationIdx`, no global flatness of
`R → S` is assumed. -/
theorem specMap_ramificationIndexAt {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] (q : Spec (.of S)) (P : Ideal R) [P.IsPrime]
    (hP : q.asIdeal.comap (algebraMap R S) = P)
    [IsDiscreteValuationRing (Localization.AtPrime P)]
    (hinj : Function.Injective
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap q).hom) :
    Pcf.Palomar.ramificationIndexAt (Spec.map (CommRingCat.ofHom (algebraMap R S))) q =
      q.asIdeal.ramificationIdx R := by
  subst hP
  let f := algebraMap R S
  let e := Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) q
  let e₁ := (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv
  let e₂ := (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv
  let φ := ((Spec.map (CommRingCat.ofHom f)).stalkMap q).hom
  let ψ := Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl
  have hcomm : ψ.comp e₁.toRingHom = e₂.toRingHom.comp φ :=
    congrArg CommRingCat.Hom.hom e.hom.w
  have hidx := Pcf.ramificationIdx_maximalIdeal_eq_of_ringEquiv φ ψ e₁ e₂ hcomm
  change Pcf.Palomar.ramificationIndexAt _ q = _ at hidx
  rw [hidx]
  have hψ : Function.Injective ψ := by
    intro a b hab
    have key : ∀ t, ψ t = e₂ (φ (e₁.symm t)) := fun t => by
      have := congrArg (fun g : _ →+* _ => g (e₁.symm t)) hcomm
      calc ψ t = ψ (e₁ (e₁.symm t)) := by rw [RingEquiv.apply_symm_apply]
        _ = e₂ (φ (e₁.symm t)) := this
    rw [key, key] at hab
    exact e₁.symm.injective (hinj (e₂.injective hab))
  let P : Ideal R := q.asIdeal.comap f
  haveI : q.asIdeal.LiesOver P := ⟨rfl⟩
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime q.asIdeal) := ψ.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (Localization.localRingHom_to_map P q.asIdeal f rfl a).symm)
  haveI : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime q.asIdeal)) :=
    show IsLocalHom ψ from inferInstance
  haveI : Module.IsTorsionFree (Localization.AtPrime P) (Localization.AtPrime q.asIdeal) := by
    refine Module.isTorsionFree_iff_smul_eq_zero.mpr fun r m hrm => ?_
    rw [Algebra.smul_def] at hrm
    rcases mul_eq_zero.mp hrm with h | h
    · exact Or.inl (hψ (h.trans (map_zero ψ).symm))
    · exact Or.inr h
  haveI : IsDedekindDomain (Localization.AtPrime P) := inferInstance
  haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime q.asIdeal) := inferInstance
  exact Pcf.ramificationIdx_eq_of_localization_square P q.asIdeal

/-- A commuting square of open immersions transports injectivity of stalk maps. -/
theorem stalkMap_injective_of_openSquare {U V X Y : Scheme.{u}} (j : U ⟶ X) (i : V ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion i] (g : U ⟶ V) (f : X ⟶ Y)
    (h : j ≫ f = g ≫ i) (x : U) (hf : Function.Injective (f.stalkMap (j x)).hom) :
    Function.Injective (g.stalkMap x).hom := by
  have h1 : Function.Injective ((j ≫ f).stalkMap x).hom := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).1.comp hf
  rw [h, Scheme.Hom.stalkMap_comp] at h1
  have hb := ConcreteCategory.bijective_of_isIso (i.stalkMap (g x))
  intro a b hab
  obtain ⟨a', rfl⟩ := hb.2 a
  obtain ⟨b', rfl⟩ := hb.2 b
  have := h1 (a₁ := a') (a₂ := b') hab
  rw [this]

end OpenImmersion

variable (k : Type*) [Field k] (p : ℕ) (c : k)
local notation "lastX" => (X (Sum.inr ()) : Coordinates k)

/-! ### The standard chart `D₊(z)` -/

/-- The homogeneous chart pullback with both denominators the last coordinate. -/
noncomputable def standardPullback : Away (grading k) lastX →+* Away (grading k) lastX :=
  Pcf.paperPDegreeLocalizationMap (𝒜 := grading k) (ℬ := grading k)
    (aeval (forms k p c)).toRingHom (p + 1)
    (Pcf.paperPForms_degreeMap (forms k p c) (p + 1) (forms_homogeneous k p c))
    (by
      rintro q ⟨m, rfl⟩
      change aeval (forms k p c) (lastX ^ m) ∈ Submonoid.powers lastX
      simp only [map_pow, aeval_X, forms_two, z]
      exact ⟨(p + 1) * m, pow_mul _ _ _⟩)

theorem standard_awayToSection_comp_appLE (hp : 0 < p) :
    AlgebraicGeometry.Proj.awayToSection (grading k) lastX ≫
      (schemeMap k p c hp).appLE (Proj.basicOpen (grading k) lastX)
        (Proj.basicOpen (grading k) lastX) (by rw [← z, preimage_affineChart]) =
      CommRingCat.ofHom (standardPullback k p c) ≫
        AlgebraicGeometry.Proj.awayToSection (grading k) lastX := by
  ext w
  obtain ⟨m, P, hP, rfl⟩ := Away.mk_surjective (grading k) (isHomogeneous_X k (Sum.inr ())) w
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
  refine Subtype.ext <| funext fun q => ?_
  change HomogeneousLocalization.mk _ = HomogeneousLocalization.mk _
  ext
  simp [Pcf.paperPDegreeMapFraction, forms, z]

/-- The homogeneous standard chart inclusion commutes with the global map. -/
theorem standard_awayι_comp_map (hp : 0 < p) :
    AlgebraicGeometry.Proj.awayι (grading k) lastX (isHomogeneous_X k (Sum.inr ()))
        Nat.zero_lt_one ≫ schemeMap k p c hp =
      Spec.map (CommRingCat.ofHom (standardPullback k p c)) ≫
        AlgebraicGeometry.Proj.awayι (grading k) lastX (isHomogeneous_X k (Sum.inr ()))
          Nat.zero_lt_one := by
  have hι : (Proj.basicOpen (grading k) lastX).ι ≫ schemeMap k p c hp =
      (schemeMap k p c hp).resLE (Proj.basicOpen (grading k) lastX)
        (Proj.basicOpen (grading k) lastX) (by rw [← z, preimage_affineChart]) ≫
          (Proj.basicOpen (grading k) lastX).ι := by simp
  rw [AlgebraicGeometry.Proj.awayι, Category.assoc, hι, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine AlgebraicGeometry.ext_to_Spec <|
    (cancel_mono (Proj.basicOpen (grading k) lastX).topIso.hom).mp ?_
  simp [AlgebraicGeometry.Proj.basicOpenIsoSpec_hom,
    AlgebraicGeometry.Proj.basicOpenToSpec_app_top]
  exact standard_awayToSection_comp_appLE k p c hp

/-- The dehomogenized pullback in the chart coordinates `(x/z, y/z)`. -/
noncomputable def chartCoordinateMap :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![X 0 ^ p * (X 0 + X 1),
    X 1 ^ (p + 1) - X 0 ^ (p + 1) - X 0 ^ p + X 0 * X 1 ^ p + C c]

theorem dehomogenize_comp_forms :
    Pcf.paperPDehomogenize.comp (aeval (forms k p c)) =
      (chartCoordinateMap k p c).comp Pcf.paperPDehomogenize := by
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with j | u
  · fin_cases j <;> simp [forms, chartCoordinateMap, Pcf.paperPDehomogenize, x, y, z]
  · simp [forms, chartCoordinateMap, Pcf.paperPDehomogenize, z]

theorem standardPullback_mk (m : ℕ) (P : Coordinates k) (hP : P ∈ grading k m) :
    (standardPullback k p c)
        (Away.mk (grading k) (isHomogeneous_X k (Sum.inr ())) m P
          (by simpa only [smul_eq_mul, mul_one] using hP)) =
      Away.mk (grading k) (isHomogeneous_X k (Sum.inr ())) ((p + 1) * m)
        (aeval (forms k p c) P) (by
          simpa only [smul_eq_mul, mul_one] using
            (Pcf.paperPForms_degreeMap (forms k p c) (p + 1)
              (forms_homogeneous k p c) m P hP)) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (aeval (forms k p c) P) ⟨aeval (forms k p c) (lastX ^ m), _⟩ =
    Localization.mk (aeval (forms k p c) P) ⟨lastX ^ ((p + 1) * m), _⟩
  congr 1
  ext
  simp [forms, z, pow_mul]

/-- Dehomogenization identifies the chart pullback with `chartCoordinateMap`. -/
theorem standardPullback_dehomogenize (w : Away (grading k) lastX) :
    Pcf.paperPStandardChartRingEquiv (K := k) (n := 2) (standardPullback k p c w) =
      chartCoordinateMap k p c (Pcf.paperPStandardChartRingEquiv (K := k) (n := 2) w) := by
  obtain ⟨m, P, hP, rfl⟩ := Away.mk_surjective (grading k) (isHomogeneous_X k (Sum.inr ())) w
  have hP' : P ∈ grading k m := by simpa only [smul_eq_mul, mul_one] using hP
  rw [standardPullback_mk k p c m P hP']
  change Pcf.paperPStandardChartDehomogenize _ =
    chartCoordinateMap k p c (Pcf.paperPStandardChartDehomogenize _)
  rw [Pcf.paperPStandardChartDehomogenize_mk ((p + 1) * m) (aeval (forms k p c) P)
      (Pcf.paperPForms_degreeMap (forms k p c) (p + 1) (forms_homogeneous k p c) m P hP'),
    Pcf.paperPStandardChartDehomogenize_mk m P hP']
  exact congrArg (fun f : Coordinates k →ₐ[k] MvPolynomial (Fin 2) k => f P)
    (dehomogenize_comp_forms k p c)

/-- The coordinate swap `(x/z, y/z) ↦ (y/z, x/z)` into the order of `AffinePlane`. -/
noncomputable def swapEquiv : MvPolynomial (Fin 2) k ≃ₐ[k] AffinePlane k :=
  MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 2) 1)

theorem swap_comp_chartCoordinateMap :
    (swapEquiv k).toAlgHom.comp (chartCoordinateMap k p c) =
      (affineCoordinateMap k p c).comp (swapEquiv k).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [swapEquiv, chartCoordinateMap, affineCoordinateMap, affineX, affineY,
      FrobeniusLine.u, FrobeniusLine.v]

/-- The affine plane in coordinates `(y/z, x/z)` as the actual chart `D₊(z)`. -/
noncomputable def affineEmbedding : Spec (.of (AffinePlane k)) ⟶ Proj (grading k) :=
  Spec.map (CommRingCat.ofHom (swapEquiv k).toRingEquiv.toRingHom) ≫
    Pcf.paperPStandardChartToProj (K := k) (n := 2)

instance affineEmbedding_isOpenImmersion : IsOpenImmersion (affineEmbedding k) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom (swapEquiv k).toRingEquiv.toRingHom)) := by
    change IsIso (Scheme.Spec.mapIso (swapEquiv k).toRingEquiv.toCommRingCatIso.op).hom
    infer_instance
  unfold affineEmbedding
  infer_instance

/-- The actual global wild map restricts on `D₊(z)` to `affineCoordinateMap`. -/
theorem affineEmbedding_comp_map (hp : 0 < p) :
    affineEmbedding k ≫ schemeMap k p c hp =
      Spec.map (CommRingCat.ofHom (affineCoordinateMap k p c).toRingHom) ≫
        affineEmbedding k := by
  unfold affineEmbedding Pcf.paperPStandardChartToProj
  simp only [Category.assoc]
  rw [standard_awayι_comp_map k p c hp]
  simp only [← Category.assoc, ← Spec.map_comp]
  apply congrArg (fun q : CommRingCat.of (Away (grading k) lastX) ⟶
      CommRingCat.of (AffinePlane k) => Spec.map q ≫
        AlgebraicGeometry.Proj.awayι (grading k) lastX
          (isHomogeneous_X k (Sum.inr ())) Nat.zero_lt_one)
  apply CommRingCat.hom_ext
  refine RingHom.ext fun w => ?_
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
    Function.comp_apply]
  change (swapEquiv k) (Pcf.paperPStandardChartRingEquiv (standardPullback k p c w)) =
    affineCoordinateMap k p c ((swapEquiv k) (Pcf.paperPStandardChartRingEquiv w))
  rw [standardPullback_dehomogenize]
  exact congrArg (fun f : MvPolynomial (Fin 2) k →ₐ[k] AffinePlane k =>
    f (Pcf.paperPStandardChartRingEquiv w)) (swap_comp_chartCoordinateMap k p c)

/-! ### The generic point of `H₀` in the chart -/

theorem affineEmbedding_preimage_basicOpen {d : ℕ} (P : Coordinates k)
    (hP : P.IsHomogeneous d) :
    affineEmbedding k ⁻¹ᵁ Proj.basicOpen (grading k) P =
      PrimeSpectrum.basicOpen (swapEquiv k (Pcf.paperPDehomogenize P)) := by
  unfold affineEmbedding
  rw [Scheme.Hom.comp_preimage, Pcf.paperPStandardChartToProj_preimage_basicOpen P hP,
    SpecMap_preimage_basicOpen]
  rfl

theorem affineEmbedding_mem_homogeneous_iff (q : Spec (.of (AffinePlane k)))
    {d : ℕ} (P : Coordinates k) (hP : P.IsHomogeneous d) :
    P ∈ (affineEmbedding k q).asHomogeneousIdeal ↔
      swapEquiv k (Pcf.paperPDehomogenize P) ∈ q.asIdeal := by
  have h := congrArg (fun U : (Spec (.of (AffinePlane k))).Opens => q ∈ U)
    (affineEmbedding_preimage_basicOpen k P hP)
  replace h := eq_iff_iff.mp h
  change ¬ P ∈ (affineEmbedding k q).asHomogeneousIdeal ↔
    ¬ swapEquiv k (Pcf.paperPDehomogenize P) ∈ q.asIdeal at h
  exact not_iff_not.mp h

theorem swapEquiv_mem_lineIdeal_iff (g : MvPolynomial (Fin 2) k) :
    swapEquiv k g ∈ FrobeniusLine.lineIdeal k ↔
      g ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) k)} := by
  have hX0 : swapEquiv k (X 0) = FrobeniusLine.v k := by
    simp [swapEquiv, FrobeniusLine.v]
  have hX1 : (swapEquiv k).symm (FrobeniusLine.v k) = X 0 := by
    rw [← hX0, AlgEquiv.symm_apply_apply]
  change _ ∈ Ideal.span {FrobeniusLine.v k} ↔ _
  rw [Ideal.mem_span_singleton', Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(swapEquiv k).symm a, ?_⟩
    apply (swapEquiv k).injective
    rw [map_mul, AlgEquiv.apply_symm_apply, hX0, ha]
  · rintro ⟨a, rfl⟩
    exact ⟨swapEquiv k a, by rw [map_mul, hX0]⟩

/-- Specialization `x ↦ 0` of the affine chart ring. -/
noncomputable def chartKillX : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![0, X 1]

theorem dehomogenize_comp_killX :
    Pcf.paperPDehomogenize.comp (killX k) = (chartKillX k).comp Pcf.paperPDehomogenize := by
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with j | u
  · fin_cases j <;> simp [killX, chartKillX, Pcf.paperPDehomogenize, y]
  · simp [killX, chartKillX, Pcf.paperPDehomogenize, z]

theorem killX_isHomogeneous {d : ℕ} {P : Coordinates k} (hP : P.IsHomogeneous d) :
    (killX k P).IsHomogeneous d := by
  have h := hP.aeval (n := 1) (g := fun i : Index => match i with
    | Sum.inl j => if j = 0 then 0 else y k
    | Sum.inr _ => z k) (by
      intro i
      rcases i with j | u
      · dsimp only
        split_ifs
        · exact isHomogeneous_zero _ _ _
        · exact isHomogeneous_X _ _
      · exact isHomogeneous_X _ _)
  rw [one_mul] at h
  exact h

/-- A homogeneous form lies in `(x)` exactly when its dehomogenization lies in `(x/z)`. -/
theorem dehomogenize_mem_span_X0_iff {d : ℕ} (P : Coordinates k) (hP : P.IsHomogeneous d) :
    Pcf.paperPDehomogenize P ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) k)} ↔
      P ∈ Ideal.span {x k} := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h
    have hk : Pcf.paperPDehomogenize (killX k P) = 0 := by
      have := congrArg (fun f : Coordinates k →ₐ[k] MvPolynomial (Fin 2) k => f P)
        (dehomogenize_comp_killX k)
      simp only [AlgHom.comp_apply] at this
      rw [this, ← ha, map_mul]
      simp [chartKillX]
    have h0 := Pcf.paperPDehomogenize_eq_zero_of_isHomogeneous _ d (killX_isHomogeneous k hP) hk
    have hs := sub_killX_mem k P
    rwa [h0, sub_zero] at hs
  · intro h
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp h
    exact Ideal.mem_span_singleton'.mpr ⟨Pcf.paperPDehomogenize a, by
      rw [map_mul]
      simp [x, Pcf.paperPDehomogenize]⟩

/-- The prime `(x/z)` of the affine chart, as an actual point of `Spec`. -/
noncomputable def chartLinePoint : Spec (.of (AffinePlane k)) :=
  ⟨FrobeniusLine.lineIdeal k, inferInstance⟩

/-- The affine chart carries the prime `(x/z)` to the generic point of `H₀`. -/
theorem affineEmbedding_chartLinePoint : affineEmbedding k (chartLinePoint k) = H0gen k := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d P hP
  have hP' : P.IsHomogeneous d := (mem_homogeneousSubmodule d P).mp hP
  rw [affineEmbedding_mem_homogeneous_iff k _ P hP']
  change swapEquiv k _ ∈ FrobeniusLine.lineIdeal k ↔ P ∈ Ideal.span {x k}
  rw [swapEquiv_mem_lineIdeal_iff, dehomogenize_mem_span_X0_iff k P hP']

/-! ### Clause (A): the actual global index along `H₀` is `p` -/

theorem lineIdeal_localization_isDVR :
    IsDiscreteValuationRing (Localization.AtPrime (FrobeniusLine.lineIdeal k)) := by
  have hheight : (FrobeniusLine.lineIdeal k).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr (MvPolynomial.X_ne_zero (1 : Fin 2)))
      (MvPolynomial.X_prime (R := k) (i := (1 : Fin 2))).not_isUnit
  exact Pcf.isDiscreteValuationRing_localizationAtPrime_of_heightOne _ hheight

section Global

variable [Fact p.Prime]

local instance wildFinite : IsFinite (schemeMap k p c (Fact.out : p.Prime).pos) :=
  schemeMap_finite k p c _
local instance wildDominant : IsDominant (schemeMap k p c (Fact.out : p.Prime).pos) :=
  schemeMap_dominant k p c _

/-- **Example `ex:wild`, index along `H₀`.** The actual stalk ramification
index of the global projective morphism at the generic point of `H₀ = V(x)`
is `p`. This is the manuscript's "the local parameter `x/z` of the target
pulls back to `x^p(x+y)/z^(p+1)`, of valuation `p`".

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem ramificationIndexAt_H0gen :
    Pcf.Palomar.ramificationIndexAt (schemeMap k p c (Fact.out : p.Prime).pos) (H0gen k) =
      p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsq := affineEmbedding_comp_map k p c hp
  have hinjF : Function.Injective ((schemeMap k p c hp).stalkMap
      (affineEmbedding k (chartLinePoint k))).hom :=
    Pcf.stalkMap_injective_of_dominant_integral _ _
  have hinj := stalkMap_injective_of_openSquare _ _ _ _ hsq _ hinjF
  rw [← affineEmbedding_chartLinePoint, ramificationIndexAt_of_openSquare _ _ _ _ hsq]
  letI : Algebra (AffinePlane k) (AffinePlane k) := (affineCoordinateMap k p c).toRingHom.toAlgebra
  haveI := lineIdeal_localization_isDVR k
  exact (specMap_ramificationIndexAt (chartLinePoint k) (FrobeniusLine.lineIdeal k)
    (affine_lineIdeal_comap k p c hp) hinj).trans (affine_lineIdeal_ramificationIdx k p c hp)

/-- The same index in the repository's divisorial notation. -/
theorem schemeDivisorRamificationIdx_H0divisor :
    Pcf.schemeDivisorRamificationIdx (schemeMap k p c (Fact.out : p.Prime).pos) (H0divisor k) =
      p :=
  ramificationIndexAt_H0gen k p c

/-- **Wildness along `H₀`.** The index along `H₀` is ramified (`> 1`) and
divisible by the characteristic `p`, hence zero in `k`.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem wildlyRamified_H0 [CharP k p] :
    1 < Pcf.Palomar.ramificationIndexAt (schemeMap k p c (Fact.out : p.Prime).pos) (H0gen k) ∧
      p ∣ Pcf.Palomar.ramificationIndexAt (schemeMap k p c (Fact.out : p.Prime).pos)
        (H0gen k) ∧
      ((Pcf.Palomar.ramificationIndexAt (schemeMap k p c (Fact.out : p.Prime).pos)
        (H0gen k) : ℕ) : k) = 0 := by
  rw [ramificationIndexAt_H0gen]
  exact ⟨(Fact.out : p.Prime).one_lt, dvd_rfl, CharP.cast_eq_zero k p⟩

/-- **"The index `p` excludes `F` from the monodromy hypothesis of
Theorem `thm:A`."** The actual generic function-field extension of the wild
map does not have prime-to-`p` monodromy: prime-to-`p` monodromy would make
every divisorial index prime to `p` (`Pcf.schemeDivisor_tame_of_primeToP`).

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem schemeMap_not_isPrimeToPMonodromyMap [CharP k p] :
    ¬ Pcf.IsPrimeToPMonodromyMap p (schemeMap k p c (Fact.out : p.Prime).pos) := by
  intro hmono
  have h := (Pcf.schemeDivisor_tame_of_primeToP p (Fact.out : p.Prime) k (structureMap k)
    (schemeMap k p c (Fact.out : p.Prime).pos) hmono (H0divisor k)).1
  exact h (by rw [schemeDivisorRamificationIdx_H0divisor])

end Global

/-! ### Clause (B): the branch point `[0:c:1]` of the restriction -/

/-- The inclusion of the line coordinate ring as the `x`-free part. -/
noncomputable def lineInclusion : LineCoords k →ₐ[k] Coordinates k :=
  rename (Sum.map (fun _ : Fin 1 => (0 : Fin 2)) id)

theorem lineInclusion_injective : Function.Injective (lineInclusion k) :=
  rename_injective _ (Sum.map_injective.mpr ⟨fun a b _ => Subsingleton.elim a b,
    Function.injective_id⟩)

theorem linePointForms_eq_comp (t : k) :
    aeval (linePointForms k t) = ((lineInclusion k).comp
      (aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k t 1))).comp
        (lineSpecialization k) := by
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with j | u
  · fin_cases j <;>
      simp [linePointForms, lineSpecialization, lineValues, lineInclusion, lu, x,
        Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms]
  · simp [linePointForms, lineSpecialization, lineValues, lineInclusion, lv, x,
      Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms]

/-- The line point `[t:1]` of `ℙ¹` embeds as the plane point `[0:t:1]`. -/
theorem lineEmbedding_finitePoint (t : k) :
    lineEmbedding k (finitePoint k t) = linePoint k t := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro P
  rw [mem_lineEmbedding_apply, lineGradedHom_apply]
  change aeval (Pcf.Examples.PaperP.BasilicaProjectiveScheme.pointForms k t 1)
      (lineSpecialization k P) = 0 ↔ aeval (linePointForms k t) P = 0
  rw [linePointForms_eq_comp]
  simp only [AlgHom.comp_apply]
  exact ⟨fun h => by rw [h, map_zero], fun h => lineInclusion_injective k (by rw [h, map_zero])⟩

/-- The plane point `[0:1:0]`, the image of `∞ ∈ ℙ¹`. -/
noncomputable def lineInfinityPoint : Proj (grading k) :=
  lineEmbedding k (Pcf.Examples.PaperP.BasilicaProjectiveScheme.infinity k)

/-- `H₀ ∩ H₂ = {[0:1:0]}` as sets of actual scheme points. -/
theorem H0_inter_H2 : H0 k ∩ H2 k = {lineInfinityPoint k} := by
  ext q
  constructor
  · rintro ⟨h0, h2⟩
    rw [← lineEmbedding_range] at h0
    obtain ⟨r, rfl⟩ := h0
    have hz := (mem_lineEmbedding_apply k r (z k)).mp h2
    rw [lineGradedHom_apply, lineSpecialization_z, lv,
      Pcf.Examples.PaperP.BasilicaProjectiveScheme.secondCoordinate_mem_iff] at hz
    rw [hz]
    rfl
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [← lineEmbedding_range]
      exact ⟨_, rfl⟩
    · change z k ∈ (lineInfinityPoint k).asHomogeneousIdeal
      refine (mem_lineEmbedding_apply k _ (z k)).mpr ?_
      rw [lineGradedHom_apply, lineSpecialization_z, lv,
        Pcf.Examples.PaperP.BasilicaProjectiveScheme.secondCoordinate_mem_iff]

section Branch

variable [Fact p.Prime] [CharP k p]

local instance wildFinite' : IsFinite (schemeMap k p c (Fact.out : p.Prime).pos) :=
  schemeMap_finite k p c _
local instance wildDominant' : IsDominant (schemeMap k p c (Fact.out : p.Prime).pos) :=
  schemeMap_dominant k p c _
local instance planeNormalizationIso :
    IsIso (Pcf.Palomar.normalizationMap (Proj (grading k))) :=
  Pcf.normalScheme_normalizationMap_isIso _
local instance lineNormalizationIso' :
    IsIso (Pcf.Palomar.normalizationMap (Proj (lineGrading k))) :=
  Pcf.normalScheme_normalizationMap_isIso _
local instance lineReturnFinite' : IsFinite (lineReturnMap k p c) :=
  Pcf.paperPFormsProjective_isFinite _ _ _ _ _
local instance lineReturnDominant' : IsDominant (lineReturnMap k p c) := by
  unfold lineReturnMap
  infer_instance

/-- The normalized weighted branch points of the return `h(t)=t^(p+1)+c` on
`H₀` are `c = h(0)` and `∞`. -/
theorem lineWeightedBranchPointSet_eq :
    Pcf.weightedBranchPointSet (lineReturnMap k p c) =
      {finitePoint k c, Pcf.Examples.PaperP.BasilicaProjectiveScheme.infinity k} := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [Pcf.weightedBranchPointSet_eq_image_criticalPointSet, lineWeightedCriticalPointSet_eq,
    Set.image_pair, lineReturnMap_finitePoint, lineReturnMap_infinity]
  simp [returnFunction, zero_pow (by omega : p + 1 ≠ 0)]

/-- **The paragraph after `ex:wild`.** The restriction `F|_{H₀}`, in its
canonical line model `h`, is branched at `[0:c:1] = F([0:0:1])`. This point
lies on `H₀` and on no other normalized weighted postcritical component of `F`
(the only other one is `H₂`). Hence the branch locus of `F|_{H₀}` is not
contained in `H₀ ∩ H₂ = {[0:1:0]}`.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem branch_restriction_not_subset_H0_inter_H2 :
    linePoint k c ∈ lineEmbedding k '' Pcf.weightedBranchPointSet (lineReturnMap k p c) ∧
      linePoint k c = schemeMap k p c (Fact.out : p.Prime).pos (linePoint k 0) ∧
      linePoint k c ∈ H0 k ∧
      (∀ q ∈ Pcf.weightedPostcriticalPointSet (schemeMap k p c (Fact.out : p.Prime).pos),
        linePoint k c ∈ closure {q} → q = H0gen k) ∧
      H0 k ∩ H2 k = {lineInfinityPoint k} ∧
      ¬ (lineEmbedding k '' Pcf.weightedBranchPointSet (lineReturnMap k p c) ⊆
        H0 k ∩ H2 k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hmem : linePoint k c ∈
      lineEmbedding k '' Pcf.weightedBranchPointSet (lineReturnMap k p c) := by
    rw [lineWeightedBranchPointSet_eq]
    exact ⟨finitePoint k c, Or.inl rfl, lineEmbedding_finitePoint k c⟩
  have h2 : linePoint k c ∉ H2 k := linePoint_not_mem_H2 k c
  refine ⟨hmem, ?_, ?_, ?_, H0_inter_H2 k, fun hsub => h2 (hsub hmem).2⟩
  · rw [schemeMap_linePoint]
    simp [returnFunction, zero_pow (by omega : p + 1 ≠ 0)]
  · rw [← lineEmbedding_finitePoint, ← lineEmbedding_range]
    exact ⟨_, rfl⟩
  · intro q hq hcl
    rw [weightedPostcriticalPointSet_eq] at hq
    rcases hq with rfl | hq
    · rfl
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      rw [closure_H2gen] at hcl
      exact absurd hcl h2

end Branch

#print axioms specMap_ramificationIndexAt
#print axioms stalkMap_injective_of_openSquare
#print axioms affineEmbedding_comp_map
#print axioms affineEmbedding_chartLinePoint
#print axioms ramificationIndexAt_H0gen
#print axioms schemeDivisorRamificationIdx_H0divisor
#print axioms wildlyRamified_H0
#print axioms schemeMap_not_isPrimeToPMonodromyMap
#print axioms lineEmbedding_finitePoint
#print axioms H0_inter_H2
#print axioms lineWeightedBranchPointSet_eq
#print axioms branch_restriction_not_subset_H0_inter_H2

#print axioms standard_awayToSection_comp_appLE
#print axioms ramificationIndexAt_of_openSquare
end Pcf.Examples.PaperP.Wild
