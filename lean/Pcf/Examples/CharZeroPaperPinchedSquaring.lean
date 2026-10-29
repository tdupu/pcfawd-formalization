/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperSmoothBranch
public import Pcf.Examples.CharZeroPaperPinchedPlane

/-!
# Branch divisors of the squaring maps in `paper.tex`, Example `ex:pinched`

The two normalizations occurring in `ex:pinched` are `𝔸² = Spec k[z,w]` with
`(z,w) ↦ (z²,w²)` and `𝔸¹ = Spec k[z]` with `z ↦ z²`. For a ring map
`φ : T → T` presented as `T ≅ T[Y]/(Y² - t)` over `φ`, the actual
residue-field fibre over `P` is `κ(P)[Y]/(Y² - t̄)`; in characteristic zero
it is reduced exactly when `t ∉ P` (`quadratic_fiber_isReduced_iff`).

Consequences, for the actual affine schemes:

* `lineSquaring_reducedFiberBranch`: the only branch divisor of `z ↦ z²` on
  `𝔸¹` is `V(z)`;
* `planeSquaring_reducedFiberBranch_support`: the branch divisors of
  `(z,w) ↦ (z²,w²)` on `𝔸²` are exactly `V(z)` and `V(w)`, obtained from the
  two one-variable squarings by the proved tower formula for normal schemes.

No branch assertion is an input.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperPinched

open CategoryTheory AlgebraicGeometry Polynomial Pcf.PaperCharZero
open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

/-! ### Quadratic presentations -/

section Quadratic

variable {T : Type u} [CommRing T] (φ : T →+* T)

/-- The source ring of `φ`, as a `T`-algebra through `φ`. -/
def SquaringSource (_φ : T →+* T) : Type u := T

instance : CommRing (SquaringSource φ) := inferInstanceAs (CommRing T)
instance : Algebra T (SquaringSource φ) := φ.toAlgebra
instance [IsDomain T] : IsDomain (SquaringSource φ) := inferInstanceAs (IsDomain T)

/-- A quadratic presentation `T[Y]/(Y² - t) ≅ T` of `T` as an algebra over itself
through `φ`. -/
structure QuadraticPresentation where
  /-- The parameter `t`. -/
  t : T
  /-- The isomorphism of `T`-algebras. -/
  equiv : AdjoinRoot (X ^ 2 - C t) ≃ₐ[T] SquaringSource φ

variable {φ}

theorem eval₂_quadratic (t x : T) (hx : x ^ 2 = φ t) :
    (X ^ 2 - C t).eval₂ φ x = 0 := by
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C]
  rw [hx, sub_self]

/-- Build a quadratic presentation from `x² = φ t` and an inverse ring map. -/
def QuadraticPresentation.ofInverse (t x : T) (hx : x ^ 2 = φ t)
    (bwd : T →+* AdjoinRoot (X ^ 2 - C t))
    (hbwd : bwd.comp φ = AdjoinRoot.of _) (hbx : bwd x = AdjoinRoot.root _)
    (hfb : (AdjoinRoot.lift φ x (eval₂_quadratic t x hx)).comp bwd = RingHom.id T) :
    QuadraticPresentation φ where
  t := t
  equiv := by
    let fwd : AdjoinRoot (X ^ 2 - C t) →ₐ[T] SquaringSource φ :=
      AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (x : SquaringSource φ)
        (by exact eval₂_quadratic t x hx)
    let bwdAlg : SquaringSource φ →ₐ[T] AdjoinRoot (X ^ 2 - C t) :=
      { toRingHom := bwd
        commutes' := fun r => by
          change bwd (φ r) = _
          rw [← RingHom.comp_apply, hbwd]
          rfl }
    refine AlgEquiv.ofAlgHom fwd bwdAlg ?_ ?_
    · apply AlgHom.toRingHom_injective
      exact hfb
    · apply AdjoinRoot.algHom_ext
      change bwd (AdjoinRoot.lift φ x (eval₂_quadratic t x hx) (AdjoinRoot.root _)) = _
      rw [AdjoinRoot.lift_root, hbx]
      rfl

theorem QuadraticPresentation.finite (Q : QuadraticPresentation φ) : φ.Finite := by
  have hmon : (X ^ 2 - C Q.t).Monic := monic_X_pow_sub_C _ (by norm_num)
  have h1 : Module.Finite T (AdjoinRoot (X ^ 2 - C Q.t)) := (AdjoinRoot.powerBasis' hmon).finite
  have h2 : Module.Finite T (SquaringSource φ) := Module.Finite.equiv Q.equiv.toLinearEquiv
  exact h2

theorem root_sq_quadratic (t : T) :
    AdjoinRoot.root (X ^ 2 - C t) ^ 2 = AdjoinRoot.of _ t := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C t)
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using h

/-- The actual residue-field tensor product has the quadratic presentation. -/
def QuadraticPresentation.fiberEquiv (Q : QuadraticPresentation φ) (P : PrimeSpectrum T) :
    P.asIdeal.Fiber (SquaringSource φ) ≃+*
      AdjoinRoot (X ^ 2 - C (algebraMap T P.asIdeal.ResidueField Q.t)) := by
  let e₁ := Algebra.TensorProduct.congr
    (AlgEquiv.refl : P.asIdeal.ResidueField ≃ₐ[P.asIdeal.ResidueField] P.asIdeal.ResidueField)
    Q.equiv.symm
  let q := (X ^ 2 - C Q.t).map
    (Algebra.TensorProduct.includeRight : T →ₐ[T]
      P.asIdeal.ResidueField ⊗[T] T).toRingHom
  let e₂ := AdjoinRoot.tensorAlgEquiv (R := T) (T := P.asIdeal.ResidueField)
    (X ^ 2 - C Q.t) q rfl
  let e₃ := AdjoinRoot.mapAlgEquiv
    (Algebra.TensorProduct.rid T P.asIdeal.ResidueField P.asIdeal.ResidueField)
    q (X ^ 2 - C (algebraMap T P.asIdeal.ResidueField Q.t))
    (Associated.of_eq (by simp [q, Algebra.smul_def]))
  exact e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃.toRingEquiv)

set_option backward.isDefEq.respectTransparency false in
/-- Reducedness of the actual affine fibre is reducedness of the fibre ring. -/
theorem squaring_fiber_isReduced_iff_ring (P : PrimeSpectrum T) :
    IsReduced ((Spec.map (CommRingCat.ofHom φ)).fiber P) ↔
      _root_.IsReduced (P.asIdeal.Fiber (SquaringSource φ)) := by
  let e := Spec.fiberToSpecResidueFieldIso T (SquaringSource φ) P
  constructor
  · intro h
    exact (affine_isReduced_iff _).mp
      (@isReduced_of_isOpenImmersion _ _ e.inv.left inferInstance h)
  · intro h
    let : IsIso e.hom.left := (Arrow.leftFunc.mapIso e).isIso_hom
    have hspec := (affine_isReduced_iff (.of (P.asIdeal.Fiber (SquaringSource φ)))).mpr h
    exact @isReduced_of_isOpenImmersion _ _ e.hom.left (IsOpenImmersion.of_isIso _) hspec

/-- **The quadratic fibre criterion.** In characteristic zero the actual fibre of
`Spec φ` over `P` is reduced iff `t ∉ P`. -/
theorem QuadraticPresentation.fiber_isReduced_iff (Q : QuadraticPresentation φ)
    (P : PrimeSpectrum T) [CharZero P.asIdeal.ResidueField] :
    IsReduced ((Spec.map (CommRingCat.ofHom φ)).fiber P) ↔ Q.t ∉ P.asIdeal := by
  rw [squaring_fiber_isReduced_iff_ring]
  have he : _root_.IsReduced (P.asIdeal.Fiber (SquaringSource φ)) ↔
      _root_.IsReduced (AdjoinRoot
        (X ^ 2 - C (algebraMap T P.asIdeal.ResidueField Q.t))) := by
    constructor
    · intro h
      exact isReduced_of_injective (Q.fiberEquiv P).symm (Q.fiberEquiv P).symm.injective
    · intro h
      exact isReduced_of_injective (Q.fiberEquiv P) (Q.fiberEquiv P).injective
  rw [he, CharZeroPaperSmoothBranch.quadratic_isReduced_iff, ne_eq,
    Ideal.algebraMap_residueField_eq_zero]

/-- The divisor `V(t)` of a prime element of a Noetherian domain. -/
def primeDivisor [IsDomain T] [IsNoetherianRing T] (t : T) (ht : Prime t) :
    SchemeDivisorPoint (Spec (.of T)) :=
  ⟨⟨Ideal.span {t}, (Ideal.span_singleton_prime ht.ne_zero).mpr ht⟩,
    (idealHeight_eq_coheight (.of T)
      ⟨Ideal.span {t}, (Ideal.span_singleton_prime ht.ne_zero).mpr ht⟩).symm.trans
      (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero) ht.not_isUnit)⟩

@[simp] theorem primeDivisor_asIdeal [IsDomain T] [IsNoetherianRing T] (t : T) (ht : Prime t) :
    (primeDivisor t ht).1.asIdeal = Ideal.span {t} := rfl

theorem primeDivisor_eq_of_mem [IsDomain T] [IsNoetherianRing T] (t : T) (ht : Prime t)
    (E : SchemeDivisorPoint (Spec (.of T))) (hE : t ∈ E.1.asIdeal) :
    E = primeDivisor t ht := by
  have hheight : E.1.asIdeal.height = 1 := (idealHeight_eq_coheight (.of T) E.1).trans E.2
  have h1 : (Ideal.span {t}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero) ht.not_isUnit
  have : (Ideal.span {t}).IsPrime := (Ideal.span_singleton_prime ht.ne_zero).mpr ht
  have : (Ideal.span {t}).FiniteHeight := by
    simp [Ideal.finiteHeight_iff, h1]
  have he : Ideal.span {t} = E.1.asIdeal := Ideal.eq_of_le_of_height_le (Ideal.span {t})
    (Ideal.span_le.mpr (by simpa using hE)) (by rw [hheight, h1])
  apply Subtype.ext
  apply PrimeSpectrum.ext
  rw [primeDivisor_asIdeal]
  exact he.symm

set_option backward.isDefEq.respectTransparency false in
/-- The sole branch divisor of a quadratic presentation with prime parameter. -/
theorem QuadraticPresentation.reducedFiberBranch [IsDomain T] [IsNoetherianRing T]
    (Q : QuadraticPresentation φ) (t : T) (hQ : Q.t = t) (ht : Prime t)
    [hchar : ∀ P : PrimeSpectrum T, CharZero P.asIdeal.ResidueField] :
    schemeReducedFiberBranch (Spec.map (CommRingCat.ofHom φ)) = {primeDivisor t ht} := by
  subst hQ
  ext E
  change (¬ IsReduced ((Spec.map (CommRingCat.ofHom φ)).fiber E.1)) ↔ E = primeDivisor Q.t ht
  rw [Q.fiber_isReduced_iff, not_not]
  constructor
  · exact primeDivisor_eq_of_mem Q.t ht E
  · rintro rfl
    rw [primeDivisor_asIdeal]
    exact Ideal.subset_span (Set.mem_singleton _)

theorem divisorSupport_primeDivisor [IsDomain T] [IsNoetherianRing T] (t : T) (ht : Prime t) :
    divisorSupport ({primeDivisor t ht} : Set (SchemeDivisorPoint (Spec (.of T)))) =
      {P : Spec (.of T) | t ∈ P.asIdeal} := by
  simp only [divisorSupport, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]
  change closure ({(show PrimeSpectrum T from (primeDivisor t ht).1)} :
    Set (PrimeSpectrum T)) = _
  rw [PrimeSpectrum.closure_singleton]
  ext P
  change (primeDivisor t ht).1.asIdeal ≤ P.asIdeal ↔ t ∈ P.asIdeal
  simp [Ideal.span_le]

end Quadratic

/-! ### The one-variable squaring `z ↦ z²` on `𝔸¹` -/

section Line

variable (k : Type u) [Field k]

/-- The affine line `𝔸¹ = Spec k[z]`. -/
abbrev line : Scheme.{u} := Spec (.of (Polynomial k))

/-- `z ↦ z²`. -/
def lineSquaringRing : Polynomial k →+* Polynomial k := (expand k 2).toRingHom

/-- The squaring map of `𝔸¹`. -/
def lineSquaring : line k ⟶ line k := Spec.map (CommRingCat.ofHom (lineSquaringRing k))

theorem lineSquaringRing_injective : Function.Injective (lineSquaringRing k) :=
  expand_injective (by norm_num)

/-- The quadratic presentation `k[z] ≅ k[z][Y]/(Y² - z)` over `z ↦ z²`. -/
def lineQuadraticPresentation : QuadraticPresentation (lineSquaringRing k) :=
  QuadraticPresentation.ofInverse (X : Polynomial k) X
    (by simp [lineSquaringRing])
    (Polynomial.eval₂RingHom ((AdjoinRoot.of _).comp Polynomial.C) (AdjoinRoot.root _))
    (by
      apply Polynomial.ringHom_ext
      · intro a; simp [lineSquaringRing]
      · simp [lineSquaringRing, root_sq_quadratic])
    (by simp)
    (by
      apply Polynomial.ringHom_ext
      · intro a; simp [lineSquaringRing]
      · simp)

theorem lineSquaringRing_finite : (lineSquaringRing k).Finite :=
  (lineQuadraticPresentation k).finite

instance lineSquaring_isFinite : IsFinite (lineSquaring k) :=
  (IsFinite.SpecMap_iff _).mpr (lineSquaringRing_finite k)

instance lineSquaring_surjective : Surjective (lineSquaring k) := by
  constructor
  exact (lineSquaringRing_finite k).to_isIntegral.comap_surjective
    (lineSquaringRing_injective k)

instance lineSquaring_isDominant : IsDominant (lineSquaring k) := inferInstance

theorem prime_X_line : Prime (X : Polynomial k) := Polynomial.prime_X

instance line_residueField_charZero [CharZero k] (P : PrimeSpectrum (Polynomial k)) :
    CharZero P.asIdeal.ResidueField :=
  charZero_of_injective_ringHom
    ((algebraMap (Polynomial k) P.asIdeal.ResidueField).comp
      (algebraMap k (Polynomial k))).injective

/-- `V(z) ⊂ 𝔸¹`. -/
def lineOrigin : SchemeDivisorPoint (line k) := primeDivisor (X : Polynomial k) (prime_X_line k)

/-- The sole branch divisor of `z ↦ z²` is `V(z)`. -/
theorem lineSquaring_reducedFiberBranch [CharZero k] :
    schemeReducedFiberBranch (lineSquaring k) = {lineOrigin k} :=
  (lineQuadraticPresentation k).reducedFiberBranch X rfl (prime_X_line k)

theorem lineSquaring_reducedFiberBranch_support [CharZero k] :
    divisorSupport (schemeReducedFiberBranch (lineSquaring k)) =
      {P : line k | (X : Polynomial k) ∈ P.asIdeal} := by
  rw [lineSquaring_reducedFiberBranch]
  exact divisorSupport_primeDivisor _ _

/-- `z ↦ z²` fixes `V(z)`. -/
theorem lineSquaring_lineOrigin : lineSquaring k (lineOrigin k).1 = (lineOrigin k).1 := by
  apply PrimeSpectrum.ext
  ext p
  change lineSquaringRing k p ∈ Ideal.span {X} ↔ p ∈ Ideal.span {X}
  simp only [Ideal.mem_span_singleton, lineSquaringRing, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom]
  rw [X_dvd_iff, X_dvd_iff, coeff_expand (by norm_num)]
  simp

end Line

/-! ### The two-variable squaring on `𝔸²` -/

section Plane

variable (k : Type u) [Field k]

open MvPolynomial in
/-- Squaring the `i`-th variable of `k[z, w]`. -/
def varSquaring (i : Fin 2) : PlaneRing k →ₐ[k] PlaneRing k :=
  aeval fun j => if j = i then X j ^ 2 else X j

open MvPolynomial in
theorem varSquaring_X (i j : Fin 2) :
    varSquaring k i (X j) = if j = i then X j ^ 2 else X j := by
  simp [varSquaring]

open MvPolynomial in
theorem squaringMap_eq_comp : (squaringMap k : PlaneRing k →+* PlaneRing k) =
    (varSquaring k 1 : PlaneRing k →+* PlaneRing k).comp (varSquaring k 0) := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp
  · intro j
    fin_cases j <;> simp [varSquaring_X]

open MvPolynomial in
theorem squaringMap_eq_comp' : (squaringMap k : PlaneRing k →+* PlaneRing k) =
    (varSquaring k 0 : PlaneRing k →+* PlaneRing k).comp (varSquaring k 1) := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp
  · intro j
    fin_cases j <;> simp [varSquaring_X]

theorem varSquaring_injective (i : Fin 2) : Function.Injective (varSquaring k i) := by
  fin_cases i
  · intro a b h
    apply squaringMap_injective k
    have e := congrArg (fun p => (varSquaring k 1 : PlaneRing k →+* PlaneRing k) p) h
    change (squaringMap k : PlaneRing k →+* PlaneRing k) a =
      (squaringMap k : PlaneRing k →+* PlaneRing k) b
    rw [squaringMap_eq_comp]
    exact e
  · intro a b h
    apply squaringMap_injective k
    have e := congrArg (fun p => (varSquaring k 0 : PlaneRing k →+* PlaneRing k) p) h
    change (squaringMap k : PlaneRing k →+* PlaneRing k) a =
      (squaringMap k : PlaneRing k →+* PlaneRing k) b
    rw [squaringMap_eq_comp']
    exact e

open MvPolynomial in
/-- The quadratic presentation of `k[z, w]` over the squaring of the `i`-th variable. -/
def varQuadraticPresentation (i : Fin 2) :
    QuadraticPresentation (varSquaring k i : PlaneRing k →+* PlaneRing k) :=
  QuadraticPresentation.ofInverse (X i) (X i) (by simp [varSquaring_X])
    (aeval fun j => if j = i then AdjoinRoot.root _ else
      AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C (X i : PlaneRing k)) (X j) :
        PlaneRing k →ₐ[k] _).toRingHom
    (by
      apply MvPolynomial.ringHom_ext
      · intro a
        change (MvPolynomial.aeval _) (varSquaring k i (algebraMap k (PlaneRing k) a)) =
          AdjoinRoot.of _ (algebraMap k (PlaneRing k) a)
        rw [AlgHom.commutes, AlgHom.commutes]
        rfl
      · intro j
        simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, varSquaring_X,
          AlgHom.toRingHom_eq_coe]
        by_cases hj : j = i
        · subst hj; simp [root_sq_quadratic]
        · simp [hj])
    (by simp)
    (by
      apply MvPolynomial.ringHom_ext
      · intro a
        change AdjoinRoot.lift (varSquaring k i : PlaneRing k →+* PlaneRing k) (MvPolynomial.X i)
          (eval₂_quadratic _ _ (by simp [varSquaring_X]))
          ((MvPolynomial.aeval _) (algebraMap k (PlaneRing k) a)) = algebraMap k (PlaneRing k) a
        rw [AlgHom.commutes]
        change AdjoinRoot.lift (varSquaring k i : PlaneRing k →+* PlaneRing k) (MvPolynomial.X i)
          (eval₂_quadratic _ _ (by simp [varSquaring_X]))
          (AdjoinRoot.of _ (algebraMap k (PlaneRing k) a)) = _
        rw [AdjoinRoot.lift_of]
        exact (varSquaring k i).commutes a
      · intro j
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          RingHom.id_apply, MvPolynomial.aeval_X]
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj, AdjoinRoot.lift_of, varSquaring_X])

/-- The scheme map squaring the `i`-th coordinate. -/
def varSquaringMap (i : Fin 2) : plane k ⟶ plane k :=
  Spec.map (CommRingCat.ofHom (varSquaring k i : PlaneRing k →+* PlaneRing k))

theorem varSquaring_finite (i : Fin 2) :
    (varSquaring k i : PlaneRing k →+* PlaneRing k).Finite :=
  (varQuadraticPresentation k i).finite

instance varSquaringMap_isFinite (i : Fin 2) : IsFinite (varSquaringMap k i) :=
  (IsFinite.SpecMap_iff _).mpr (varSquaring_finite k i)

instance varSquaringMap_surjective (i : Fin 2) : Surjective (varSquaringMap k i) := by
  constructor
  exact (varSquaring_finite k i).to_isIntegral.comap_surjective (varSquaring_injective k i)

instance varSquaringMap_isDominant (i : Fin 2) : IsDominant (varSquaringMap k i) :=
  inferInstance

instance plane_residueField_charZero [CharZero k] (P : PrimeSpectrum (PlaneRing k)) :
    CharZero P.asIdeal.ResidueField :=
  charZero_of_injective_ringHom
    ((algebraMap (PlaneRing k) P.asIdeal.ResidueField).comp
      (algebraMap k (PlaneRing k))).injective

theorem prime_X_plane (i : Fin 2) : Prime (MvPolynomial.X i : PlaneRing k) :=
  MvPolynomial.X_prime

/-- The coordinate axis `V(X i) ⊂ 𝔸²`: `V(z)` for `i = 0`, `V(w)` for `i = 1`. -/
def axisDivisor (i : Fin 2) : SchemeDivisorPoint (plane k) :=
  primeDivisor (MvPolynomial.X i : PlaneRing k) (prime_X_plane k i)

theorem varSquaringMap_reducedFiberBranch [CharZero k] (i : Fin 2) :
    schemeReducedFiberBranch (varSquaringMap k i) = {axisDivisor k i} :=
  (varQuadraticPresentation k i).reducedFiberBranch (MvPolynomial.X i) rfl (prime_X_plane k i)

instance plane_isNormal : IsNormalScheme (plane k) :=
  CharZeroPaperSmoothBranch.normal_spec (PlaneRing k)

/-- A divisor of `𝔸²` containing `X i` is the axis `V(X i)`. -/
theorem eq_axisDivisor_of_mem (i : Fin 2) (E : SchemeDivisorPoint (plane k))
    (hE : (MvPolynomial.X i : PlaneRing k) ∈ E.1.asIdeal) : E = axisDivisor k i :=
  primeDivisor_eq_of_mem _ (prime_X_plane k i) E hE

/-- A finite dominant self-map of `𝔸²` whose pullback sends `X i` into `(X i)` fixes
the axis `V(X i)`. -/
theorem fixes_axis (g : plane k ⟶ plane k) [IsFinite g] [IsDominant g] (i : Fin 2)
    (hg : (MvPolynomial.X i : PlaneRing k) ∈ (g (axisDivisor k i).1).asIdeal) :
    g (axisDivisor k i).1 = (axisDivisor k i).1 := by
  have h := eq_axisDivisor_of_mem k i ⟨g (axisDivisor k i).1,
    coheight_apply_eq_one g (axisDivisor k i)⟩ hg
  exact congrArg Subtype.val h

/-- The squaring map of `𝔸²` is the composite of the two coordinate squarings. -/
theorem planeSquaring_eq_comp :
    planeSquaring k = varSquaringMap k 1 ≫ varSquaringMap k 0 := by
  unfold planeSquaring varSquaringMap
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact squaringMap_eq_comp k

instance planeSquaring_isFinite [CharZero k] : IsFinite (planeSquaring k) := by
  rw [planeSquaring_eq_comp]; infer_instance

instance planeSquaring_isDominant [CharZero k] : IsDominant (planeSquaring k) := by
  rw [planeSquaring_eq_comp]; infer_instance

instance planeSquaring_surjective [CharZero k] : Surjective (planeSquaring k) := by
  rw [planeSquaring_eq_comp]; infer_instance

theorem planeSquaring_X_mem (i : Fin 2) (P : plane k)
    (hP : (MvPolynomial.X i : PlaneRing k) ∈ P.asIdeal) :
    (MvPolynomial.X i : PlaneRing k) ∈ (planeSquaring k P).asIdeal := by
  change squaringMap k (MvPolynomial.X i) ∈ P.asIdeal
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, squaringMap_X0, sq]
    exact P.asIdeal.mul_mem_left _ hP
  · simp only [Fin.mk_one, Fin.isValue, squaringMap_X1, sq]
    exact P.asIdeal.mul_mem_left _ hP

/-- `f̃` fixes both coordinate axes. -/
theorem planeSquaring_axis [CharZero k] (i : Fin 2) :
    planeSquaring k (axisDivisor k i).1 = (axisDivisor k i).1 :=
  fixes_axis k (planeSquaring k) i
    (planeSquaring_X_mem k i _ (Ideal.subset_span (Set.mem_singleton _)))

/-- **The branch divisors of `(z,w) ↦ (z², w²)` are exactly `V(z)` and `V(w)`.** -/
theorem planeSquaring_reducedFiberBranch [CharZero k] :
    schemeReducedFiberBranch (planeSquaring k) = {axisDivisor k 0, axisDivisor k 1} := by
  rw [← divisorSupport_eq_iff, planeSquaring_eq_comp,
    reducedFiberBranch_support_tower, varSquaringMap_reducedFiberBranch,
    varSquaringMap_reducedFiberBranch]
  have himage : varSquaringMap k 0 '' divisorSupport {axisDivisor k 1} =
      divisorSupport {axisDivisor k 1} := by
    simp only [divisorSupport, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]
    rw [← (varSquaringMap k 0).isClosedMap.closure_image_eq_of_continuous
      (varSquaringMap k 0).continuous, Set.image_singleton]
    congr 2
    apply fixes_axis k (varSquaringMap k 0) 1
    change varSquaring k 0 (MvPolynomial.X 1) ∈ Ideal.span {MvPolynomial.X 1}
    rw [varSquaring_X]
    simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [himage, ← divisorSupport_union]
  rfl

end Plane

end Pcf.Examples.CharZeroPaperPinched

#print axioms Pcf.Examples.CharZeroPaperPinched.QuadraticPresentation.fiber_isReduced_iff
#print axioms Pcf.Examples.CharZeroPaperPinched.lineSquaring_reducedFiberBranch
#print axioms Pcf.Examples.CharZeroPaperPinched.lineSquaring_lineOrigin
#print axioms Pcf.Examples.CharZeroPaperPinched.planeSquaring_reducedFiberBranch
#print axioms Pcf.Examples.CharZeroPaperPinched.planeSquaring_axis
