/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.CharPExceptionalBlowup
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.CharP.Algebra

/-!
# The exceptional divisor and its geometric generic fibre

For `paper-p.tex`, Example `ex:charp-exceptional-fibre-paper`: on the actual `y`-chart of
`Bl_A(X)` (`CharPExceptionalBlowup`), the exceptional divisor `D = V(y)` has coordinate
ring `k[u,v]`, the centre `A` has coordinate ring `k[t]`, and the restriction of the
blow-up map `D → A` is `t ↦ u^p`. In characteristic `p`, the geometric generic fibre
`D ×_A Spec \overline{k(t)}` is not reduced: `1 ⊗ u - t^{1/p} ⊗ 1` is a nonzero
nilpotent.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CharPExceptionalFibre

open MvPolynomial
open Pcf.Examples.PaperP.CharPExceptionalBlowup
open Pcf.Examples.PaperP.CharPExceptionalChart (ChartBase)
open scoped TensorProduct

set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ)

/-- A ring hom with a section whose defect lies in `J ≤ ker` has kernel `J`. -/
theorem ker_eq_of_section {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (σ : B →+* A)
    (J : Ideal A) (hJ : J ≤ RingHom.ker f) (hdef : ∀ a, a - σ (f a) ∈ J)
    (_hfσ : ∀ b, f (σ b) = b) : RingHom.ker f = J := by
  refine le_antisymm (fun a ha => ?_) hJ
  have h := hdef a
  rw [RingHom.mem_ker.mp ha, map_zero, sub_zero] at h
  exact h

/-! ### The centre `A = Spec k[t]` -/

/-- The coordinate ring of `A`: `x, y, z ↦ 0`, `t ↦ T`. -/
noncomputable def centerCoord (hp : 0 < p) : HyperRing k p →ₐ[k] Polynomial k :=
  Ideal.Quotient.liftₐ _ (aeval ![0, 0, 0, Polynomial.X]) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    have : aeval ![0, 0, 0, (Polynomial.X : Polynomial k)] (hyperEquation k p) = 0 := by
      simp [hyperEquation, zero_pow hp.ne']
    rw [this, mul_zero])

theorem centerCoord_mk (hp : 0 < p) (q : Ambient k) :
    centerCoord k p hp (Ideal.Quotient.mk _ q) = aeval ![0, 0, 0, Polynomial.X] q := rfl

/-- The section `T ↦ t`. -/
noncomputable def centerSection : Polynomial k →ₐ[k] HyperRing k p := Polynomial.aeval (ht k p)

theorem centerCoord_section (hp : 0 < p) (b : Polynomial k) :
    centerCoord k p hp (centerSection k p b) = b := by
  have h : (centerCoord k p hp).comp (centerSection k p) = AlgHom.id k _ := by
    apply Polynomial.algHom_ext
    simp [centerSection, ht, centerCoord_mk]
  exact congrArg (fun g : Polynomial k →ₐ[k] Polynomial k => g b) h

/-- The centre `A` is `Spec k[t]`: the kernel of `centerCoord` is the ideal `(x,y,z)`. -/
theorem centerCoord_ker (hp : 0 < p) :
    RingHom.ker (centerCoord k p hp).toRingHom = center k p := by
  apply ker_eq_of_section (centerCoord k p hp).toRingHom (centerSection k p).toRingHom
  · rw [center, Ideal.span_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl <;>
      simp [RingHom.mem_ker, hx, hy, hz, centerCoord_mk]
  · intro a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction q using MvPolynomial.induction_on with
    | C c =>
        change _ - centerSection k p (centerCoord k p hp (Ideal.Quotient.mk _ (C c))) ∈ _
        rw [centerCoord_mk, aeval_C, AlgHom.commutes,
          show (Ideal.Quotient.mk _ (C c) : HyperRing k p) = algebraMap k _ c from rfl, sub_self]
        exact zero_mem _
    | add a b ha hb =>
        simp only [map_add, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at ha hb ⊢
        convert add_mem ha hb using 1
        ring
    | mul_X a i ha =>
        simp only [map_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at ha ⊢
        set m := Ideal.Quotient.mk (Ideal.span {hyperEquation k p}) a
        set c := centerSection k p (centerCoord k p hp m)
        set xi := Ideal.Quotient.mk (Ideal.span {hyperEquation k p}) (X i : Ambient k)
        have hxi : xi - centerSection k p (centerCoord k p hp xi) ∈ center k p := by
          fin_cases i
          · have hmem : hx k p ∈ center k p := Ideal.subset_span (by simp)
            simpa [xi, centerCoord_mk, centerSection, hx] using hmem
          · have hmem : hy k p ∈ center k p := Ideal.subset_span (by simp)
            simpa [xi, centerCoord_mk, centerSection, hy] using hmem
          · have hmem : hz k p ∈ center k p := Ideal.subset_span (by simp)
            simpa [xi, centerCoord_mk, centerSection, hz] using hmem
          · simp [xi, centerCoord_mk, centerSection, ht]
        have : m * xi - c * centerSection k p (centerCoord k p hp xi) =
            (m - c) * xi + c * (xi - centerSection k p (centerCoord k p hp xi)) := by ring
        rw [this]
        exact add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hxi)
  · exact centerCoord_section k p hp

/-! ### The exceptional divisor `D = Spec k[u,v]` -/

/-- Restriction to `y = 0` on the chart: `y ↦ 0`, `u ↦ u`, `v ↦ v`. -/
noncomputable def exceptionalCoord : ChartBase k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![0, X 0, X 1]

noncomputable def exceptionalSection : MvPolynomial (Fin 2) k →ₐ[k] ChartBase k :=
  aeval ![X 1, X 2]

theorem exceptionalCoord_section (b : MvPolynomial (Fin 2) k) :
    exceptionalCoord k (exceptionalSection k b) = b := by
  have h : (exceptionalCoord k).comp (exceptionalSection k) = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [exceptionalCoord, exceptionalSection]
  exact congrArg (fun g : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k => g b) h

/-- `D = V(y)` has coordinate ring `k[u,v]`. -/
theorem exceptionalCoord_ker :
    RingHom.ker (exceptionalCoord k).toRingHom = Ideal.span {(X 0 : ChartBase k)} := by
  apply ker_eq_of_section (exceptionalCoord k).toRingHom (exceptionalSection k).toRingHom
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp [RingHom.mem_ker, exceptionalCoord]
  · intro a
    induction a using MvPolynomial.induction_on with
    | C c => simp [exceptionalCoord, exceptionalSection]
    | add a b ha hb =>
        simp only [map_add, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at ha hb ⊢
        convert add_mem ha hb using 1
        ring
    | mul_X a i ha =>
        simp only [map_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at ha ⊢
        set c := exceptionalSection k (exceptionalCoord k a)
        have hxi : (X i : ChartBase k) - exceptionalSection k (exceptionalCoord k (X i)) ∈
            Ideal.span {(X 0 : ChartBase k)} := by
          fin_cases i
          · simp [exceptionalCoord]
          · simp [exceptionalCoord, exceptionalSection]
          · simp [exceptionalCoord, exceptionalSection]
        have : a * X i - c * exceptionalSection k (exceptionalCoord k (X i)) =
            (a - c) * X i + c * (X i - exceptionalSection k (exceptionalCoord k (X i))) := by
          ring
        rw [this]
        exact add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hxi)
  · exact exceptionalCoord_section k

/-- On the actual chart, `D` is cut out by the pulled-back centre: the kernel of the
restriction `R[I/y] → k[u,v]` is `I·R[I/y]`. -/
theorem exceptionalDivisor_ker :
    RingHom.ker ((exceptionalCoord k).toRingHom.comp (chartEquiv k p).symm.toRingHom) =
      (center k p).map (algebraMap (HyperRing k p) (YChart k p)) := by
  rw [← RingHom.comap_ker, exceptionalCoord_ker]
  rw [exceptionalIdeal_eq]
  ext q
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  change X 0 ∣ (chartEquiv k p).symm q ↔ _
  rw [← map_dvd_iff (chartEquiv k p), RingEquiv.apply_symm_apply]

/-- The map `D → A` is `t ↦ u^p`. -/
noncomputable def fibreMap : Polynomial k →ₐ[k] MvPolynomial (Fin 2) k :=
  Polynomial.aeval (X 0 ^ p)

/-- **The restriction of the blow-up `D → A` is `t ↦ u^p`.** Restricting a function on
`X` to the chart and then to `D` equals restricting it to `A = Spec k[t]` and pulling
back along `t ↦ u^p`.

`paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
theorem exceptional_square (hp : 0 < p) (r : HyperRing k p) :
    exceptionalCoord k ((chartEquiv k p).symm (algebraMap (HyperRing k p) (YChart k p) r)) =
      fibreMap k p (centerCoord k p hp r) := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction q using MvPolynomial.induction_on with
  | C c =>
      rw [centerCoord_mk, aeval_C, AlgHom.commutes]
      rw [show Ideal.Quotient.mk (Ideal.span {hyperEquation k p}) (C c) =
        algebraMap k (HyperRing k p) c from rfl,
        ← IsScalarTower.algebraMap_apply k (HyperRing k p) (YChart k p)]
      have : (chartEquiv k p).symm (algebraMap k (YChart k p) c) = C c := by
        apply (chartEquiv k p).injective
        rw [RingEquiv.apply_symm_apply]
        apply Subtype.ext
        change _ = chartCoords k p (C c)
        rw [chartCoords, aeval_C]
        rfl
      rw [this, exceptionalCoord, aeval_C]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a i ha =>
      simp only [map_mul, ha]
      congr 1
      fin_cases i
      · change exceptionalCoord k ((chartEquiv k p).symm
          (algebraMap (HyperRing k p) (YChart k p) (hx k p))) = _
        rw [chart_x_eq, RingEquiv.symm_apply_apply]
        simp [exceptionalCoord, centerCoord_mk, fibreMap]
      · change exceptionalCoord k ((chartEquiv k p).symm
          (algebraMap (HyperRing k p) (YChart k p) (hy k p))) = _
        rw [← chartEquiv_X0, RingEquiv.symm_apply_apply]
        simp [exceptionalCoord, centerCoord_mk, fibreMap]
      · change exceptionalCoord k ((chartEquiv k p).symm
          (algebraMap (HyperRing k p) (YChart k p) (hz k p))) = _
        rw [chart_z_eq, RingEquiv.symm_apply_apply]
        simp [exceptionalCoord, centerCoord_mk, fibreMap]
      · change exceptionalCoord k ((chartEquiv k p).symm
          (algebraMap (HyperRing k p) (YChart k p) (ht k p))) = _
        rw [chart_t_eq, RingEquiv.symm_apply_apply]
        simp [exceptionalCoord, centerCoord_mk, fibreMap]

/-! ### The geometric generic fibre is not reduced -/

/-- `k[u,v]` as an algebra over `k[t]` through `D → A`. -/
def FibreRing (k : Type*) [Field k] (_p : ℕ) := MvPolynomial (Fin 2) k

noncomputable instance : CommRing (FibreRing k p) := inferInstanceAs (CommRing (MvPolynomial _ _))

noncomputable instance : Algebra (Polynomial k) (FibreRing k p) :=
  (fibreMap k p).toRingHom.toAlgebra

/-- The fibre coordinate `u`. -/
noncomputable def fibreU : FibreRing k p := (X 0 : MvPolynomial (Fin 2) k)

theorem fibre_algebraMap_X :
    algebraMap (Polynomial k) (FibreRing k p) Polynomial.X = fibreU k p ^ p := by
  change fibreMap k p Polynomial.X = _
  rw [fibreMap, Polynomial.aeval_X]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Nonreduced geometric fibre.** For any field `L` over `k[t]` of characteristic `p` in
which `t` has a `p`-th root `s`, the fibre `L ⊗_{k[t]} k[u,v]` of `D → A` is not
reduced: `1 ⊗ u - s ⊗ 1` is a nonzero nilpotent.

`paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
theorem fibre_not_isReduced [hp : Fact p.Prime] (L : Type*) [Field L]
    [Algebra (Polynomial k) L] [CharP L p] (s : L)
    (hs : s ^ p = algebraMap (Polynomial k) L Polynomial.X) :
    ¬ IsReduced (L ⊗[Polynomial k] FibreRing k p) := by
  have hp2 := hp.out.two_le
  let g : Polynomial L := (Polynomial.X - Polynomial.C s) ^ p
  let Q := AdjoinRoot g
  have hgdeg : g.natDegree = p := by
    simp [g, Polynomial.natDegree_pow]
  haveI : Nontrivial Q := AdjoinRoot.nontrivial g (by
    rw [Polynomial.degree_eq_natDegree (by simp [g, Polynomial.X_sub_C_ne_zero]), hgdeg]
    exact_mod_cast hp.out.ne_zero)
  haveI : CharP Q p := charP_of_injective_algebraMap (algebraMap L Q).injective p
  have hroot : (AdjoinRoot.root g - algebraMap L Q s) ^ p = 0 := by
    have := AdjoinRoot.eval₂_root g
    rw [AdjoinRoot.algebraMap_eq]
    simpa [g, Polynomial.eval₂_pow] using this
  have hroot' : AdjoinRoot.root g ^ p = algebraMap L Q (s ^ p) := by
    rw [sub_pow_char, sub_eq_zero] at hroot
    rw [map_pow]
    exact hroot
  let f₁ : L →ₐ[Polynomial k] Q := IsScalarTower.toAlgHom _ _ _
  let φ : MvPolynomial (Fin 2) k →+* Q :=
    MvPolynomial.eval₂Hom ((algebraMap (Polynomial k) Q).comp Polynomial.C)
      ![AdjoinRoot.root g, 0]
  have hφ : ∀ a : Polynomial k, φ (fibreMap k p a) = algebraMap (Polynomial k) Q a := by
    have h : φ.comp (fibreMap k p).toRingHom = algebraMap (Polynomial k) Q := by
      apply Polynomial.ringHom_ext
      · intro c
        change φ (fibreMap k p (Polynomial.C c)) = _
        rw [fibreMap, Polynomial.aeval_C, MvPolynomial.algebraMap_eq]
        simp only [φ, eval₂Hom_C, RingHom.comp_apply]
      · change φ (fibreMap k p Polynomial.X) = _
        rw [fibreMap, Polynomial.aeval_X, map_pow]
        simp only [φ, eval₂Hom_X', Matrix.cons_val_zero]
        rw [hroot', hs, ← IsScalarTower.algebraMap_apply]
    exact fun a => congrArg (fun f => f a) h
  let g₁ : FibreRing k p →ₐ[Polynomial k] Q := { φ with commutes' := hφ }
  let Φ := Algebra.TensorProduct.productMap f₁ g₁
  haveI : Nontrivial (L ⊗[Polynomial k] FibreRing k p) := Φ.toRingHom.domain_nontrivial
  haveI : CharP (L ⊗[Polynomial k] FibreRing k p) p :=
    charP_of_injective_algebraMap
      (algebraMap L (L ⊗[Polynomial k] FibreRing k p)).injective p
  let w : L ⊗[Polynomial k] FibreRing k p :=
    (1 : L) ⊗ₜ[Polynomial k] fibreU k p - s ⊗ₜ[Polynomial k] (1 : FibreRing k p)
  have hw : w ^ p = 0 := by
    simp only [w, sub_pow_char, Algebra.TensorProduct.tmul_pow, one_pow]
    rw [hs, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      Algebra.smul_def, mul_one, fibre_algebraMap_X, sub_self]
  have hw0 : w ≠ 0 := by
    intro h0
    have := congrArg Φ h0
    rw [map_zero] at this
    have hΦ : Φ w = AdjoinRoot.root g - algebraMap L Q s := by
      simp only [w, map_sub, Φ, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one,
        one_mul]
      congr 1
      change φ (X 0) = _
      simp [φ]
    rw [hΦ, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_X, ← AdjoinRoot.mk_C, ← map_sub,
      AdjoinRoot.mk_eq_zero] at this
    have hle := Polynomial.natDegree_le_of_dvd this (Polynomial.X_sub_C_ne_zero s)
    rw [hgdeg, Polynomial.natDegree_X_sub_C] at hle
    omega
  intro hred
  exact hw0 (hred.eq_zero w ⟨p, hw⟩)

/-- **`ex:charp-exceptional-fibre-paper`, geometric generic fibre.** Over the algebraic
closure of the function field `k(t)` of `A`, the fibre of `D → A` is not reduced.

`paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
theorem geometricGenericFibre_not_isReduced [Fact p.Prime] [CharP k p] :
    ¬ IsReduced (AlgebraicClosure (RatFunc k) ⊗[Polynomial k] FibreRing k p) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (Polynomial k) (AlgebraicClosure (RatFunc k)) Polynomial.X)
    (Fact.out : p.Prime).pos
  exact fibre_not_isReduced k p _ s hs

#print axioms ker_eq_of_section
#print axioms centerCoord_ker
#print axioms exceptionalCoord_ker
#print axioms exceptionalDivisor_ker
#print axioms exceptional_square
#print axioms fibre_not_isReduced
#print axioms geometricGenericFibre_not_isReduced

end Pcf.Examples.PaperP.CharPExceptionalFibre
