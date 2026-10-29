/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPhiGalois
public import Pcf.Bounding.PrimeToPMonodromyOpenSquare
public import Pcf.Bounding.SchemePrimeToPMonodromy

/-!
# Degree and monodromy of `φ = 1 + ι` (`ex:monodromy-loss`)

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: "The isogeny `φ` has degree 2".

* `phi1_finite`: `phi1 : A → A[1/x]` is finite (`x² + i x₃ x - 1 = 0`, `y² = x³ - x`,
  `1/x = x + i x₃`). So `Spec phi1` is `φ` over the chart `U_A`, a finite map.
* `stalkCoord`, `stalkCoord_isFractionRing`, `SpecMap_stalkMap_stalkCoord`: generic stalks of
  affine schemes of domains as fraction fields (as in `FrobeniusPinchingMonodromy`).
* `SpecPhi1_galois`: the actual generic stalk extension of `Spec phi1` is Galois of degree 2.
* **`phi_genericDegree`**: the generic stalk extension of `φ` has degree 2.
* **`phi_isPrimeToPMonodromyMap`**: `φ` has prime-to-`p` monodromy for every prime `p ≠ 2`,
  in particular for `p = 3`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u

section Finite
variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- `A[1/x]` as an `A`-algebra through `phi1` (a type synonym avoiding the localization
algebra structure). -/
def AxPhi (_hi : i ^ 2 = -1) : Type u := Ax k

noncomputable instance : CommRing (AxPhi k i hi) := inferInstanceAs (CommRing (Ax k))
noncomputable instance : Algebra (A k) (AxPhi k i hi) := (phi1 k i hi).toAlgebra

/-- The identity `A[1/x] → AxPhi`. -/
noncomputable def toPhi : Ax k ≃+* AxPhi k i hi := RingEquiv.refl _

theorem algebraMap_AxPhi (a : A k) :
    algebraMap (A k) (AxPhi k i hi) a = toPhi k i hi (phi1 k i hi a) := rfl

instance : Algebra.FiniteType (A k) (AxPhi k i hi) :=
  piece_finiteType k i hi (CommRingCat.ofHom (phi1 k i hi)) (ιA k) _ (ιA k)
    (pieceA_phi1 k i hi).symm

include hi in
theorem AxPhi_isIntegral : Algebra.IsIntegral (A k) (AxPhi k i hi) := by
  set X := algebraMap (A k) (Ax k) (xA k)
  set Y := algebraMap (A k) (Ax k) (yA k)
  set U := invX k
  set c := algebraMap k (Ax k) i
  have hXU : X * U = 1 := Ax_XU k
  have hcc : c ^ 2 = -1 := by
    have := congrArg (algebraMap k (Ax k)) hi; simpa using this
  have hx3 : phi1 k i hi (xA k) = c * (X ^ 2 - 1) * U := liftA_x k _ _ _
  have hc : phi1 k i hi (algebraMap k (A k) i) = c := phi1_algebraMap k i hi i
  -- `X` is integral
  have hX : IsIntegral (A k) (toPhi k i hi X) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (algebraMap k (A k) i * xA k) * Polynomial.X - 1,
      ?_, ?_⟩
    · have : (Polynomial.X ^ 2 + Polynomial.C (algebraMap k (A k) i * xA k) * Polynomial.X - 1 :
          (A k)[X]) = Polynomial.X ^ 2 + (Polynomial.C (algebraMap k (A k) i * xA k) *
            Polynomial.X - 1) := by ring
      rw [this]
      apply Polynomial.monic_X_pow_add
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by decide)
      · rw [degree_one]; decide
    · rw [← aeval_def]
      simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, map_one]
      have hroot :
          X ^ 2 + phi1 k i hi (algebraMap k (A k) i) * phi1 k i hi (xA k) * X - 1 = 0 := by
        rw [hc, hx3]
        linear_combination (X ^ 2 - 1) * hcc + c ^ 2 * (X ^ 2 - 1) * hXU
      exact hroot
  have hA : ∀ a : A k, IsIntegral (A k) (toPhi k i hi (phi1 k i hi a)) := fun a =>
    isIntegral_algebraMap (x := a)
  have hU : IsIntegral (A k) (toPhi k i hi U) := by
    have : U = X + phi1 k i hi (algebraMap k (A k) i * xA k) := by
      rw [map_mul, hc, hx3]
      linear_combination X * hXU - (X ^ 2 - 1) * U * hcc
    rw [this, map_add]
    exact hX.add (hA _)
  have hY : IsIntegral (A k) (toPhi k i hi Y) := by
    have hY2 : toPhi k i hi Y ^ 2 = toPhi k i hi X ^ 3 - toPhi k i hi X := by
      exact Ax_Yrel k
    exact IsIntegral.of_pow (n := 2) (by decide) (hY2 ▸ (hX.pow 3).sub hX)
  have hloc : ∀ a : A k, IsIntegral (A k) (toPhi k i hi (algebraMap (A k) (Ax k) a)) := by
    intro a
    have ha : a ∈ Algebra.adjoin k {xA k, yA k} := by rw [A_adjoin]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact hX
      · exact hY
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply, ← phi1_algebraMap k i hi]
      exact hA _
    | add a b _ _ ha hb => rw [map_add, map_add]; exact ha.add hb
    | mul a b _ _ ha hb => rw [map_mul, map_mul]; exact ha.mul hb
  refine ⟨fun s => ?_⟩
  obtain ⟨⟨a, t⟩, hs⟩ := IsLocalization.mk'_surjective (Submonoid.powers (xA k))
    ((toPhi k i hi).symm s)
  obtain ⟨n, hn⟩ := t.2
  have : IsLocalization.mk' (Ax k) a t = algebraMap (A k) (Ax k) a * invX k ^ n := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, mul_assoc, ← hn, map_pow, ← mul_pow,
      mul_comm (invX k), Ax_XU, one_pow, mul_one]
  have hs' : s = toPhi k i hi (algebraMap (A k) (Ax k) a * invX k ^ n) := by
    rw [← this]; exact ((toPhi k i hi).symm_apply_eq.mp hs.symm).symm ▸ rfl
  rw [hs', map_mul, map_pow]
  exact (hloc a).mul (hU.pow n)

include hi in
/-- **`phi1` is finite**: `Spec phi1` is `φ` over the chart `U_A`. -/
theorem phi1_finite : (phi1 k i hi).Finite := by
  haveI := AxPhi_isIntegral k i hi
  exact (Algebra.IsIntegral.finite : Module.Finite (A k) (AxPhi k i hi))

instance SpecPhi1_isFinite : IsFinite (Spec.map (CommRingCat.ofHom (phi1 k i hi))) := by
  rw [IsFinite.SpecMap_iff]; exact phi1_finite k i hi

end Finite

section Stalks
variable {R : Type u} [CommRing R]

/-- The coordinate map into a stalk of an affine scheme through `Spec.stalkIso`. -/
noncomputable def stalkCoord (q : Spec (.of R)) : R →+* (Spec (.of R)).presheaf.stalk q :=
  (Spec.stalkIso (.of R) q).inv.hom.comp (algebraMap R (Localization.AtPrime q.asIdeal))

theorem stalkCoord_isFractionRing [IsDomain R] (q : Spec (.of R)) (hq : q.asIdeal = ⊥) :
    @IsFractionRing R _ ((Spec (.of R)).presheaf.stalk q) _ (stalkCoord q).toAlgebra := by
  have h : q.asIdeal.primeCompl = nonZeroDivisors R := by
    ext r; simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero, hq]
  haveI : IsFractionRing R (Localization.AtPrime q.asIdeal) := by
    unfold IsFractionRing; rw [← h]; infer_instance
  letI : Algebra R ((Spec (.of R)).presheaf.stalk q) := (stalkCoord q).toAlgebra
  let e : Localization.AtPrime q.asIdeal ≃ₐ[R] (Spec (.of R)).presheaf.stalk q :=
    { (Spec.stalkIso (.of R) q).symm.commRingCatIsoToRingEquiv with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors R) e

/-- The stalk map of `Spec f` restricts to `f` on coordinates. -/
theorem SpecMap_stalkMap_stalkCoord {S : Type u} [CommRing S] (f : R →+* S)
    (q : Spec (.of S)) (a : R) :
    (Spec.map (CommRingCat.ofHom f)).stalkMap q
        (stalkCoord (Spec.map (CommRingCat.ofHom f) q) a) = stalkCoord q (f a) := by
  rw [← Scheme.localRingHom_comp_stalkIso]
  simp only [stalkCoord, RingHom.comp_apply, CommRingCat.comp_apply]
  erw [Iso.inv_hom_id_apply]
  rw [ConcreteCategory.comp_apply]
  congr 1
  exact Localization.localRingHom_to_map _ _ _ rfl a

theorem genericPoint_asIdeal_Spec [IsDomain R] :
    (genericPoint (Spec (.of R))).asIdeal = ⊥ := by
  rw [genericPoint_eq_bot_of_affine]
  rfl

end Stalks

section Monodromy
variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- `Spec phi1 : Spec A[1/x] ⟶ Spec A`. -/
noncomputable abbrev SpecPhi1 : Spec (.of (Ax k)) ⟶ Spec (.of (A k)) :=
  Spec.map (CommRingCat.ofHom (phi1 k i hi))

theorem SpecPhi1_genericPoint_asIdeal :
    (SpecPhi1 k i hi (genericPoint (Spec (.of (Ax k))))).asIdeal = ⊥ := by
  change ((genericPoint (Spec (.of (Ax k)))).asIdeal).comap (phi1 k i hi) = ⊥
  rw [genericPoint_asIdeal_Spec]
  ext a
  simp only [Ideal.mem_comap, Ideal.mem_bot]
  exact ⟨fun h => phi1_injective k i hi (h.trans (map_zero _).symm), fun h => by simp [h]⟩

/-- **The generic stalk extension of `Spec phi1` is Galois of degree 2.** -/
theorem SpecPhi1_galois
    (hF : IsField ((Spec (.of (A k))).presheaf.stalk
      (SpecPhi1 k i hi (genericPoint (Spec (.of (Ax k))))))) :
    letI := hF.toField
    letI := ((SpecPhi1 k i hi).stalkMap (genericPoint (Spec (.of (Ax k))))).hom.toAlgebra
    IsGalois ((Spec (.of (A k))).presheaf.stalk
        (SpecPhi1 k i hi (genericPoint (Spec (.of (Ax k))))))
      ((Spec (.of (Ax k))).presheaf.stalk (genericPoint (Spec (.of (Ax k))))) ∧
    Module.finrank ((Spec (.of (A k))).presheaf.stalk
        (SpecPhi1 k i hi (genericPoint (Spec (.of (Ax k))))))
      ((Spec (.of (Ax k))).presheaf.stalk (genericPoint (Spec (.of (Ax k))))) = 2 := by
  letI := hF.toField
  letI := ((SpecPhi1 k i hi).stalkMap (genericPoint (Spec (.of (Ax k))))).hom.toAlgebra
  refine galois_of_phi1 k i hi (stalkCoord _) (stalkCoord _)
    (stalkCoord_isFractionRing _ (SpecPhi1_genericPoint_asIdeal k i hi))
    (stalkCoord_isFractionRing _ genericPoint_asIdeal_Spec) ?_
  apply RingHom.ext
  intro a
  exact SpecMap_stalkMap_stalkCoord (phi1 k i hi) _ a

end Monodromy

section MonodromyPhi
variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- **`Spec phi1` has prime-to-`p` monodromy** for every prime `p ≠ 2`. -/
theorem SpecPhi1_isPrimeToPMonodromyMap (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Pcf.IsPrimeToPMonodromyMap p (SpecPhi1 k i hi) := by
  let X := Spec (.of (Ax k))
  let f := SpecPhi1 k i hi
  have hgp : f (genericPoint X) = genericPoint (Spec (.of (A k))) :=
    Pcf.map_genericPoint_eq_of_isDominant f
  let e := ((Spec (.of (A k))).presheaf.stalkCongr
    (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hF : IsField ((Spec (.of (A k))).presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field ((Spec (.of (A k))).presheaf.stalk (f (genericPoint X))) := hF.toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  change Pcf.IsPrimeToPMonodromy.{u, u, u} p
    ((Spec (.of (A k))).presheaf.stalk (f (genericPoint X))) (X.presheaf.stalk (genericPoint X))
  obtain ⟨hgal, hfin⟩ := SpecPhi1_galois k i hi hF
  haveI := hgal
  haveI : FiniteDimensional ((Spec (.of (A k))).presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) := Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
  refine Pcf.isPrimeToPMonodromy_of_embedding_into_galois p _ _ _ (AlgHom.id _ _) ?_
  rw [hfin]
  exact (Nat.coprime_primes Nat.prime_two Fact.out).mpr hp2.symm

/-- The chart `D(x) ⊂ E`. -/
noncomputable abbrev chartDx : Spec (.of (Ax k)) ⟶ E k :=
  Spec.map (CommRingCat.ofHom (algebraMap (A k) (Ax k))) ≫ ιA k

instance chartDx_isDominant : IsDominant (chartDx k) := by
  constructor
  have hne : (Set.range (chartDx k)).Nonempty := ⟨_, ⟨⊥, Ideal.isPrime_bot⟩, rfl⟩
  exact ((chartDx k).isOpenEmbedding.isOpenMap.isOpen_range).dense hne

theorem square_phi : SpecPhi1 k i hi ≫ ιA k = chartDx k ≫ phi k i hi := by
  rw [Category.assoc]; exact (pieceA_phi1 k i hi).symm

/-- **Degree 2.** The actual generic stalk extension of `φ` has degree `2`.

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem phi_genericDegree :
    letI := ((phi k i hi).stalkMap (genericPoint (E k))).hom.toAlgebra
    Module.finrank ((E k).presheaf.stalk (phi k i hi (genericPoint (E k))))
      ((E k).presheaf.stalk (genericPoint (E k))) = 2 := by
  have hz : chartDx k (genericPoint (Spec (.of (Ax k)))) = genericPoint (E k) :=
    Pcf.map_genericPoint_eq_of_isDominant (chartDx k)
  obtain ⟨eE, eK, hcomm⟩ := Pcf.exists_stalkEquivs_of_square (SpecPhi1 k i hi) (chartDx k)
    (ιA k) (phi k i hi) (square_phi k i hi) (genericPoint _) hz
    (ConcreteCategory.bijective_of_isIso _) (ConcreteCategory.bijective_of_isIso _)
  letI := ((phi k i hi).stalkMap (genericPoint (E k))).hom.toAlgebra
  letI := ((SpecPhi1 k i hi).stalkMap (genericPoint (Spec (.of (Ax k))))).hom.toAlgebra
  -- the degree on the chart
  let X := Spec (.of (Ax k))
  let f := SpecPhi1 k i hi
  have hgp : f (genericPoint X) = genericPoint (Spec (.of (A k))) :=
    Pcf.map_genericPoint_eq_of_isDominant f
  let e := ((Spec (.of (A k))).presheaf.stalkCongr
    (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hF : IsField ((Spec (.of (A k))).presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  obtain ⟨-, hfin⟩ := SpecPhi1_galois k i hi hF
  rw [Algebra.finrank_eq_of_equiv_equiv eK eE hcomm]
  exact hfin

/-- **`φ` has prime-to-`p` monodromy** for every prime `p ≠ 2`: its function-field extension
is Galois of degree 2. -/
theorem phi_isPrimeToPMonodromyMap (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Pcf.IsPrimeToPMonodromyMap p (phi k i hi) := by
  obtain ⟨eE, eK, hcomm⟩ := Pcf.exists_stalkEquivs_of_square (SpecPhi1 k i hi) (chartDx k)
    (ιA k) (phi k i hi) (square_phi k i hi) (genericPoint _)
    (Pcf.map_genericPoint_eq_of_isDominant (chartDx k))
    (ConcreteCategory.bijective_of_isIso _) (ConcreteCategory.bijective_of_isIso _)
  refine Pcf.isPrimeToPMonodromyMap_of_genericStalkEquivs p (SpecPhi1 k i hi) (phi k i hi)
    eK.symm eE.symm ?_ (SpecPhi1_isPrimeToPMonodromyMap k i hi p hp2)
  apply RingHom.ext
  intro y
  have := congrArg (fun φ => φ (eK.symm y)) hcomm
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply] at this
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [this, RingEquiv.symm_apply_apply]

end MonodromyPhi

#print axioms phi1_finite
#print axioms SpecPhi1_isPrimeToPMonodromyMap
#print axioms phi_genericDegree
#print axioms phi_isPrimeToPMonodromyMap

end Pcf.Examples.PaperP.MonodromyLossCurve
