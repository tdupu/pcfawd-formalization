/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.FiniteTypeSingularLocusClosed
public import Pcf.Bounding.RegularQuotientParameters

/-!
# Regular points are smooth over a perfect field

For a regular local ring `R` that is a quotient of a regular local, formally
smooth `k`-algebra `P` with finite free differentials, the local Jacobian
criterion shows `R` is formally smooth over a perfect field `k`. The input is
the regular-quotient bound `I ∩ m² ⊆ m I` (Stacks `00NR`) together with the
split injectivity of `m / m² → κ ⊗ Ω[P/k]` over a perfect field.
-/

@[expose] public section

namespace Pcf

open IsLocalRing KaehlerDifferential TensorProduct

universe u v w

/-- The Jacobian step: a regular local quotient of a regular local, formally
smooth algebra with finite free differentials over a perfect field is formally
smooth. -/
theorem formallySmooth_of_isRegularLocalRing_quotient_of_perfectField
    (k : Type u) (P : Type v) (R : Type w) [Field k] [PerfectField k]
    [CommRing P] [CommRing R] [Algebra k P] [Algebra k R] [Algebra P R]
    [IsScalarTower k P R] [IsRegularLocalRing P] [IsRegularLocalRing R]
    [Algebra.EssFiniteType k R] [Algebra.FormallySmooth k P]
    [Module.Free P Ω[P⁄k]] [Module.Finite P Ω[P⁄k]]
    (h₁ : Function.Surjective (algebraMap P R)) :
    Algebra.FormallySmooth k R := by
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField P h₁
    (IsNoetherian.noetherian _)]
  set I := RingHom.ker (algebraMap P R)
  set K := ResidueField R
  have : IsRegularLocalRing (P ⧸ I) :=
    IsRegularLocalRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective h₁).symm
  have hK : Function.Surjective (algebraMap P K) := by
    rw [IsScalarTower.algebraMap_eq P R K]
    exact residue_surjective.comp h₁
  have : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k R K
  obtain ⟨l, hl⟩ := exists_retraction_kerCotangentToTensor_of_formallySmooth k P K hK
  have hinj : Function.Injective (kerCotangentToTensor k P K) :=
    Function.LeftInverse.injective (fun x ↦ LinearMap.congr_fun hl x)
  set J := RingHom.ker (algebraMap P K)
  have hJ : J ≤ maximalIdeal P := le_maximalIdeal (RingHom.ker_ne_top _)
  have hmJ : maximalIdeal P ≤ J := by
    have : IsLocalHom (algebraMap P K) := IsLocalHom.of_surjective _ hK
    intro a ha
    rw [RingHom.mem_ker]
    by_contra h
    exact ha ((isUnit_map_iff (algebraMap P K) a).mp (Ne.isUnit h))
  -- every element of `K ⊗ I` is `1 ⊗ x`
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective P I K hK y
  have hxJ : (x : P) ∈ J := by
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_eq P R K, RingHom.comp_apply,
      x.2, map_zero]
  have hD : kerCotangentToTensor k P K (J.toCotangent ⟨x, hxJ⟩) = 0 := by
    rw [kerCotangentToTensor_toCotangent]
    rw [TensorProduct.mk_apply, cotangentComplexBaseChange_tmul, one_smul,
      kerToTensor_apply] at hy
    exact hy
  have hx2 : (x : P) ∈ J ^ 2 := by
    exact (Ideal.toCotangent_eq_zero J ⟨x, hxJ⟩).mp (hinj (hD.trans (map_zero _).symm))
  have hxm : (x : P) ∈ I ⊓ maximalIdeal P ^ 2 :=
    ⟨x.2, Ideal.pow_right_mono hJ 2 hx2⟩
  have hxmI : (x : P) ∈ (maximalIdeal P • (⊤ : Submodule P I)).map I.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
    exact inf_sq_le_smul_of_regular_quotient I hxm
  obtain ⟨z, hz, hzx⟩ := hxmI
  have hzx' : z = x := Subtype.ext hzx
  subst hzx'
  have hle : maximalIdeal P • (⊤ : Submodule P I) ≤
      LinearMap.ker (TensorProduct.mk P K I 1) := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [LinearMap.mem_ker, TensorProduct.mk_apply, ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_one, RingHom.mem_ker.mp (hmJ hr), TensorProduct.zero_tmul]
  exact hle hz

/-- Regular-to-smooth at a prime of a finite-type algebra over a perfect field:
the `(2) → (1)` direction of Stacks Lemma 10.140.5.

Divergence from Stacks: Stacks assumes only that the residue field `κ(q)` is
separable over `k`; here `k` is assumed perfect, which makes every residue
field separable. Only the implication regular ⇒ smooth is stated; the converse
is `isRegularLocalRing_of_isSmoothAt`. -/
@[stacks 00TV "(2) ⇒ (1), perfect base field"]
theorem isSmoothAt_of_isRegularLocalRing_of_perfectField
    (k : Type u) (S : Type v) [Field k] [PerfectField k]
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (p : Ideal S) [p.IsPrime] [IsRegularLocalRing (Localization.AtPrime p)] :
    Algebra.IsSmoothAt k p := by
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k S)
  let Q : Ideal (MvPolynomial (Fin n) k) := p.comap f₀
  let P' := Localization.AtPrime Q
  let fP : P' →ₐ[k] Localization.AtPrime p := IsLocalization.liftAlgHom (M := Q.primeCompl)
      (f := (IsScalarTower.toAlgHom k S (Localization.AtPrime p)).comp f₀) fun x ↦ by
    simpa using IsLocalization.map_units (M := p.primeCompl) _ ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := Q.primeCompl) _ x ⟨s, hs⟩, ?_⟩
    simp [fP, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight]
  algebraize [fP.toRingHom]
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) k) P' := .of_isLocalization Q.primeCompl
  have : Algebra.FormallySmooth k P' := .comp _ (MvPolynomial (Fin n) k) _
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial (Fin n) k) P'
  have : Module.Free P' Ω[P'⁄k] := .of_equiv e
  have : Module.Finite P' Ω[P'⁄k] := .equiv e
  have : Algebra.EssFiniteType k (Localization.AtPrime p) :=
    have : Algebra.EssFiniteType S (Localization.AtPrime p) :=
      .of_isLocalization _ p.primeCompl
    .comp k S _
  exact formallySmooth_of_isRegularLocalRing_quotient_of_perfectField k P'
    (Localization.AtPrime p) hf₁

#print axioms formallySmooth_of_isRegularLocalRing_quotient_of_perfectField
#print axioms isSmoothAt_of_isRegularLocalRing_of_perfectField

end Pcf
