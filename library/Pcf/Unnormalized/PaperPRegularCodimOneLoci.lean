/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.PaperPCodimOneNormalLoci
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular in codimension one

On an integral locally Noetherian scheme the local ring at a codimension-one
point is a one-dimensional Noetherian local domain, so it is regular exactly
when it is a DVR, exactly when it is integrally closed. This turns the
integrally-closed hypotheses of `PaperPCodimOneNormalLoci` into the source's
literal "regular in codimension one" (`paper-p.tex`, l. 2227–2229 and
l. 2375–2378).
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

noncomputable section

/-- At a codimension-one point of an integral locally Noetherian scheme the
local ring is regular iff it is integrally closed (both iff DVR). -/
theorem isRegularLocalRing_stalk_iff_isIntegrallyClosed
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (P : SchemeDivisorPoint X) :
    IsRegularLocalRing (X.presheaf.stalk P.1) ↔
      IsIntegrallyClosed (X.presheaf.stalk P.1) := by
  let R := X.presheaf.stalk P.1
  have hdim : ringKrullDim R = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, P.2]; rfl
  have hnf : ¬ IsField R := by
    intro h
    let := h.toField
    rw [ringKrullDim_eq_zero_of_field] at hdim
    exact zero_ne_one hdim
  have tfae := tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R
  have hprime : ∀ Q : Ideal R, Q ≠ ⊥ → Q.IsPrime → Q = maximalIdeal R := by
    intro Q hQ hQp
    by_contra hne
    let p0 : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
    let q : PrimeSpectrum R := ⟨Q, hQp⟩
    let m : PrimeSpectrum R := ⟨maximalIdeal R, inferInstance⟩
    have h1 : p0 < q := by
      change (⊥ : Ideal R) < Q
      exact bot_lt_iff_ne_bot.mpr hQ
    have h2 : q < m := by
      change Q < maximalIdeal R
      exact lt_of_le_of_ne (le_maximalIdeal hQp.ne_top) hne
    have ha := Order.height_add_one_le h1
    have hb := Order.height_add_one_le h2
    have hc := Order.height_le_krullDim m
    have hd : Order.krullDim (PrimeSpectrum R) = 1 := hdim
    rw [hd] at hc
    have hm : Order.height m ≤ 1 := by exact_mod_cast hc
    have : (2 : ℕ∞) ≤ Order.height m := by
      calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ Order.height p0 + 1 + 1 := by gcongr; exact bot_le
        _ ≤ Order.height q + 1 := by gcongr
        _ ≤ Order.height m := hb
    have := this.trans hm
    norm_num at this
  constructor
  · intro hreg
    have h1 : (maximalIdeal R).spanFinrank = 1 := by
      have := hreg.spanFinrank_maximalIdeal
      rw [hdim] at this
      exact_mod_cast this
    have hpr : (maximalIdeal R).IsPrincipal :=
      ((Submodule.spanFinrank_eq_one_iff _).mp h1).1
    have h54 := tfae.out 5 4
    exact (h54.mp hpr).1
  · intro hic
    have h41 := tfae.out 4 1
    have : IsPrincipalIdealRing R := h41.mp ⟨hic, hprime⟩
    infer_instance

/-- **l. 2227–2229**, literal form: in characteristic zero, if `A` and `B` are
regular in codimension one then `branch(g) = branch₀(g) = branch₁(g)`. -/
theorem weightedBranchPointSet_eq_unnormalized_of_regularInCodimOne
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)] [IsFinite (Palomar.normalizationMap Y)]
    (k : Type u) [Field k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (hX : ∀ P : SchemeDivisorPoint X, IsRegularLocalRing (X.presheaf.stalk P.1))
    (hY : ∀ Q : SchemeDivisorPoint Y, IsRegularLocalRing (Y.presheaf.stalk Q.1)) :
    weightedBranchPointSet g =
        {y : Y | ∃ E ∈ schemeUnnormalizedBranchZero g, E.1 = y} ∧
    {y : Y | ∃ E ∈ schemeUnnormalizedBranchZero g, E.1 = y} =
        {y : Y | ∃ E ∈ schemeUnnormalizedBranchOne g, E.1 = y} :=
  weightedBranchPointSet_eq_unnormalized_of_codimOne_normal g k sX sY
    (fun P => (isRegularLocalRing_stalk_iff_isIntegrallyClosed P).mp (hX P))
    (fun Q => (isRegularLocalRing_stalk_iff_isIntegrallyClosed Q).mp (hY Q))

/-- **l. 2375–2378**, literal form: in characteristic zero, if `X` is regular
in codimension one then `PC`, `PC₀`, `PC₁` have the same generic points and
PCF, `0`-PCF, `1`-PCF coincide. -/
theorem postcritical_coincide_of_regularInCodimOne
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hX : ∀ P : SchemeDivisorPoint X, IsRegularLocalRing (X.presheaf.stalk P.1)) :
    letI : IsFinite (Palomar.normalizationMap X) := schemeGlobalNormalizationMap_isFinite X k s
    (weightedPostcriticalPointSet f =
        Subtype.val '' schemeUnnormalizedPostcriticalSet false k s f ∧
      Subtype.val '' schemeUnnormalizedPostcriticalSet false k s f =
        Subtype.val '' schemeUnnormalizedPostcriticalSet true k s f) ∧
    (IsWeightedNormalizedPCFDownstairs k s f ↔ IsSchemeUnnormalizedPCF false k s f) ∧
    (IsSchemeUnnormalizedPCF false k s f ↔ IsSchemeUnnormalizedPCF true k s f) :=
  postcritical_coincide_of_codimOne_normal k s f
    (fun P => (isRegularLocalRing_stalk_iff_isIntegrallyClosed P).mp (hX P))

#print axioms isRegularLocalRing_stalk_iff_isIntegrallyClosed
#print axioms weightedBranchPointSet_eq_unnormalized_of_regularInCodimOne
#print axioms postcritical_coincide_of_regularInCodimOne

end

end Pcf
