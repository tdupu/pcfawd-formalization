/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.InvariantDivisorGeometry
public import Pcf.Bounding.SmoothRegularLocal
public import Pcf.Bounding.PrincipalQuotientRegular
public import Pcf.Stacks.Common.AffineBasicOpen

/-!
# Finite regularity corrections on a divisor

Principal generation at a prime spreads to a principal open neighborhood. Together
with generic smoothness of the reduced divisor, this gives a smaller route to the
regularity correction needed by the invariant-divisor argument.
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

/-- A finitely generated ideal that is principal at a prime is principal throughout
some principal open neighborhood of that prime, with one generator from the original
ideal. -/
theorem exists_principalOpen_map_eq_span_of_isPrincipal_atPrime
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (p : Ideal R) [p.IsPrime]
    [(I.map (algebraMap R (Localization.AtPrime p))).IsPrincipal] :
    ∃ a ∈ I, ∃ f : R, f ∉ p ∧
      ∀ (q : Ideal R) [q.IsPrime], f ∉ q →
        I.map (algebraMap R (Localization.AtPrime q)) =
          Ideal.span {algebraMap R (Localization.AtPrime q) a} := by
  classical
  obtain ⟨b, hb⟩ := (inferInstance :
    (I.map (algebraMap R (Localization.AtPrime p))).IsPrincipal)
  change I.map (algebraMap R (Localization.AtPrime p)) = Ideal.span {b} at hb
  have hbmem : b ∈ I.map (algebraMap R (Localization.AtPrime p)) :=
    hb ▸ Ideal.subset_span (Set.mem_singleton b)
  obtain ⟨⟨a, t⟩, hat⟩ :=
    (IsLocalization.mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p)).mp hbmem
  rcases a with ⟨a, ha⟩
  have haeq : I.map (algebraMap R (Localization.AtPrime p)) =
      Ideal.span {algebraMap R (Localization.AtPrime p) a} := by
    rw [hb, ← hat, Ideal.span_singleton_mul_right_unit
      (IsLocalization.map_units (Localization.AtPrime p) t)]
  obtain ⟨s, hs⟩ := hI
  have hden : ∀ x ∈ s, ∃ t : R, t ∉ p ∧ t * x ∈ Ideal.span {a} := by
    intro x hx
    have hxI : x ∈ I := hs ▸ Submodule.subset_span hx
    have hxmap := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) hxI
    rw [haeq] at hxmap
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
      (Localization.AtPrime p) _ x).mp (by
        simpa only [Ideal.map_span, Set.image_singleton] using hxmap)
  have aux : ∃ f : R, f ∉ p ∧
      ∀ (q : Ideal R) [q.IsPrime], f ∉ q →
        ∀ x ∈ s, algebraMap R (Localization.AtPrime q) x ∈
          Ideal.span {algebraMap R (Localization.AtPrime q) a} := by
    clear hs hbmem haeq hb b hat
    induction s using Finset.induction_on with
    | empty => exact ⟨1, (inferInstance : p.IsPrime).one_notMem, by simp⟩
    | @insert x s hx ih =>
      obtain ⟨t, htp, ht⟩ := hden x (Finset.mem_insert_self _ _)
      obtain ⟨f, hfp, hf⟩ := ih (fun y hy ↦ hden y (Finset.mem_insert_of_mem hy))
      refine ⟨t * f, (inferInstance : p.IsPrime).mul_notMem htp hfp, ?_⟩
      intro q _ htq y hy
      have htq' : t ∉ q := fun h ↦ htq (q.mul_mem_right _ h)
      have hfq : f ∉ q := fun h ↦ htq (q.mul_mem_left _ h)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · apply (Ideal.unit_mul_mem_iff_mem _
          (IsLocalization.map_units (Localization.AtPrime q)
            (⟨t, htq'⟩ : q.primeCompl))).mp
        have hm := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime q)) ht
        simpa only [map_mul, Ideal.map_span, Set.image_singleton] using hm
      · exact hf q hfq y hy
  obtain ⟨f, hfp, hf⟩ := aux
  refine ⟨a, ha, f, hfp, ?_⟩
  intro q _ hfq
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  swap
  · rintro _ (rfl : _ = _)
    exact Ideal.mem_map_of_mem _ ha
  rw [← hs, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  exact hf q hfq x hx

/-- Generic smoothness gives a finite intrinsic singular correction on every
integral finite-type scheme over a perfect field. Closedness of the regular locus
is not needed. -/
theorem finite_schemeDivisorPoint_stalkSingularLocus_of_perfectField
    (k : Type u) [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] :
    {Q : SchemeDivisorPoint X | Q.1 ∈ stalkSingularLocus X}.Finite := by
  have : LocallyOfFinitePresentation s := inferInstance
  have hfin : {Q : SchemeDivisorPoint X | Q.1 ∈ (s.smoothLocus : Set X)ᶜ}.Finite := by
    apply finite_schemeDivisorPoint_mem_of_isClosed s.smoothLocus.isOpen.isClosed_compl
    intro heq
    exact (heq.symm ▸ Set.mem_univ (genericPoint X))
      s.genericPoint_mem_smoothLocus_of_perfectField
  exact hfin.subset fun Q hQ ↦
    stalkSingularLocus_subset_compl_smoothLocus (.of k) s hQ

/-- Along an ambient divisor, generic principal generation and generic smoothness
of the divisor give a neighborhood with regular ambient and divisor stalks at every
codimension-one point of the divisor. -/
theorem exists_open_invariantDivisor_regularityCorrection
    (k : Type u) [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (A : SchemeDivisorPoint X) :
    ∃ V : (pointClosureIdealSheaf A.1).subscheme.Opens,
      genericPoint (pointClosureIdealSheaf A.1).subscheme ∈ V ∧
      ∀ Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme,
        Q.1 ∈ V →
          (pointClosureIdealSheaf A.1).subschemeι Q.1 ∉ stalkSingularLocus X ∧
            Q.1 ∉ stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hAU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ A.1) isOpen_univ
  let W : X.affineOpens := ⟨U, hU⟩
  let I := pointClosureIdealSheaf A.1
  let R := Γ(X, W)
  let p : Ideal R := I.ideal W
  let : Nonempty (W : X.Opens) := ⟨⟨A.1, hAU⟩⟩
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian W
  let : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed W
  let : p.IsPrime := pointClosureIdealSheaf_ideal_isPrime A.1 W hAU
  have hp : p.height = 1 := pointClosureIdealSheaf_ideal_height A W hAU
  let : IsDiscreteValuationRing (Localization.AtPrime p) :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne p hp
  let : (p.map (algebraMap R (Localization.AtPrime p))).IsPrincipal :=
    IsPrincipalIdealRing.principal _
  obtain ⟨a, ha, f, hfp, hf⟩ :=
    exists_principalOpen_map_eq_span_of_isPrincipal_atPrime p
      (Ideal.fg_of_isNoetherianRing p) p
  have hAf : A.1 ∈ X.basicOpen f := by
    apply (Stacks.SchemeLevel.mem_basicOpen_iff_notMem_primeIdealOf W.2 f ⟨A.1, hAU⟩).mpr
    simpa only [p, I, pointClosureIdealSheaf_ideal A.1 W hAU] using hfp
  let sA := I.subschemeι ≫ s
  have : LocallyOfFiniteType sA := inferInstance
  have : LocallyOfFinitePresentation sA := inferInstance
  let V : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ X.basicOpen f ⊓ sA.smoothLocus
  refine ⟨V, ⟨?_, sA.genericPoint_mem_smoothLocus_of_perfectField⟩, ?_⟩
  · change I.subschemeι (genericPoint I.subscheme) ∈ X.basicOpen f
    simpa only [I, pointClosureSubscheme_genericPoint] using hAf
  · intro Q hQ
    have hQf : I.subschemeι Q.1 ∈ X.basicOpen f := hQ.1
    have hQU : I.subschemeι Q.1 ∈ (W : X.Opens) := X.basicOpen_le f hQf
    have hdiv : IsRegularLocalRing (I.subscheme.presheaf.stalk Q.1) :=
      isRegularLocalRing_stalk_of_mem_smoothLocus (.of k) sA Q.1 hQ.2
    refine ⟨?_, fun h ↦ h hdiv⟩
    let q : Ideal R := ambientPrimeOfQuotientPoint I W Q.1 hQU
    let : q.IsPrime := ambientPrimeOfQuotientPoint_isPrime I W Q.1 hQU
    have hfq : f ∉ q := by
      rw [show q = (W.2.primeIdealOf ⟨I.subschemeι Q.1, hQU⟩).asIdeal from
        ambientPrimeOfQuotientPoint_eq_primeIdealOf I W Q.1 hQU]
      exact (Stacks.SchemeLevel.mem_basicOpen_iff_notMem_primeIdealOf W.2 f _).mp hQf
    let P : Ideal (Localization.AtPrime q) := p.map (algebraMap R _)
    have hP : P = Ideal.span {algebraMap R (Localization.AtPrime q) a} := hf q hfq
    let : P.IsPrincipal := ⟨algebraMap R (Localization.AtPrime q) a, hP⟩
    let : IsRegularLocalRing (Localization.AtPrime q ⧸ P) :=
      isRegularLocalRing_divisorQuotientLocalization I W Q.1 hQU hdiv
    have hdimQ : ringKrullDim (Localization.AtPrime q ⧸ P) = 1 := by
      simpa only [Q.2, WithBot.coe_one] using
        ringKrullDim_divisorQuotientLocalization I W Q.1 hQU
    have hdimR : 2 ≤ ringKrullDim (Localization.AtPrime q) := by
      rw [show ringKrullDim (Localization.AtPrime q) =
        ↑(Order.coheight (I.subschemeι Q.1)) from
          ringKrullDim_ambientPrimeLocalization I W Q.1 hQU]
      exact WithBot.coe_le_coe.mpr (A.two_le_coheight_closureDivisor Q)
    let : IsRegularLocalRing (Localization.AtPrime q) :=
      isRegularLocalRing_of_principal_quotient_of_dim_one P hdimQ hdimR
    have hreg : IsRegularLocalRing (X.presheaf.stalk (I.subschemeι Q.1)) :=
      IsRegularLocalRing.of_ringEquiv (ambientPrimeLocalizationRingEquivStalk I W Q.1 hQU)
    exact fun h ↦ h hreg

/-- The actual ambient and intrinsic singular correction on a divisor is finite.
The proof uses generic Cartier generation and generic smoothness, and requires no
closedness theorem for either singular locus. -/
theorem invariantDivisorSing_finite_of_perfectField
    (k : Type u) [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X] (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (A : SchemeDivisorPoint X) : (invariantDivisorSing A).Finite := by
  obtain ⟨V, hV, hregular⟩ := exists_open_invariantDivisor_regularityCorrection k s A
  have hfin : {Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme |
      Q.1 ∈ (V : Set _)ᶜ}.Finite := by
    apply finite_schemeDivisorPoint_mem_of_isClosed V.isOpen.isClosed_compl
    intro heq
    exact (heq.symm ▸ Set.mem_univ _) hV
  exact hfin.subset fun Q hQ hQV ↦ hQ.elim (hregular Q hQV).1 (hregular Q hQV).2

#print axioms exists_principalOpen_map_eq_span_of_isPrincipal_atPrime
#print axioms finite_schemeDivisorPoint_stalkSingularLocus_of_perfectField
#print axioms exists_open_invariantDivisor_regularityCorrection
#print axioms invariantDivisorSing_finite_of_perfectField

end

end Pcf
