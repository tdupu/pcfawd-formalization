/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingPostcriticalSupport

/-!
# The postcritical set as a reduced closed subscheme

`paper.tex`, the paragraph after `def:pcf` (ledger row `u:pc-support`): when `f` is PCF,
the union of the postcritical integral effective divisors is a reduced divisor, also
denoted `PC(f)`.

Under the PCF hypothesis the union of the postcritical divisors is closed
(`isClosed_normalized_postcriticalSupport`). Here it is given its reduced induced
scheme structure through `Scheme.IdealSheafData.vanishingIdeal`. The resulting closed
subscheme is reduced and its support is the union. Its ideal sheaf is the intersection
of the point-closure ideal sheaves of the postcritical divisors, and its irreducible
components are exactly the postcritical divisors.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

namespace Pcf.PaperCharZero

/-- Pull back an irreducible set along an inducing map whose range contains it. -/
theorem isIrreducible_preimage_of_isInducing {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {f : Y → Z} (hf : IsInducing f) {T : Set Z} (hT : IsIrreducible T)
    (hTr : T ⊆ Set.range f) : IsIrreducible (f ⁻¹' T) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht⟩ := hT.nonempty
    obtain ⟨y, rfl⟩ := hTr ht
    exact ⟨y, ht⟩
  · intro u v hu hv ⟨a, haT, hau⟩ ⟨b, hbT, hbv⟩
    obtain ⟨u', hu', rfl⟩ := hf.isOpen_iff.mp hu
    obtain ⟨v', hv', rfl⟩ := hf.isOpen_iff.mp hv
    obtain ⟨t, htT, htu, htv⟩ := hT.2 u' v' hu' hv' ⟨f a, haT, hau⟩ ⟨f b, hbT, hbv⟩
    obtain ⟨y, rfl⟩ := hTr htT
    exact ⟨y, htT, htu, htv⟩

section CharacteristicZero

variable (k : Type u) [Field k] [CharZero k]
  {A : Scheme.{u}} (g : A ⟶ A)
  [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
  [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A]
  [CharZero (A.presheaf.stalk (genericPoint A))]
  [∀ U : A.affineOpens, Algebra k Γ(A, U)]
  [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]

/-- Under PCF, the union of the postcritical divisors as a closed subset. -/
def postcriticalCloseds (hpcf : Pcf.IsNormalizedPCF k g) : Closeds A :=
  ⟨divisorSupport (Pcf.schemeNormalizedPostcriticalSet k g),
    isClosed_normalized_postcriticalSupport k g hpcf⟩

/-- The reduced ideal sheaf of `PC(f)` under PCF. -/
noncomputable def postcriticalIdealSheaf (hpcf : Pcf.IsNormalizedPCF k g) :
    A.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (postcriticalCloseds k g hpcf)

/-- `PC(f)` as a closed subscheme with its reduced induced structure.

Manuscript: `def:pcf` (Definition 3.1). -/
noncomputable abbrev postcriticalSubscheme (hpcf : Pcf.IsNormalizedPCF k g) : Scheme.{u} :=
  (postcriticalIdealSheaf k g hpcf).subscheme

/-- The postcritical subscheme is reduced. -/
instance postcriticalSubscheme_isReduced (hpcf : Pcf.IsNormalizedPCF k g) :
    IsReduced (postcriticalSubscheme k g hpcf) :=
  Palomar.isReduced_vanishingIdeal_subscheme _

/-- Its underlying closed set is the union of the postcritical divisors. -/
theorem range_postcriticalSubschemeι (hpcf : Pcf.IsNormalizedPCF k g) :
    Set.range (postcriticalIdealSheaf k g hpcf).subschemeι =
      divisorSupport (Pcf.schemeNormalizedPostcriticalSet k g) := by
  rw [Scheme.IdealSheafData.range_subschemeι, postcriticalIdealSheaf,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- As an ideal sheaf, `PC(f)` is the intersection of the reduced ideal sheaves of its
finitely many postcritical divisors. -/
theorem postcriticalIdealSheaf_eq_iInf (hpcf : Pcf.IsNormalizedPCF k g) :
    postcriticalIdealSheaf k g hpcf =
      ⨅ Q : Pcf.schemeNormalizedPostcriticalSet k g, pointClosureIdealSheaf Q.1.1 := by
  have hcl : postcriticalCloseds k g hpcf =
      ⨆ Q : Pcf.schemeNormalizedPostcriticalSet k g,
        (⟨closure ({Q.1.1} : Set A), isClosed_closure⟩ : Closeds A) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.mp hx
      exact (le_iSup (fun Q : Pcf.schemeNormalizedPostcriticalSet k g =>
        (⟨closure ({Q.1.1} : Set A), isClosed_closure⟩ : Closeds A)) ⟨Q, hQ⟩) hxQ
    · refine iSup_le fun Q x hx => ?_
      exact Set.mem_biUnion Q.2 hx
  rw [postcriticalIdealSheaf, hcl, Scheme.IdealSheafData.vanishingIdeal_iSup]
  rfl

/-- **Components of `PC(f)`.** The irreducible components of the reduced postcritical
subscheme are exactly the (preimages of the) postcritical integral effective divisors. -/
theorem irreducibleComponents_postcriticalSubscheme (hpcf : Pcf.IsNormalizedPCF k g) :
    irreducibleComponents (postcriticalSubscheme k g hpcf) =
      (fun Q : SchemeDivisorPoint A =>
        (postcriticalIdealSheaf k g hpcf).subschemeι ⁻¹' closure ({Q.1} : Set A)) ''
        Pcf.schemeNormalizedPostcriticalSet k g := by
  classical
  set PC := Pcf.schemeNormalizedPostcriticalSet k g
  let ι := (postcriticalIdealSheaf k g hpcf).subschemeι
  have hind : IsInducing ι := ι.isClosedEmbedding.isInducing
  have hrange : Set.range ι = divisorSupport PC := range_postcriticalSubschemeι k g hpcf
  have hCsub : ∀ Q ∈ PC, closure ({Q.1} : Set A) ⊆ Set.range ι := by
    intro Q hQ x hx
    rw [hrange]
    exact Set.mem_biUnion hQ hx
  have hCirr : ∀ Q : SchemeDivisorPoint A, IsIrreducible (closure ({Q.1} : Set A)) :=
    fun Q => isIrreducible_singleton.closure
  -- an irreducible subset of the support lies in one divisor closure
  have hone : ∀ T : Set A, IsIrreducible T → T ⊆ divisorSupport PC →
      ∃ Q ∈ PC, T ⊆ closure ({Q.1} : Set A) := by
    intro T hT hTS
    have hfin : PC.Finite := hpcf
    obtain ⟨z, hz, hTz⟩ := (isIrreducible_iff_sUnion_isClosed.mp hT)
      (hfin.toFinset.image fun Q => closure ({Q.1} : Set A))
      (by
        intro z hz
        simp only [Finset.mem_image] at hz
        obtain ⟨Q, -, rfl⟩ := hz
        exact isClosed_closure)
      (by
        intro x hx
        obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.mp (hTS hx)
        exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hQ)),
          hxQ⟩)
    simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hz
    obtain ⟨Q, hQ, rfl⟩ := hz
    exact ⟨Q, hQ, hTz⟩
  have himage_sub : ∀ W : Set (postcriticalSubscheme k g hpcf),
      ι '' W ⊆ divisorSupport PC := by
    rintro W _ ⟨w, -, rfl⟩
    rw [← hrange]
    exact ⟨w, rfl⟩
  ext Z
  constructor
  · intro hZ
    obtain ⟨Q, hQ, hsub⟩ := hone (ι '' Z) (hZ.prop.image ι ι.continuous.continuousOn)
      (himage_sub Z)
    refine ⟨Q, hQ, ?_⟩
    have hpre : IsIrreducible (ι ⁻¹' closure ({Q.1} : Set A)) :=
      isIrreducible_preimage_of_isInducing hind (hCirr Q) (hCsub Q hQ)
    have hZle : Z ⊆ ι ⁻¹' closure ({Q.1} : Set A) := fun z hz => hsub ⟨z, hz, rfl⟩
    exact (hZ.eq_of_le hpre hZle).symm
  · rintro ⟨Q, hQ, rfl⟩
    refine ⟨isIrreducible_preimage_of_isInducing hind (hCirr Q) (hCsub Q hQ), ?_⟩
    intro W hW hZW
    obtain ⟨Q', hQ', hsub'⟩ := hone (ι '' W) (hW.image ι ι.continuous.continuousOn)
      (himage_sub W)
    have hQQ' : Q = Q' := by
      have hQmem : Q.1 ∈ closure ({Q'.1} : Set A) := by
        obtain ⟨y, hy⟩ := hCsub Q hQ
          (subset_closure (Set.mem_singleton Q.1) : Q.1 ∈ closure ({Q.1} : Set A))
        have hyZ : y ∈ ι ⁻¹' closure ({Q.1} : Set A) := by
          change ι y ∈ closure ({Q.1} : Set A)
          rw [hy]
          exact subset_closure (Set.mem_singleton Q.1)
        rw [← hy]
        exact hsub' ⟨y, hZW hyZ, rfl⟩
      exact (divisor_mem_closure_iff Q Q').mp hQmem
    subst hQQ'
    intro w hw
    exact hsub' ⟨w, hw, rfl⟩

end CharacteristicZero

end Pcf.PaperCharZero

#print axioms Pcf.PaperCharZero.postcriticalSubscheme_isReduced
#print axioms Pcf.PaperCharZero.range_postcriticalSubschemeι
#print axioms Pcf.PaperCharZero.postcriticalIdealSheaf_eq_iInf
#print axioms Pcf.PaperCharZero.irreducibleComponents_postcriticalSubscheme
