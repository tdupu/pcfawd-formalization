/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryFibresCharZero
public import Pcf.Bounding.PrimaryFibresScheme

/-!
# Fibre multiplicities in characteristic zero for schemes

`latex/paper-p.tex`, Lemma `lem:primary-fibres`, for `p = 0`: for a dominant
morphism `q : D ⟶ A` of normal integral schemes over a field of characteristic
zero, the multiplicity `μ(E/Q) = v_E(q^* t_Q)` of a prime divisor `E` of `D`
over a prime divisor `Q` of `A` is one for `Q` in a dense open set. The
multiplicity is the stalk ramification index `schemeDivisorRamificationIdx q E`.

The proof reduces to `exists_ramificationIdx_eq_one_charZero` on finitely many
affine charts, as `PrimaryFibresScheme` does in characteristic `p`, reusing its
chart lemmas.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.Bounding

noncomputable section

set_option linter.style.haveILetI false

/-- **Fibres in characteristic zero on one pair of affine charts.** -/
theorem exists_basicOpen_schemeDivisorRamificationIdx_chart_charZero
    (k : Type u) [Field k] [CharZero k]
    {D A : Scheme.{u}} [IsIntegral D] [IsIntegral A]
    [IsLocallyNoetherian D] [IsLocallyNoetherian A] [IsNormalScheme D] [IsNormalScheme A]
    (s : A ⟶ Spec (.of k)) (q : D ⟶ A) [IsDominant q] [LocallyOfFiniteType q]
    [QuasiCompact q]
    (U : A.affineOpens) (V : D.affineOpens) (hVU : (V : D.Opens) ≤ q ⁻¹ᵁ (U : A.Opens))
    [Nonempty (V : D.Opens)] :
    ∃ c : Γ(A, U), c ≠ 0 ∧ ∀ (E : SchemeDivisorPoint D), E.1 ∈ (V : D.Opens) →
      ∀ (Q : SchemeDivisorPoint A), q E.1 = Q.1 → Q.1 ∈ A.basicOpen c →
        schemeDivisorRamificationIdx q E = 1 := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (V : D.Opens))
  have : Nonempty (U : A.Opens) := ⟨⟨q v.1, hVU v.2⟩⟩
  let R := Γ(A, U)
  let B := Γ(D, V)
  letI : Algebra R B := (q.appLE U V hVU).hom.toAlgebra
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian V
  have : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  have : IsIntegrallyClosed B := IsNormalScheme.component_integrallyClosed V
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr
    (appLE_injective_of_dominant q U V hVU)
  have : Algebra.FiniteType R B :=
    HasRingHomProperty.appLE @LocallyOfFiniteType q (inferInstance : LocallyOfFiniteType q)
      U V hVU
  let φ : k →+* R := (s.appLE ⊤ U (fun _ _ => trivial)).hom.comp
    (Scheme.ΓSpecIso (.of k)).inv.hom
  have : CharZero R := charZero_of_injective_ringHom φ.injective
  obtain ⟨c, hc, H⟩ := exists_ramificationIdx_eq_one_charZero R B
  refine ⟨c, hc, ?_⟩
  intro E hE Q hQ hQc
  let Q' : SchemeDivisorPoint A := ⟨q E.1, by rw [hQ]; exact Q.2⟩
  have hqE : q E.1 ∈ (U : A.Opens) := hVU hE
  let P := (V.2.primeIdealOf ⟨E.1, hE⟩).asIdeal
  let 𝔮 := (U.2.primeIdealOf ⟨q E.1, hqE⟩).asIdeal
  have hcomap : P.comap (algebraMap R B) = 𝔮 :=
    congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (f := q) (x := E.1) U U.2 V V.2 hVU hE)
  have hPover : P.LiesOver 𝔮 := ⟨hcomap.symm⟩
  have hPh : P.height = 1 := by
    have h := pointClosureIdealSheaf_ideal_height E V hE
    rwa [pointClosureIdealSheaf_ideal E.1 V hE] at h
  have h𝔮h : 𝔮.height = 1 := by
    have h := pointClosureIdealSheaf_ideal_height Q' U hqE
    rwa [pointClosureIdealSheaf_ideal Q'.1 U hqE] at h
  have hc𝔮 : c ∉ 𝔮 := (not_mem_primeIdealOf_iff_mem_basicOpen U (q E.1) hqE c).mpr
    (by rw [hQ]; exact hQc)
  rw [← H 𝔮 h𝔮h hc𝔮 P hPh hPover]
  -- Transport to the stalks.
  let Rp := A.presheaf.stalk (q E.1)
  let Sq := D.presheaf.stalk E.1
  letI : Algebra R Rp := A.presheaf.algebra_section_stalk ⟨q E.1, hqE⟩
  letI : Algebra B Sq := D.presheaf.algebra_section_stalk ⟨E.1, hE⟩
  letI : Algebra Rp Sq := (q.stalkMap E.1).hom.toAlgebra
  letI : Algebra R Sq :=
    ((D.presheaf.germ V E.1 hE).hom.comp (q.appLE U V hVU).hom).toAlgebra
  have : IsScalarTower R B Sq := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R Rp Sq := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact germ_appLE_apply q U V hVU E.1 hE a)
  have : IsLocalization.AtPrime Rp 𝔮 := U.2.isLocalization_stalk ⟨q E.1, hqE⟩
  have : IsLocalization.AtPrime Sq P := V.2.isLocalization_stalk ⟨E.1, hE⟩
  have : IsLocalHom (algebraMap Rp Sq) :=
    show IsLocalHom (q.stalkMap E.1).hom from inferInstance
  have : IsDiscreteValuationRing Rp := Q'.stalk_isDiscreteValuationRing
  have : FaithfulSMul Rp Sq := (faithfulSMul_iff_algebraMap_injective Rp Sq).mpr
    (stalkMap_injective_of_dominant_integral q E.1)
  have : Module.Flat Rp Sq := inferInstance
  exact Pcf.ramificationIdx_eq_of_localization_square 𝔮 P

#print axioms exists_basicOpen_schemeDivisorRamificationIdx_chart_charZero

/-- **Fibre multiplicities in characteristic zero** (`latex/paper-p.tex`,
Lemma `lem:primary-fibres`, the case `p = 0`). Let `q : D ⟶ A` be a dominant,
locally finite type, quasi-compact morphism of normal integral locally
noetherian schemes, with `A` quasi-compact over a field of characteristic zero.
There is a nonempty (hence dense) open `U ⊆ A` such that for every prime divisor
`Q` of `A` with generic point in `U` and every prime divisor `E` of `D` whose
generic point maps to that of `Q`, the multiplicity `μ(E/Q) = v_E(q^* t_Q)` is
one.

The proof route differs from the paper's appeal to Stacks Tags `04KT` and
`0578`; see `exists_ramificationIdx_eq_one_charZero`. -/
theorem exists_open_schemeDivisorRamificationIdx_eq_one_charZero
    (k : Type u) [Field k] [CharZero k]
    {D A : Scheme.{u}} [IsIntegral D] [IsIntegral A]
    [IsLocallyNoetherian D] [IsLocallyNoetherian A] [IsNormalScheme D] [IsNormalScheme A]
    [CompactSpace A]
    (s : A ⟶ Spec (.of k)) (q : D ⟶ A) [IsDominant q] [LocallyOfFiniteType q]
    [QuasiCompact q] :
    ∃ U : A.Opens, (U : Set A).Nonempty ∧
      ∀ (E : SchemeDivisorPoint D) (Q : SchemeDivisorPoint A), q E.1 = Q.1 → Q.1 ∈ U →
        schemeDivisorRamificationIdx q E = 1 := by
  classical
  -- Finite affine covers of `A` and of each preimage.
  obtain ⟨SA, hSAfin, hSA⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
    (show IsCompact (X := A) ((⊤ : A.Opens) : Set A) from CompactSpace.isCompact_univ)
  choose SV hSVfin hSV using fun Ui : A.affineOpens =>
    isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
      (show IsCompact (X := D) ((q ⁻¹ᵁ (Ui : A.Opens) : D.Opens) : Set D) from
        QuasiCompact.isCompact_preimage _ (Ui : A.Opens).isOpen Ui.2.isCompact)
  -- Chart data.
  have hchart (ij : A.affineOpens × D.affineOpens)
      (hle : (ij.2 : D.Opens) ≤ q ⁻¹ᵁ (ij.1 : A.Opens)) (hne : Nonempty (ij.2 : D.Opens)) :=
    exists_basicOpen_schemeDivisorRamificationIdx_chart_charZero k s q ij.1 ij.2 hle
  choose c hc ha using hchart
  let good (ij : A.affineOpens × D.affineOpens) : Prop :=
    (ij.2 : D.Opens) ≤ q ⁻¹ᵁ (ij.1 : A.Opens) ∧ Nonempty (ij.2 : D.Opens)
  let G (ij : A.affineOpens × D.affineOpens) : A.Opens :=
    if h : good ij then A.basicOpen (c ij h.1 h.2) else ⊤
  let SVall : Set D.affineOpens := ⋃ Ui ∈ SA, SV Ui
  have hSVallfin : SVall.Finite := hSAfin.biUnion fun Ui _ => hSVfin Ui
  let I : Finset (A.affineOpens × D.affineOpens) := hSAfin.toFinset ×ˢ hSVallfin.toFinset
  let U : A.Opens := I.inf G
  have hmemU (x : A) : x ∈ U ↔ ∀ ij ∈ I, x ∈ G ij := by
    change x ∈ I.inf G ↔ _
    induction I using Finset.induction_on with
    | empty => simp
    | insert ij I hij ih =>
      rw [Finset.inf_insert, Opens.mem_inf, ih]
      simp [Finset.mem_insert]
  have hgen : genericPoint A ∈ U := by
    rw [hmemU]
    intro ij _
    simp only [G]
    split_ifs with h
    · have hne : A.basicOpen (c ij h.1 h.2) ≠ ⊥ := by
        rw [Ne, AlgebraicGeometry.basicOpen_eq_bot_iff]
        exact hc ij h.1 h.2
      obtain ⟨y, hy⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
      exact ((genericPoint_spec A).mem_open_set_iff (A.basicOpen _).isOpen).mpr
        ⟨y, trivial, hy⟩
    · trivial
  refine ⟨U, ⟨_, hgen⟩, ?_⟩
  intro E Q hQ hQU
  -- Locate charts containing `E` and `q E`.
  have hqE : q E.1 ∈ (⊤ : A.Opens) := trivial
  rw [hSA] at hqE
  simp only [Opens.mem_iSup] at hqE
  obtain ⟨Ui, hUi, hqUi⟩ := hqE
  have hEV : E.1 ∈ q ⁻¹ᵁ (Ui : A.Opens) := hqUi
  rw [hSV Ui] at hEV
  simp only [Opens.mem_iSup] at hEV
  obtain ⟨V, hV, hEV⟩ := hEV
  let ij : A.affineOpens × D.affineOpens := (Ui, V)
  have hle : (V : D.Opens) ≤ q ⁻¹ᵁ (Ui : A.Opens) := by
    rw [hSV Ui]
    exact le_iSup₂ (f := fun i (_ : i ∈ SV Ui) => (i : D.Opens)) V hV
  have hne : Nonempty (V : D.Opens) := ⟨⟨E.1, hEV⟩⟩
  have hgood : good ij := ⟨hle, hne⟩
  have hijI : ij ∈ I := by
    simp only [I, Finset.mem_product, Set.Finite.mem_toFinset]
    exact ⟨hUi, Set.mem_biUnion hUi hV⟩
  have hQG : Q.1 ∈ G ij := (hmemU Q.1).mp hQU ij hijI
  simp only [G, dite_eq_left hgood] at hQG
  exact ha ij hle hne E hEV Q hQ hQG

#print axioms exists_open_schemeDivisorRamificationIdx_eq_one_charZero

end

end Pcf.Bounding
