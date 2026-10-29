/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPPrimaryFibresConstruction
public import Pcf.Bounding.PrimaryFibresScheme

/-!
# `lem:primary-fibres` for schemes, by the paper's argument

`paper-p.tex`, Lemma `lem:primary-fibres` (live source l. 1233–1276). The repo already proves
the lemma by another route (`exists_open_schemeDivisorRamificationIdx_eq_prime_pow`). Here the
same statement is derived from the paper's own proof: on every pair of affine charts
`U ⊆ B`, `V ⊆ q⁻¹U`, the square `A' → R'` of normalizations in `K' = K(T)` and `L' = LK'`
(`PaperPPrimaryFibres.exists_primaryFibres_paperSquare`) gives the display
`e(F'/F) v_F(q^* t) = e(D'/D) v_{F'}(q'^* t') = e(D'/D)` and `v_F(q^* t) ∣ p^a`
(`paperSquare_chart`); the finitely many charts are then intersected.

Scope. The square is constructed on affine charts (`B'`, `E'` over `U`, `V`), not as global
schemes `B'`, `E'`; the display is proved for every divisor `F` meeting a chart `V` over a
divisor `D` meeting the chart open `D(c)`. Since `E` is covered by finitely many charts, every
divisor `F` of `E` meets some chart, and the global conclusion holds on the intersection `U`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.Bounding

noncomputable section

set_option linter.style.haveILetI false

open PaperPPrimaryFibres
open scoped PaperPPrimaryFibres

/-- **The paper's square on one pair of affine charts.** For affine charts `U ⊆ B` and
`V ⊆ q⁻¹U ⊆ E` with `R = Γ(B,U) → S = Γ(E,V)`, the actual square of `lem:primary-fibres`
(`A' = baseNorm R S T`, `R' = sourceNorm S T`) gives `c ≠ 0` and `a` such that for every divisor
`F` of `E` meeting `V` over a divisor `D` of `B` meeting `D(c)`: `v_F(q^* t)` (the scheme
multiplicity) equals the ring multiplicity at the chart primes, the display
`e(F'/F) v_F(q^* t) = e(D'/D) v_{F'}(q'^* t') = e(D'/D)` holds on the square, and
`v_F(q^* t) = p^b`, `b ≤ a`. -/
theorem paperSquare_chart
    (p : ℕ) [hp : Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {D A : Scheme.{u}} [IsIntegral D] [IsIntegral A]
    [IsLocallyNoetherian D] [IsLocallyNoetherian A] [IsNormalScheme D] [IsNormalScheme A]
    (s : A ⟶ Spec (.of k)) [LocallyOfFiniteType s] (q : D ⟶ A) [IsDominant q]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (U : A.affineOpens) (V : D.affineOpens) (hVU : (V : D.Opens) ≤ q ⁻¹ᵁ (U : A.Opens))
    [Nonempty (U : A.Opens)] [Nonempty (V : D.Opens)] :
    letI : Algebra Γ(A, U) Γ(D, V) := (q.appLE U V hVU).hom.toAlgebra
    haveI : FaithfulSMul Γ(A, U) Γ(D, V) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (appLE_injective_of_dominant q U V hVU)
    ∃ T : Finset (PaperOmega Γ(D, V)), ∃ a : ℕ,
      Module.finrank (FractionRing Γ(A, U)) (baseAlt Γ(A, U) Γ(D, V) T) = p ^ a ∧
      ∃ c : Γ(A, U), c ≠ 0 ∧ ∀ (E : SchemeDivisorPoint D) (hE : E.1 ∈ (V : D.Opens)),
        ∀ (Q : SchemeDivisorPoint A), q E.1 = Q.1 → Q.1 ∈ A.basicOpen c →
          let F := (V.2.primeIdealOf ⟨E.1, hE⟩).asIdeal
          schemeDivisorRamificationIdx q E = F.ramificationIdx Γ(A, U) ∧
          ∃ (D' : Ideal (baseNorm Γ(A, U) Γ(D, V) T)) (F' : Ideal (sourceNorm Γ(D, V) T))
            (_ : D'.IsPrime) (_ : F'.IsPrime),
            F'.LiesOver F ∧ F'.LiesOver D' ∧
            F'.ramificationIdx Γ(D, V) * F.ramificationIdx Γ(A, U) =
              D'.ramificationIdx Γ(A, U) * F'.ramificationIdx (baseNorm Γ(A, U) Γ(D, V) T) ∧
            D'.ramificationIdx Γ(A, U) * F'.ramificationIdx (baseNorm Γ(A, U) Γ(D, V) T) =
              D'.ramificationIdx Γ(A, U) ∧
            ∃ b ≤ a, F.ramificationIdx Γ(A, U) = p ^ b := by
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
  letI : Algebra k R := φ.toAlgebra
  letI : Algebra k B := ((algebraMap R B).comp φ).toAlgebra
  haveI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType k R := by
    have h : (s.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance
        ⟨⊤, isAffineOpen_top (Spec (.of k))⟩ U (fun _ _ => trivial)
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fun x => ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]⟩)
    exact RingHom.FiniteType.comp h h2
  obtain ⟨T, -, a, ha, -, c, hc, H⟩ :=
    PaperPPrimaryFibres.exists_primaryFibres_paperSquare p k R B
  refine ⟨T, a, ha, c, hc, ?_⟩
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
  have hH := H 𝔮 h𝔮h hc𝔮 P hPh hPover
  obtain ⟨D', F', hD'p, hF'p, hrest⟩ := hH
  have hbe := hrest.2.2.2.2.2.2.2.2
  refine ⟨?_, D', F', hD'p, hF'p, hrest.2.2.2.1, hrest.2.2.2.2.1, hrest.2.2.2.2.2.2.1,
    hrest.2.2.2.2.2.2.2.1, hbe⟩
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


/-- **`p`-primary fibre multiplicities** (`latex/paper-p.tex`, Lemma
`lem:primary-fibres`). Let `q : D ⟶ A` be a dominant, locally finite type,
quasi-compact morphism of normal integral locally noetherian schemes, with `A`
quasi-compact over a field of characteristic `p`. There are a nonempty (hence
dense) open `U ⊆ A` and `a ≥ 0` such that for every prime divisor `Q` of `A`
with generic point in `U` and every prime divisor `E` of `D` whose generic point
maps to that of `Q`, the multiplicity `μ(E/Q) = v_E(q^* t_Q)` is a power of `p`
dividing `p^a`.

This is the paper's proof: on each pair of affine charts the actual square
`A' = baseNorm`, `R' = sourceNorm` of `paperSquare_chart` gives the display and the bound
(divergences from the paper: see `PaperPPrimaryFibresConstruction`). The statement is that of
`exists_open_schemeDivisorRamificationIdx_eq_prime_pow`, plus `LocallyOfFiniteType s`. -/
theorem exists_open_schemeDivisorRamificationIdx_eq_prime_pow_paperSquare
    (p : ℕ) [hp : Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {D A : Scheme.{u}} [IsIntegral D] [IsIntegral A]
    [IsLocallyNoetherian D] [IsLocallyNoetherian A] [IsNormalScheme D] [IsNormalScheme A]
    [CompactSpace A]
    (s : A ⟶ Spec (.of k)) [LocallyOfFiniteType s] (q : D ⟶ A) [IsDominant q]
    [LocallyOfFiniteType q] [QuasiCompact q] :
    ∃ U : A.Opens, (U : Set A).Nonempty ∧ ∃ a : ℕ,
      ∀ (E : SchemeDivisorPoint D) (Q : SchemeDivisorPoint A), q E.1 = Q.1 → Q.1 ∈ U →
        ∃ b ≤ a, schemeDivisorRamificationIdx q E = p ^ b := by
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
      (hle : (ij.2 : D.Opens) ≤ q ⁻¹ᵁ (ij.1 : A.Opens)) (hne : Nonempty (ij.2 : D.Opens)) :
      ∃ c : Γ(A, ij.1), c ≠ 0 ∧ ∃ a : ℕ, ∀ (E : SchemeDivisorPoint D),
        E.1 ∈ (ij.2 : D.Opens) → ∀ (Q : SchemeDivisorPoint A), q E.1 = Q.1 →
          Q.1 ∈ A.basicOpen c → ∃ b ≤ a, schemeDivisorRamificationIdx q E = p ^ b := by
    obtain ⟨v⟩ := hne
    haveI : Nonempty (ij.1 : A.Opens) := ⟨⟨q v.1, hle v.2⟩⟩
    haveI : Nonempty (ij.2 : D.Opens) := ⟨v⟩
    obtain ⟨T, a, -, c, hc, H⟩ := paperSquare_chart p k s q ij.1 ij.2 hle
    refine ⟨c, hc, a, fun E hE Q hQ hQc => ?_⟩
    obtain ⟨h1, -, -, -, -, -, -, -, -, b, hb, hbe⟩ := H E hE Q hQ hQc
    exact ⟨b, hb, h1.trans hbe⟩
  choose c hc a ha using hchart
  let good (ij : A.affineOpens × D.affineOpens) : Prop :=
    (ij.2 : D.Opens) ≤ q ⁻¹ᵁ (ij.1 : A.Opens) ∧ Nonempty (ij.2 : D.Opens)
  let G (ij : A.affineOpens × D.affineOpens) : A.Opens :=
    if h : good ij then A.basicOpen (c ij h.1 h.2) else ⊤
  let aa (ij : A.affineOpens × D.affineOpens) : ℕ :=
    if h : good ij then a ij h.1 h.2 else 0
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
  refine ⟨U, ⟨_, hgen⟩, I.sup aa, ?_⟩
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
  obtain ⟨b, hb, hbe⟩ := ha ij hle hne E hEV Q hQ hQG
  refine ⟨b, le_trans hb ?_, hbe⟩
  have : aa ij = a ij hle hne := by simp only [aa, dite_eq_left hgood]
  rw [← this]
  exact Finset.le_sup hijI


end

#print axioms paperSquare_chart
#print axioms exists_open_schemeDivisorRamificationIdx_eq_prime_pow_paperSquare

end Pcf.Bounding
