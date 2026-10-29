/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedLocalStructure
public import Pcf.Examples.PaperP.PinchedNodeFibre

/-!
# The invariant divisor `B = ν(V(w - 1))` of the pinched plane and `g = f|_B`

For `paper-p.tex`, Example `ex:pinched` ("Let `B = ν(V(w - 1))` and `g = f|_B`";
"Restricting functions to `w = 1` identifies the ring of `B` with
`R_B = {p ∈ k[z] : p(2) = p(-2)}`, since every such `p` is the restriction of
`p(z) ∈ R`"; "The line `V(w - 1)` is invariant under `f̃`, so `f(B) = B`"):

* `lineRestr : R →+* R_B`, `h ↦ h(z, 1)`; `lineRestr_surjective` (every `p ∈ R_B` is the
  restriction of `p(z) ∈ R`); `lineRestr_comp_fStar : ρ ∘ f* = g* ∘ ρ`.
* `planeLineIdeal_eq_span`: the ideal of `V(w - 1) ⊆ 𝔸²` is `(w - 1)`; `linePoint`
  is its generic point and `bPoint = ν(linePoint)` is the generic point of `B`, with
  `bPoint_asIdeal : 𝔭_B = ker ρ`.
* `fScheme_bPoint : f(η_B) = η_B` (`B` is `f`-invariant); `bPoint_height : ht 𝔭_B = 1`,
  so `B` is an integral effective divisor (`bDivisor`).
* `quotientLineEquiv : R ⧸ 𝔭_B ≃+* R_B`, intertwining `f*` mod `𝔭_B` with `g*`
  (`quotientLineEquiv_fStar`).
* `oIdeal_height : 2 ≤ ht 𝔪_o` (chain `0 < 𝔭_B < 𝔪_o`), hence
  `regularInCodimOne`: every prime of height `≤ 1` has a regular local ring.

Divergence from the manuscript: here `B` is identified with `Spec R_B` through the
ring isomorphism `R ⧸ 𝔭_B ≃ R_B`; the identification with the reduced closed subscheme
`(pointClosureIdealSheaf η_B).subscheme` is in `PinchedLineScheme`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedLine

open AlgebraicGeometry CategoryTheory MvPolynomial Pcf.Examples.Pinched
  Pcf.Examples.PaperP.PinchedNormalization Pcf.Examples.PaperP.PinchedLocalStructure

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k
local notation "S" => PlaneRing k
local notation "RB" => PinchedNodeFibre.NodeRing k

/-- Restriction to the line `w = 1` of the plane: `h(z, w) ↦ h(z, 1)`. -/
noncomputable def planeRestr : S →ₐ[k] Polynomial k := aeval ![Polynomial.X, 1]

omit [CharZero k] in
theorem eval_planeRestr (a : k) (p : S) :
    (planeRestr k p).eval a = aeval ![a, 1] p := by
  have h : (Polynomial.aeval a).comp (planeRestr k) = aeval ![a, 1] := by
    unfold planeRestr
    rw [MvPolynomial.comp_aeval]
    congr 1
    funext i
    fin_cases i <;> simp
  have := congrArg (fun φ => φ p) h
  simpa using this

omit [CharZero k] in
/-- The embedding `k[z] → k[z, w]`, `z ↦ z`. -/
theorem planeRestr_aeval_X0 (p : Polynomial k) : planeRestr k (Polynomial.aeval (X 0 : S) p) = p := by
  have h : (planeRestr k).comp (Polynomial.aeval (X 0 : S)) = AlgHom.id k _ := by
    apply Polynomial.algHom_ext
    simp [planeRestr]
  exact congrArg (fun φ => φ p) h

omit [CharZero k] in
theorem aeval_X0_mem (p : Polynomial k) (hp : p ∈ nodeAlg k) :
    Polynomial.aeval (X 0 : S) p ∈ pinchedAlg k := by
  rw [mem_pinchedAlg_iff]
  have h1 : evalTwoOne k (Polynomial.aeval (X 0 : S) p) = Polynomial.aeval (2 : k) p := by
    rw [← Polynomial.aeval_algHom_apply]; simp [evalTwoOne]
  have h2 : evalNegTwoOne k (Polynomial.aeval (X 0 : S) p) = Polynomial.aeval (-2 : k) p := by
    rw [← Polynomial.aeval_algHom_apply]; simp [evalNegTwoOne]
  change evalTwoOne k _ = evalNegTwoOne k _
  rw [h1, h2]
  exact hp

/-- The restriction `ρ : R → R_B`, `h ↦ h(z, 1)`. -/
noncomputable def lineRestr : R →+* RB where
  toFun h := PinchedNodeFibre.mk k (planeRestr k (PinchedRing.val k h)) (by
    rw [mem_nodeAlg_iff, Polynomial.coe_aeval_eq_eval, Polynomial.coe_aeval_eq_eval,
      eval_planeRestr, eval_planeRestr]
    exact (mem_pinchedAlg_iff k).mp (PinchedRing.val_mem k h))
  map_one' := by apply PinchedNodeFibre.val_injective; simp
  map_mul' a b := by
    apply PinchedNodeFibre.val_injective
    exact map_mul (planeRestr k) _ _
  map_zero' := by apply PinchedNodeFibre.val_injective; simp
  map_add' a b := by
    apply PinchedNodeFibre.val_injective
    exact map_add (planeRestr k) _ _

omit [CharZero k] in
theorem val_lineRestr (h : R) :
    PinchedNodeFibre.val k (lineRestr k h) = planeRestr k (PinchedRing.val k h) := rfl

/-- Every `p ∈ R_B` is the restriction of `p(z) ∈ R`. -/
theorem lineRestr_surjective : Function.Surjective (lineRestr k) := by
  intro p
  refine ⟨PinchedRing.mk k _ (aeval_X0_mem k _ (PinchedNodeFibre.val_mem k p)), ?_⟩
  apply PinchedNodeFibre.val_injective
  exact planeRestr_aeval_X0 k _

omit [CharZero k] in
/-- `ρ ∘ f* = g* ∘ ρ`: restricting `h(z², w²)` to `w = 1` gives `h(z², 1)`. -/
theorem lineRestr_comp_fStar :
    (lineRestr k).comp (PinchedAmbient.fStar k) = (PinchedNodeFibre.gStar k).comp (lineRestr k) := by
  ext h
  apply PinchedNodeFibre.val_injective
  simp only [RingHom.comp_apply]
  rw [PinchedNodeFibre.val_gStar, val_lineRestr, val_lineRestr, PinchedAmbient.val_fStar]
  have hcomp : (planeRestr k).comp (squaringMap k) =
      (Polynomial.aeval (Polynomial.X ^ 2 : Polynomial k)).comp (planeRestr k) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [planeRestr, squaringMap]
  rw [Polynomial.comp_eq_aeval]
  exact congrArg (fun φ => φ (PinchedRing.val k h)) hcomp

/-! ### The ideal of the line `w = 1` -/

/-- The ideal of `V(w - 1)` in `k[z, w]`, as the kernel of restriction. -/
noncomputable def planeLineIdeal : Ideal S := RingHom.ker (planeRestr k)

omit [CharZero k] in
/-- The substitution `σ : h(z, w) ↦ h(z, 1)` on `k[z, w]`. -/
theorem sub_subst_mem (p : S) : p - aeval ![X 0, 1] p ∈ Ideal.span {(X 1 - 1 : S)} := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    have : p * X i - aeval ![X 0, 1] p * ![X 0, (1 : S)] i =
        (p - aeval ![X 0, 1] p) * X i + aeval ![X 0, 1] p * (X i - ![X 0, (1 : S)] i) := by
      ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    fin_cases i
    · simp
    · exact Ideal.subset_span rfl

omit [CharZero k] in
theorem subst_eq (p : S) : aeval ![X 0, 1] p = Polynomial.aeval (X 0 : S) (planeRestr k p) := by
  have h : (aeval ![X 0, (1 : S)]) = (Polynomial.aeval (X 0 : S)).comp (planeRestr k) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [planeRestr]
  exact congrArg (fun φ => φ p) h

omit [CharZero k] in
/-- **The ideal of the line `w = 1` is `(w - 1)`**. -/
theorem planeLineIdeal_eq_span : planeLineIdeal k = Ideal.span {(X 1 - 1 : S)} := by
  apply le_antisymm
  · intro p hp
    have h := sub_subst_mem k p
    rw [subst_eq, (RingHom.mem_ker).mp hp, map_zero, sub_zero] at h
    exact h
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change planeRestr k (X 1 - 1) = 0
    simp [planeRestr]

omit [CharZero k] in
instance planeLineIdeal_isPrime : (planeLineIdeal k).IsPrime := RingHom.ker_isPrime _

/-- The generic point of the line `V(w - 1) ⊆ 𝔸²`. -/
noncomputable def linePoint : Spec (.of S) := ⟨planeLineIdeal k, inferInstance⟩

/-- The generic point of `B = ν(V(w - 1))`. -/
noncomputable def bPoint : Spec (.of R) := PinchedAmbient.nu k (linePoint k)

omit [CharZero k] in
theorem bPoint_asIdeal : (bPoint k).asIdeal = RingHom.ker (lineRestr k) := by
  ext h
  change planeRestr k (PinchedRing.val k h) = 0 ↔ lineRestr k h = 0
  constructor
  · intro h0; apply PinchedNodeFibre.val_injective; exact h0
  · intro h0; exact congrArg (PinchedNodeFibre.val k) h0

/-- **`f(B) = B`**: the generic point of `B` is fixed by `f`. -/
theorem fScheme_bPoint : PinchedAmbient.fScheme k (bPoint k) = bPoint k := by
  apply PrimeSpectrum.ext
  change Ideal.comap (PinchedAmbient.fStar k) (bPoint k).asIdeal = (bPoint k).asIdeal
  rw [bPoint_asIdeal]
  ext h
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
  rw [← RingHom.comp_apply, lineRestr_comp_fStar, RingHom.comp_apply]
  exact ⟨fun h0 => PinchedNodeFibre.gStar_injective k (by rw [h0, map_zero]),
    fun h0 => by rw [h0, map_zero]⟩

/-- **The ring of `B` is `R_B`**: `R ⧸ 𝔭_B ≃+* R_B`. -/
noncomputable def quotientLineEquiv : (R ⧸ (bPoint k).asIdeal) ≃+* RB :=
  (Ideal.quotEquivOfEq (bPoint_asIdeal k)).trans
    (RingHom.quotientKerEquivOfSurjective (lineRestr_surjective k))

theorem quotientLineEquiv_mk (h : R) :
    quotientLineEquiv k (Ideal.Quotient.mk _ h) = lineRestr k h := rfl

/-- The map induced by `f*` on `R ⧸ 𝔭_B` (well defined since `f(η_B) = η_B`). -/
noncomputable def fStarLine : (R ⧸ (bPoint k).asIdeal) →+* (R ⧸ (bPoint k).asIdeal) :=
  Ideal.quotientMap (bPoint k).asIdeal (PinchedAmbient.fStar k) (by
    intro h hh
    change h ∈ ((PinchedAmbient.fScheme k) (bPoint k)).asIdeal
    rw [fScheme_bPoint]
    exact hh)

/-- **`g = f|_B`** on rings: under `R ⧸ 𝔭_B ≃ R_B`, `f*` becomes `g* : p ↦ p(z²)`. -/
theorem quotientLineEquiv_fStar (x : R ⧸ (bPoint k).asIdeal) :
    quotientLineEquiv k (fStarLine k x) = PinchedNodeFibre.gStar k (quotientLineEquiv k x) := by
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
  change lineRestr k (PinchedAmbient.fStar k h) = PinchedNodeFibre.gStar k (lineRestr k h)
  rw [← RingHom.comp_apply, lineRestr_comp_fStar, RingHom.comp_apply]

#print axioms planeLineIdeal_eq_span
#print axioms bPoint_asIdeal
#print axioms fScheme_bPoint
#print axioms quotientLineEquiv
#print axioms quotientLineEquiv_fStar

/-! ### Heights: `B` is a divisor, `ht 𝔪_o ≥ 2`, and `X` is regular in codimension one -/

omit [CharZero k] in
theorem planeLineIdeal_ne_bot : planeLineIdeal k ≠ ⊥ := by
  rw [planeLineIdeal_eq_span, Ne, Ideal.span_singleton_eq_bot]
  intro h0
  have h2 := congrArg (aeval ![(0 : k), 0]) h0
  simp at h2

omit [CharZero k] in
theorem planeLineIdeal_height : (planeLineIdeal k).height = 1 := by
  apply le_antisymm
  · have hmin : planeLineIdeal k ∈ (Ideal.span {(X 1 - 1 : S)}).minimalPrimes := by
      rw [← planeLineIdeal_eq_span, Ideal.minimalPrimes_eq_subsingleton_self]
      rfl
    haveI : (Ideal.span {(X 1 - 1 : S)}).IsPrincipal := ⟨⟨_, rfl⟩⟩
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  · rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact planeLineIdeal_ne_bot k

/-- **`B` has codimension one**: `ht 𝔭_B = 1`. -/
theorem bPoint_height : (bPoint k).asIdeal.height = 1 := by
  change ((planeLineIdeal k).under R).height = 1
  rw [Pcf.height_under_eq_of_finite_of_finiteType k]
  exact planeLineIdeal_height k

/-- `B` as an integral effective divisor (codimension-one point) of `X`. -/
noncomputable def bDivisor : Pcf.SchemeDivisorPoint (Spec (.of R)) :=
  ⟨bPoint k, by
    rw [← idealHeight_eq_coheight (.of R) (bPoint k)]
    exact bPoint_height k⟩

theorem bPoint_lt_oIdeal : (bPoint k).asIdeal < oIdeal k := by
  rw [bPoint_asIdeal]
  refine lt_of_le_of_ne ?_ ?_
  · intro h hh
    rw [RingHom.mem_ker] at hh
    rw [mem_oIdeal_iff]
    have := congrArg (fun p => Polynomial.eval 2 (PinchedNodeFibre.val k p)) hh
    simp only [val_lineRestr, eval_planeRestr] at this
    simpa [evalTwoOne, MvPolynomial.coe_aeval_eq_eval] using this
  · intro heq
    have hz : zSqSubFour k ∈ RingHom.ker (lineRestr k) := heq ▸ zSqSubFour_mem_oIdeal k
    rw [RingHom.mem_ker] at hz
    have := congrArg (fun p => Polynomial.eval 0 (PinchedNodeFibre.val k p)) hz
    simp only [val_lineRestr, eval_planeRestr] at this
    change aeval ![(0 : k), 1] (X 0 ^ 2 - 4 : S) = _ at this
    simp at this

/-- **`ht 𝔪_o ≥ 2`**, from the chain `0 < 𝔭_B < 𝔪_o`. -/
theorem oIdeal_height : 2 ≤ (oIdeal k).height := by
  have := Ideal.height_add_one_le_of_lt_of_isPrime (bPoint_lt_oIdeal k)
  rw [bPoint_height] at this
  exact le_trans (by norm_num) this

/-- **`X` is regular in codimension one**: every prime of height `≤ 1` has a regular
local ring (indeed `X` is regular away from `o`).

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem regularInCodimOne (P : Ideal R) [P.IsPrime] (hP : P.height ≤ 1) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  apply isRegularLocalRing_of_ne_oIdeal k P
  rintro rfl
  have := (oIdeal_height k).trans hP
  norm_num at this

/-- **The singular locus of `X` is `{o}`**. -/
theorem isRegularLocalRing_iff_ne_o (P : Ideal R) [P.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime P) ↔ P ≠ oIdeal k := by
  refine ⟨?_, isRegularLocalRing_of_ne_oIdeal k P⟩
  rintro h rfl
  exact not_isRegularLocalRing_at_o k h

#print axioms bPoint_height
#print axioms oIdeal_height
#print axioms regularInCodimOne
#print axioms isRegularLocalRing_iff_ne_o

end Pcf.Examples.PaperP.PinchedLine
