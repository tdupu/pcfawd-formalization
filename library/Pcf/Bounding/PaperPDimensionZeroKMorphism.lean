/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPDimensionZero

/-!
# The unconditional dimension-zero clause for `k`-morphisms

`paper-p.tex`, Definition `def:pcfawd`, declares every finite surjective
self-map of a zero-dimensional variety PCF all the way down, with no
separate separability hypothesis. The Lean predicate `IsPCFAllDivisors`
contains generic separability (convention C5 of the fidelity review), so the
source clause holds in Lean once that separability is automatic.

For a `k`-morphism (`f ≫ s = s`) of a zero-dimensional integral scheme
locally of finite type over `k` it is automatic: the function field is
finite over `k`, the generic stalk map is a `k`-algebra endomorphism of it,
hence bijective, hence separable. Without `f ≫ s = s` it fails: Frobenius of
`Spec 𝔽_p(t)` is a finite surjective inseparable self-map of a
zero-dimensional variety over `k = 𝔽_p(t)` that is not a `k`-morphism.

Using this, l. 571 ("In dimension one, PCF all the way down is the same as
PCF") holds for `k`-morphisms of integral schemes of dimension at most one.
The file also proves the dimension inequality behind l. 554–555: the reduced
closure of a non-generic point has dimension at most one less than the
ambient scheme.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- On an integral, locally Noetherian scheme of dimension at most zero,
every point is the generic point. -/
theorem eq_genericPoint_of_topologicalKrullDim_le_zero
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : topologicalKrullDim X ≤ (0 : WithBot ℕ∞)) (x : X) :
    x = genericPoint X := by
  haveI : IsLocallyArtinian X := .of_topologicalKrullDim_le_zero hX
  exact ((genericPoint_spec X).specializes (Set.mem_univ x)).eq.symm

/-- A field homomorphism that is bijective makes the extension separable. -/
theorem isSeparable_of_bijective_algebraMap {K L : Type*} [Field K] [Field L]
    [Algebra K L] (h : Function.Bijective (algebraMap K L)) :
    Algebra.IsSeparable K L := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := h.2 x
  exact isSeparable_algebraMap y

/-- The points of the spectrum of a field coincide. -/
theorem spec_field_point_eq (k : Type u) [Field k] (x y : Spec (.of k)) : x = y := by
  haveI := x.isPrime
  haveI := y.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime x.asIdeal
  have hy : y.asIdeal = ⊥ := Ideal.eq_bot_of_prime y.asIdeal
  exact PrimeSpectrum.ext (hx.trans hy.symm)

/-- **`def:pcfawd`, dimension-zero clause, separability.** A finite dominant
`k`-morphism of an integral scheme of dimension at most zero, locally of
finite type over `k`, is generically separable: its generic stalk map is a
`k`-algebra endomorphism of a finite extension of `k`, hence bijective.

`paper-p.tex` correspondence: Definition 3.3 (`def:pcfawd`). -/
theorem isGenericallySeparable_of_topologicalKrullDim_zero_of_comp_eq
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hX : topologicalKrullDim X ≤ (0 : WithBot ℕ∞)) (hfs : f ≫ s = s) :
    IsGenericallySeparable f := by
  have hpt := eq_genericPoint_of_topologicalKrullDim_le_zero hX
  haveI : LocallyQuasiFinite s :=
    .of_injective (fun x y _ => (hpt x).trans (hpt y).symm)
  set η := genericPoint X with hη
  have hgp : f η = η := map_genericPoint_eq_of_isDominant f
  -- The base stalk is a field.
  have hsη : s η = genericPoint (Spec (.of k)) := spec_field_point_eq k _ _
  let eA := ((Spec (.of k)).presheaf.stalkCongr
    (Inseparable.of_eq hsη)).commRingCatIsoToRingEquiv
  letI : Field ((Spec (.of k)).presheaf.stalk (s η)) :=
    (eA.toMulEquiv.isField (Field.toIsField (Spec (.of k)).functionField)).toField
  letI : Algebra ((Spec (.of k)).presheaf.stalk (s η)) (X.presheaf.stalk η) :=
    (s.stalkMap η).hom.toAlgebra
  letI : Algebra.QuasiFinite ((Spec (.of k)).presheaf.stalk (s η))
      (X.presheaf.stalk η) := s.quasiFiniteAt η
  letI : Module.Finite ((Spec (.of k)).presheaf.stalk (s η)) (X.presheaf.stalk η) :=
    Algebra.QuasiFinite.iff_of_isArtinianRing.mp inferInstance
  -- The two stalk identities.
  let eX := (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hcomp := Scheme.Hom.stalkMap_comp f s η
  have hcongr := Scheme.Hom.stalkMap_congr_hom (f ≫ s) s hfs η
  have hpoint := Scheme.Hom.stalkMap_congr_point s (f η) η hgp
  let A := (Spec (.of k)).presheaf.stalk (s η)
  let K := X.presheaf.stalk η
  let φ := (f.stalkMap η).hom
  let ψ : A →+* K := (s.stalkMap η).hom
  have hφψ : ∀ b, φ ((s.stalkMap (f η)).hom b) =
      ψ (((Spec (.of k)).presheaf.stalkCongr
        (Inseparable.of_eq (congrArg s hgp))).hom.hom b) := by
    intro b
    have h := congrArg (fun F => F.hom b) (hcomp.symm.trans hcongr)
    exact h
  have heψ : ∀ b, eX ((s.stalkMap (f η)).hom b) =
      ψ (((Spec (.of k)).presheaf.stalkCongr
        (Inseparable.of_eq (congrArg s hgp))).hom.hom b) := by
    intro b
    have h := congrArg (fun F => F.hom b) hpoint
    exact h
  let c := ((Spec (.of k)).presheaf.stalkCongr
        (Inseparable.of_eq (congrArg s hgp))).commRingCatIsoToRingEquiv
  have hσ : ∀ a : A, φ (eX.symm (ψ a)) = ψ a := by
    intro a
    obtain ⟨b, rfl⟩ := c.surjective a
    have h1 : eX.symm (ψ (c b)) = (s.stalkMap (f η)).hom b := by
      rw [RingEquiv.symm_apply_eq]
      exact (heψ b).symm
    rw [h1]
    exact hφψ b
  let σ : K →ₐ[A] K :=
    { toRingHom := φ.comp eX.symm.toRingHom
      commutes' := fun a => hσ a }
  have hσbij : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  have hφ : (φ : _ → _) = σ ∘ eX := by
    funext x
    change φ x = φ (eX.symm (eX x))
    rw [RingEquiv.symm_apply_apply]
  have hfield : IsField (X.presheaf.stalk (f η)) := eX.toMulEquiv.isField (Field.toIsField _)
  letI : Field (X.presheaf.stalk (f η)) := hfield.toField
  letI := (f.stalkMap η).hom.toAlgebra
  change Algebra.IsSeparable (X.presheaf.stalk (f η)) (X.presheaf.stalk η)
  apply isSeparable_of_bijective_algebraMap
  change Function.Bijective φ
  rw [hφ]
  exact hσbij.comp eX.bijective

/-- **`def:pcfawd`, dimension-zero clause.** For a finite dominant
`k`-morphism of an integral scheme of dimension at most zero, locally of
finite type over `k`, PCF all the way down holds with no separability
hypothesis, as in the source.

`paper-p.tex` correspondence: Definition 3.3 (`def:pcfawd`). -/
theorem isPCFAllDivisors_of_topologicalKrullDim_zero_of_comp_eq
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hX : topologicalKrullDim X ≤ (0 : WithBot ℕ∞)) (hfs : f ≫ s = s) :
    IsPCFAllDivisors k s f :=
  isPCFAllDivisors_of_topologicalKrullDim_zero k s f hX
    (isGenericallySeparable_of_topologicalKrullDim_zero_of_comp_eq k s f hX hfs)

/-- Iterates of a `k`-morphism are `k`-morphisms. -/
theorem end_pow_asHom_comp_eq {X S : Scheme.{u}} (s : X ⟶ S) (f : X ⟶ X)
    (hfs : f ≫ s = s) (n : ℕ) : (End.of f ^ n).asHom ≫ s = s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, End.mul_asHom]
      rw [Category.assoc, ih]
      exact hfs

attribute [local instance] specializationOrder in
/-- `paper-p.tex`, l. 554–555 (dimension inequality): the reduced closure of
a non-generic point of an integral scheme has topological Krull dimension at
most one less than the ambient scheme. This is the inequality that makes the
divisor recursion of `def:pcfawd` terminate; the source's equality
"drops by one" additionally uses the dimension formula for varieties
(Stacks `0A21`), which is not formalized here. -/
theorem topologicalKrullDim_pointClosure_add_one_le
    {X : Scheme.{u}} [IsIntegral X] (y : X) (hy : y ≠ genericPoint X) :
    topologicalKrullDim (pointClosureIdealSheaf y).subscheme + 1 ≤
      topologicalKrullDim X := by
  let ι := (pointClosureIdealSheaf y).subschemeι
  have hstrict : StrictMono ι :=
    ι.continuous.specialization_monotone.strictMono_of_injective
      ι.isClosedEmbedding.injective
  have hle : ∀ z, ι z ≤ y := by
    intro z
    have h1 : genericPoint (pointClosureIdealSheaf y).subscheme ⤳ z :=
      genericPoint_specializes z
    have h2 := ι.continuous.specialization_monotone h1
    rw [pointClosureSubscheme_genericPoint] at h2
    exact h2
  let F : (pointClosureIdealSheaf y).subscheme → Set.Iic y := fun z => ⟨ι z, hle z⟩
  have hF : StrictMono F := fun a b hab => hstrict hab
  have hdim : Order.krullDim (pointClosureIdealSheaf y).subscheme ≤ Order.height y := by
    rw [Order.height_eq_krullDim_Iic]
    exact Order.krullDim_le_of_strictMono F hF
  have hlt : y < genericPoint X := lt_of_le_of_ne (genericPoint_specializes y) hy
  have hcoh : 1 ≤ Order.coheight y := by
    have := Order.coheight_add_one_le hlt
    exact le_trans (by simp) this
  have hsum : ((Order.height y + Order.coheight y : ℕ∞) : WithBot ℕ∞) ≤
      Order.krullDim X := by
    rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun a : X => Order.height a + Order.coheight a) y)
  rw [← scheme_orderKrullDim_eq_topologicalKrullDim,
    ← scheme_orderKrullDim_eq_topologicalKrullDim]
  calc Order.krullDim (pointClosureIdealSheaf y).subscheme + 1
      ≤ (Order.height y : WithBot ℕ∞) + 1 := by gcongr
    _ ≤ ((Order.height y + Order.coheight y : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]
        gcongr
        exact WithBot.coe_le_coe.mpr hcoh
    _ ≤ Order.krullDim X := hsum

/-- The actual return of `def:pcfawd` on the original reduced closure of an
eventually periodic point is a morphism over the restricted structure map. -/
theorem eventuallyPeriodicPointReturn_comp_eq {X S : Scheme.{u}}
    (s : X ⟶ S) (f : X ⟶ X) (hfs : f ≫ s = s) (r p : ℕ) (x : X)
    (h : schemePointIterate f (r + p) x = schemePointIterate f r x) :
    eventuallyPeriodicPointReturn f r p x h ≫
        ((pointClosureIdealSheaf (schemePointIterate f r x)).subschemeι ≫ s) =
      (pointClosureIdealSheaf (schemePointIterate f r x)).subschemeι ≫ s := by
  unfold eventuallyPeriodicPointReturn pointClosureReturnMap
  rw [pointClosureSubschemeMap_subschemeι_assoc, end_pow_asHom_comp_eq s f hfs p]

/-- In an integral scheme of dimension at most one, the reduced closure of a
non-generic point has dimension at most zero. -/
theorem topologicalKrullDim_pointClosure_le_zero
    {X : Scheme.{u}} [IsIntegral X] (hX : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (y : X) (hy : y ≠ genericPoint X) :
    topologicalKrullDim (pointClosureIdealSheaf y).subscheme ≤ (0 : WithBot ℕ∞) := by
  have h := (topologicalKrullDim_pointClosure_add_one_le y hy).trans hX
  generalize topologicalKrullDim (pointClosureIdealSheaf y).subscheme = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
      have h' : d + 1 ≤ 1 := by exact_mod_cast h
      have : d ≤ 0 := by
        induction d using ENat.recTopCoe with
        | top => simp at h'
        | coe d =>
            have h'' : d + 1 ≤ 1 := by exact_mod_cast h'
            exact_mod_cast (by omega : d ≤ 0)
      exact_mod_cast this

/-- **`paper-p.tex`, l. 571.** In dimension one (more precisely, dimension at
most one), PCF all the way down is the same as PCF, for finite dominant
`k`-morphisms of integral schemes locally of finite type over `k`. PCF here is
the source's separable normalized PCF (convention C5).

`paper-p.tex` correspondence: Definition 3.3 (`def:pcfawd`). -/
theorem isPCFAllDivisors_iff_of_topologicalKrullDim_le_one
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hX : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (hfs : f ≫ s = s) :
    IsPCFAllDivisors k s f ↔ IsSeparableNormalizedPCF k s f := by
  rw [isPCFAllDivisors_iff]
  refine ⟨And.left, fun hpcf => ⟨hpcf, fun C r p _ hperiodic => ?_⟩⟩
  have hcoh : Order.coheight (schemePointIterate f r C.1) = 1 :=
    coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k s
      (End.of f ^ r).asHom C
  have hne : schemePointIterate f r C.1 ≠ genericPoint X :=
    SchemeDivisorPoint.ne_genericPoint (X := X) ⟨_, hcoh⟩
  exact isPCFAllDivisors_of_topologicalKrullDim_zero_of_comp_eq k _ _
    (topologicalKrullDim_pointClosure_le_zero hX _ hne)
    (eventuallyPeriodicPointReturn_comp_eq s f hfs r p C.1 hperiodic)

#print axioms eq_genericPoint_of_topologicalKrullDim_le_zero
#print axioms isGenericallySeparable_of_topologicalKrullDim_zero_of_comp_eq
#print axioms isPCFAllDivisors_of_topologicalKrullDim_zero_of_comp_eq
#print axioms end_pow_asHom_comp_eq
#print axioms topologicalKrullDim_pointClosure_add_one_le
#print axioms eventuallyPeriodicPointReturn_comp_eq
#print axioms topologicalKrullDim_pointClosure_le_zero
#print axioms isPCFAllDivisors_iff_of_topologicalKrullDim_le_one

end

end Pcf
