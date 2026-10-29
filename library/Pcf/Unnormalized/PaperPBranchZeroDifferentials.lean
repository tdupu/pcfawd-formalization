/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.SchemeBranchZero
public import Pcf.Stacks.Purity.Tag0BMBSchemeAPI

/-!
# `branch₀` as the image of the support of `Ω`

`paper-p.tex`, prose after `lem:branch-crit` (l. 2144–2147):

> By [Stacks 02GF (3)], the set of points at which `g` is not unramified is the support of
> `Ω_{A/B}`, so `branch₀(g)` is the union of the integral effective divisors contained in the
> image of the support of `Ω_{A/B}`.

Encoding. The stalk `Ω_{X/Y,x}` is encoded as the module of differentials of the actual
stalk map `𝒪_{Y,g x} → 𝒪_{X,x}`; these agree by localization of Kähler differentials
(Stacks `00RT`, `01UM`). On an affine chart the support is also identified with Mathlib's
`Module.support` of `Ω[Γ(X,V)⁄Γ(Y,U)]` (`mem_schemeDifferentialSupport_iff_chart`).
Integral effective divisors are their generic points (`SchemeDivisorPoint`), and
"contained in a closed set" is `closure {E} ⊆ ·`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf

universe u

variable {X Y : Scheme.{u}}

/-- The support of `Ω_{X/Y}`: the points `x` with `Ω_{X/Y,x} ≠ 0`, where the stalk is
computed as `Ω[𝒪_{X,x}⁄𝒪_{Y,g x}]` for the actual stalk map. -/
def schemeDifferentialSupport (g : X ⟶ Y) : Set X :=
  {x | letI := (g.stalkMap x).hom.toAlgebra
    Nontrivial Ω[X.presheaf.stalk x⁄Y.presheaf.stalk (g x)]}

/-- `x ∈ Supp Ω_{X/Y}` iff the stalk map at `x` is not formally unramified. -/
theorem mem_schemeDifferentialSupport_iff (g : X ⟶ Y) (x : X) :
    x ∈ schemeDifferentialSupport g ↔ SchemeStalkNotFormallyUnramifiedAt g x := by
  let := (g.stalkMap x).hom.toAlgebra
  change Nontrivial _ ↔ ¬ Algebra.FormallyUnramified _ _
  rw [Algebra.formallyUnramified_iff, not_subsingleton_iff_nontrivial]

/-- **Stacks `02GF`, (1) ⇔ (3)**, for a morphism locally of finite type: `g` is unramified
at `x` iff `Ω_{X/Y,x} = 0`. -/
@[stacks 02GF "(1) ⇔ (3) only, for `f` locally of finite type; `Ω_{X/S,x}` encoded as the \
module of differentials of the stalk map, which Stacks identifies with the stalk via 01UM"]
theorem isStacksUnramifiedAt_iff_differential_subsingleton (g : X ⟶ Y)
    [LocallyOfFiniteType g] (x : X) :
    Stacks.IsStacksUnramifiedAt g x ↔ x ∉ schemeDifferentialSupport g := by
  rw [mem_schemeDifferentialSupport_iff, SchemeStalkNotFormallyUnramifiedAt, not_not,
    Stacks.isStacksUnramifiedAt_iff_stalkMap]
  refine ⟨fun h => h.2, fun h => ⟨⟨⊤, trivial, ?_⟩, h⟩⟩
  infer_instance

/-- **l. 2144–2145.** For `g` locally of finite type, the set of points at which `g` is not
unramified is the support of `Ω_{X/Y}`. -/
theorem schemeDifferentialSupport_eq_notUnramified (g : X ⟶ Y) [LocallyOfFiniteType g] :
    schemeDifferentialSupport g = {x | ¬ Stacks.IsStacksUnramifiedAt g x} := by
  ext x
  rw [Set.mem_ofPred_eq, isStacksUnramifiedAt_iff_differential_subsingleton, not_not]

/-- The support of `Ω_{X/Y}` is closed (for `g` locally of finite type). -/
theorem isClosed_schemeDifferentialSupport (g : X ⟶ Y) [LocallyOfFiniteType g] :
    IsClosed (schemeDifferentialSupport g) := by
  rw [schemeDifferentialSupport_eq_notUnramified]
  exact (Stacks.isOpen_setOf_isStacksUnramifiedAt (f := g)).isClosed_compl

/-- Affine-chart form: on affine opens `V ⊆ g⁻¹ U`, a point of `V` lies in `Supp Ω_{X/Y}`
iff its prime lies in `Module.support` of `Ω[Γ(X,V)⁄Γ(Y,U)]`. -/
theorem mem_schemeDifferentialSupport_iff_chart (g : X ⟶ Y) {x : X} (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)
    (hx : x ∈ V) :
    letI := (g.appLE U V hVU).hom.toAlgebra
    x ∈ schemeDifferentialSupport g ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Module.support Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)] := by
  let := (g.appLE U V hVU).hom.toAlgebra
  rw [mem_schemeDifferentialSupport_iff, SchemeStalkNotFormallyUnramifiedAt,
    Stacks.formallyUnramified_stalkMap_iff U hU V hV hVU hx, ← Set.notMem_compl_iff,
    ← Algebra.unramifiedLocus_eq_compl_support]
  rfl

/-- **l. 2144–2147, membership form.** In characteristic zero, for a finite dominant map of
integral schemes, an integral effective divisor `E` of `Y` is in `branch₀(g)` iff its generic
point lies in the image of `Supp Ω_{X/Y}`. -/
theorem mem_schemeUnnormalizedBranchZero_iff_mem_image_differentialSupport
    (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] [CharZero k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    (E : SchemeDivisorPoint Y) :
    E ∈ schemeUnnormalizedBranchZero g ↔ E.1 ∈ g '' schemeDifferentialSupport g := by
  rw [mem_schemeUnnormalizedBranchZero_iff_critical_divisor g k E]
  constructor
  · rintro ⟨P, hP, hcrit⟩
    exact ⟨P.1, (mem_schemeDifferentialSupport_iff g P.1).2 hcrit, hP⟩
  · rintro ⟨x, hx, hgx⟩
    let P : SchemeDivisorPoint X :=
      ⟨x, coheight_eq_one_of_finite_preimage g x (hgx ▸ E.2)⟩
    exact ⟨P, hgx, (mem_schemeDifferentialSupport_iff g x).1 hx⟩

/-- **l. 2144–2147, as stated.** `branch₀(g)` consists of exactly the integral effective
divisors of `Y` contained in the (closed) image of the support of `Ω_{X/Y}`. -/
theorem schemeUnnormalizedBranchZero_eq_divisors_in_image_differentialSupport
    (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] [CharZero k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)] :
    schemeUnnormalizedBranchZero g =
      {E | closure {E.1} ⊆ g '' schemeDifferentialSupport g} := by
  have hcl : IsClosed (g '' schemeDifferentialSupport g) :=
    g.isClosedMap _ (isClosed_schemeDifferentialSupport g)
  ext E
  rw [mem_schemeUnnormalizedBranchZero_iff_mem_image_differentialSupport g k E,
    Set.mem_ofPred_eq, hcl.closure_subset_iff, Set.singleton_subset_iff]

#print axioms isStacksUnramifiedAt_iff_differential_subsingleton
#print axioms mem_schemeDifferentialSupport_iff_chart
#print axioms schemeUnnormalizedBranchZero_eq_divisors_in_image_differentialSupport

end Pcf
