/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimCoreDefs
public import Pcf.Bounding.PrincipalQuotientRegular

/-!
# Ambient regularity at a good exceptional point

In the normalized blow-up argument of `latex/paper-p.tex`, Theorem
`thm:allcodim-normal`, the local divisor is principal and its reduced
closure has a discrete valuation stalk at a good codimension-two point.
The principal-quotient regularity criterion makes the ambient normal
surface stalk regular there. This is the local regularity needed before
purity and the tame root-cover argument.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- At a good codimension-two point of the exceptional divisor, the
ambient stalk is regular. The hypotheses are precisely the principal
equation and DVR quotient in `AllCodimGoodAt`. -/
theorem AllCodimGoodAt.ambient_regular
    (p : ℕ) {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (β : Y ⟶ X) (y : X) (B : Set X)
    (d : SchemeDivisorPoint Y) (E : Y) (hdE : d.1 ⤳ E)
    (h : AllCodimGoodAt p β y B d E hdE)
    (hE : Order.coheight E = 2) :
    IsRegularLocalRing (Y.presheaf.stalk E) := by
  let P := stalkGenerizationPrime Y hdE
  letI : P.IsPrincipal := h.principal
  letI : IsDiscreteValuationRing (Y.presheaf.stalk E ⧸ P) := h.divisor_dvr
  haveI : IsRegularLocalRing (Y.presheaf.stalk E ⧸ P) := inferInstance
  have hdimP : ringKrullDim (Y.presheaf.stalk E ⧸ P) = 1 :=
    IsDiscreteValuationRing.ringKrullDim_eq_one _
  have hdimE : 2 ≤ ringKrullDim (Y.presheaf.stalk E) := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hE]
    norm_num
  exact isRegularLocalRing_of_principal_quotient_of_dim_one P hdimP hdimE

#print axioms AllCodimGoodAt.ambient_regular

end
end Pcf
