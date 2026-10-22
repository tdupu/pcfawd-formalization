/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimCoreDefs

/-!
# The étale restriction statement at a codimension-two point

This is the local conclusion "`φ_m` is étale at `E₀`" in `latex/paper-p.tex`,
proof of Theorem `thm:allcodim-normal`, stated for an arbitrary finite
dominant map `F : X_S ⟶ Y` of normal schemes with prime-to-`p` monodromy.
At a codimension-two point `E₀` on the closure of a divisor `d'`, if the image
divisor `d = F d'` is principal and regular at `E = F E₀`, and `F` is étale at
every other divisor over a generization of `E`, then the closure of `d'` is a
discrete valuation ring at `E₀`, unramified over the closure of `d` at `E`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

noncomputable section

/-- The chart property, for the prime `p` and base field `k`. -/
def AllCodimChartProperty (p : ℕ) (k : Type u) [Field k] [CharP k p] : Prop :=
  ∀ {Xs Y : Scheme.{u}} [IsIntegral Xs] [IsIntegral Y]
    [IsNormalScheme Xs] [IsNormalScheme Y]
    [IsLocallyNoetherian Xs] [IsLocallyNoetherian Y]
    (_ : Y ⟶ Spec (.of k)) (F : Xs ⟶ Y) [IsFinite F] [IsDominant F]
    (_ : IsPrimeToPMonodromyMap p F)
    (d' : SchemeDivisorPoint Xs) (E₀ : Xs) (hdE : d'.1 ⤳ E₀)
    (_ : Order.coheight E₀ = 2)
    (_ : (stalkGenerizationPrime Y (hdE.map F.continuous)).IsPrincipal)
    (_ : IsDiscreteValuationRing (closureStalk Y (hdE.map F.continuous)))
    (_ : ∀ w : SchemeDivisorPoint Xs, F w.1 ⤳ F E₀ → F w.1 ≠ F d'.1 →
      (F.stalkMap w.1).hom.FormallyEtale),
    IsDiscreteValuationRing (closureStalk Xs hdE) ∧
      (letI := (stalkGenerizationQuotientMap F hdE).toAlgebra
       (maximalIdeal (closureStalk Xs hdE)).ramificationIdx
         (closureStalk Y (hdE.map F.continuous)) = 1)

end
end Pcf
