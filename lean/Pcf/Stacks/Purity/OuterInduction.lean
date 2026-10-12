/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Purity.PuncturedSpectrum
import Pcf.Stacks.Purity.RegularHypersurface

/-!
# The hypersurface induction step in Stacks Tag `0BMA`

This file formalizes the outer induction in the higher-dimensional case of Stacks Tag `0BMA`.
For a minimal generator `x` of the maximal ideal of a regular local ring `R`, it constructs the
canonical map from the punctured spectrum of `R/(x)` to the punctured spectrum of `R`, and hence
the restriction of a finite etale cover to the punctured hypersurface.

The predicate `HypersurfaceFiniteEtaleLifting` is the exact conclusion of Stacks Tag `0BLM` in
this affine local situation: if the restriction of a cover to the punctured hypersurface extends
over the whole hypersurface, then the original cover extends over `Spec R`.  The main theorem
proves the genuine `0BMA` induction step from this `0BLM` input and purity for `R/(x)`.  The last
theorem also performs the regular-hypersurface choice and dimension drop used in the proof of
Tag `0BMA`.

No proof of Tag `0BLM` is claimed here, and neither Tag `0BMA` nor Tag `0BMB` is repackaged as
an assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

section Hypersurface

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (x : R)

local notation "Rbar" => R ⧸ Ideal.span (Set.singleton x)

/-- The closed immersion `Spec(R/(x)) → Spec R`, restricted to punctured spectra.

The map really lands in the punctured spectrum: the quotient map is a surjective local
homomorphism, so its map on spectra sends the closed point to the closed point and no other
prime to the closed point. -/
noncomputable def puncturedHypersurfaceMap
    [IsLocalRing Rbar] :
    puncturedSpectrumScheme Rbar ⟶ puncturedSpectrumScheme R := by
  let q : R →+* Rbar := Ideal.Quotient.mk (Ideal.span (Set.singleton x))
  letI : IsLocalHom q :=
    IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  let j : Spec (.of Rbar) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom q)
  let g : puncturedSpectrumScheme Rbar ⟶ Spec (.of R) :=
    (puncturedSpectrum Rbar).ι ≫ j
  apply IsOpenImmersion.lift (puncturedSpectrum R).ι g
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  change g z ≠ IsLocalRing.closedPoint R
  intro hz
  let z' : PrimeSpectrum Rbar := z.1
  have hz' : PrimeSpectrum.comap q z.1 = IsLocalRing.closedPoint R := by
    have hgz : g z = PrimeSpectrum.comap q z' := by rfl
    rw [hgz] at hz
    exact hz
  have hclosed :
      PrimeSpectrum.comap q (IsLocalRing.closedPoint Rbar) =
        IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint q
  have : z.1 = IsLocalRing.closedPoint Rbar :=
    (PrimeSpectrum.comap_injective_of_surjective q Ideal.Quotient.mk_surjective)
      (hz'.trans hclosed.symm)
  exact ((mem_puncturedSpectrum_iff Rbar z.1).mp z.2) this

/-- Pull a finite etale cover of the punctured spectrum of `R` back to the punctured
hypersurface `Spec(R/(x)) \ {m}`.  This is the cover denoted `V₀` in Tags `0BLM` and `0BMA`. -/
noncomputable def restrictFiniteEtaleToPuncturedHypersurface
    [IsLocalRing Rbar] :
    FiniteEtaleCover (puncturedSpectrumScheme R) ⥤
      FiniteEtaleCover (puncturedSpectrumScheme Rbar) :=
  FiniteEtaleCover.pullback _ (puncturedHypersurfaceMap R x)

/-- Purity for a local ring in the sense used in clause (1) of Stacks Tag `0BMA`: every finite
etale cover of the punctured spectrum extends over the whole spectrum. -/
abbrev PuncturedSpectrumPurity : Prop :=
  (restrictFiniteEtaleToPuncturedSpectrum R).EssSurj

/-- The affine-local conclusion of Stacks Tag `0BLM` for the hypersurface `(x)`.

For every finite etale cover `V` of the punctured spectrum of `R`, if its pullback `V₀` to the
punctured spectrum of `R/(x)` is the restriction of a finite etale cover of `Spec(R/(x))`, then
`V` itself is the restriction of a finite etale cover of `Spec R`.

This is deliberately a named intermediate property, not a proof or an assumption of purity.
It isolates exactly the local-cohomological lifting result which Stacks Tag `0BLM` supplies. -/
def HypersurfaceFiniteEtaleLifting
    [IsLocalRing Rbar] [IsNoetherianRing Rbar] : Prop :=
  ∀ V : FiniteEtaleCover (puncturedSpectrumScheme R),
    (∃ Y₀ : FiniteEtaleCover (Spec (.of Rbar)),
      Nonempty
        ((restrictFiniteEtaleToPuncturedSpectrum Rbar).obj Y₀ ≅
          (restrictFiniteEtaleToPuncturedHypersurface R x).obj V)) →
      ∃ Y : FiniteEtaleCover (Spec (.of R)),
        Nonempty ((restrictFiniteEtaleToPuncturedSpectrum R).obj Y ≅ V)

omit [IsNoetherianRing R] in
/-- The higher-dimensional induction step of Stacks Tag `0BMA`.

Purity for the regular hypersurface `R/(x)` says that `V₀` extends over the hypersurface;
Tag `0BLM` then lifts that extension to one of `V` over `Spec R`. -/
theorem puncturedSpectrumPurity_of_hypersurface_lifting
    [IsLocalRing Rbar] [IsNoetherianRing Rbar]
    (hquotient : PuncturedSpectrumPurity Rbar)
    (hlift : HypersurfaceFiniteEtaleLifting R x) :
    PuncturedSpectrumPurity R := by
  rcases hquotient with ⟨hquotient⟩
  constructor
  intro V
  exact hlift V (hquotient ((restrictFiniteEtaleToPuncturedHypersurface R x).obj V))

end Hypersurface

/-- The complete outer induction assembly in the `d + 1 ≥ 3` branch of Stacks Tag `0BMA`.

The theorem chooses a minimal generator `x ∈ m \ m²`, installs the proved regularity of
`R/(x)`, records its exact dimension `d`, invokes the induction hypothesis there, and applies
the `0BLM` lifting property.  Thus the only mathematical inputs left at this stage are precisely
the lower-dimensional purity theorem and the hypersurface lifting theorem, rather than the
terminal statement of `0BMA` itself. -/
theorem regularLocal_puncturedSpectrumPurity_induction_step
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (_hd : 2 ≤ d) (hdim : ringKrullDim R = d + 1)
    (hInduction :
      ∀ (x : R) (_hx : x ∈ maximalIdeal R) (_hx2 : x ∉ maximalIdeal R ^ 2)
        [IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R))],
        ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) = d →
          PuncturedSpectrumPurity (R ⧸ Ideal.span ({x} : Set R)))
    (hLifting :
      ∀ (x : R) (_hx : x ∈ maximalIdeal R) (_hx2 : x ∉ maximalIdeal R ^ 2)
        [IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R))],
        HypersurfaceFiniteEtaleLifting R x) :
    PuncturedSpectrumPurity R := by
  obtain ⟨x, hx, hx2, hregular, hdimQuotient⟩ :=
    exists_regularLocalRing_quotient_of_ringKrullDim_eq_succ R d hdim
  letI : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top hx)
  letI : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := hregular
  exact puncturedSpectrumPurity_of_hypersurface_lifting R x
    (hInduction x hx hx2 hdimQuotient) (hLifting x hx hx2)

#print axioms puncturedHypersurfaceMap
#print axioms restrictFiniteEtaleToPuncturedHypersurface
#print axioms puncturedSpectrumPurity_of_hypersurface_lifting
#print axioms regularLocal_puncturedSpectrumPurity_induction_step

end Pcf.Stacks
