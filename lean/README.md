# Lean formalization of "PCF All the Way Down"

A Lean 4 + Mathlib formalization of parts of the manuscript *PCF all the way down* (Dupuy, Levy,
Tucker, Wang).

| Field | Value |
| --- | --- |
| Lean | `4.35.0` |
| Mathlib | `v4.35.0` (rev `56a005855ea1`) |
| Build | `lake build` from this directory |
| Assumed inputs | [AXIOMS.md](AXIOMS.md) |
| Manuscript | *PCF all the way down*, cited below **by its LaTeX `\label`s**, never by number (numbers change between versions of the manuscript). Labels refer to `latex/paper.tex` unless marked `paper-p.tex` (the characteristic-`p` version) |

## Dedicated paper targets

| Manuscript | Active Lake project | Entry points |
| --- | --- | --- |
| `latex/paper.tex` | [`paper-char-zero/`](paper-char-zero/readme.md) | `PaperCharZero.theoremA`, `PaperCharZero.cor_pcfawd` |

The characteristic-zero project also imports the formalized supporting
results and examples of `paper.tex`; see its `readme.md` and
`validation.md`.

## Theorem A in both characteristics and every codimension

This section cites `paper-p.tex`, the characteristic-`p` version of the
manuscript. Theorem `thm:A` of `paper-p.tex` is formalized as
`Pcf.isPCFAllSubvarieties_charZero_of_downstairsPCF` and
`Pcf.isPCFAllSubvarieties_charP_of_downstairsPCF`; the second assumes
prime-to-`p` monodromy. Both conclude the depth-indexed recursive property
`Pcf.IsPCFAllSubvarieties` on original reduced point closures in every
codimension. The proof includes the normalized Rees blow-up, generic fibre
multiplicity, tame chart, and finite-cover transfer. The exact source map,
build evidence, and axiom audit are in [THEOREM-A.md](THEOREM-A.md).

## What the paper proves, and what this development proves

In `latex/paper.tex`, Theorem A (`thm:A` = `thm:general`; not the `thm:A` of
`paper-p.tex` above) and Corollary `cor:pcfawd` say: every finite
surjective post-critically finite self-map `f` of a variety over a field of characteristic
zero is *PCF all the way down* (`def:pcfawd`) — for every preperiodic integral effective
divisor `A` with `f^{r+s}(A) = f^r(A)`, the restriction `f^s|_{f^r(A)}` is PCF, recursively.
The proof has three layers:

1. **Divisorial dynamics** (`sec:defs`, `sec:pcf`, `sec:prelim`): branch loci, `PC(f)`,
   iterates, towers, normalization.
2. **The bounding theorem** (`thm:bounding`, `sec:bounding`): for `f : X → Y` finite
   surjective between *normal* varieties and `A ⊂ X` an integral effective divisor with image
   `B`, the restriction `g = f|_A` is étale at the generic point of every divisor of `A`
   whose image is not in `Σ = (B ∩ Z) ∪ (B ∩ Sing Y) ∪ Sing B`. Proved by Zariski–Nagata
   purity and Abhyankar's lemma.
3. **Assembly** (`sec:main`, `sec:general`): for normal `X` and invariant `A`, `Σ` does not
   depend on the iterate, so `g` is `1`-PCF (`thm:normal-invariant`); the general case passes
   to the normalization (`thm:general`).

**This development machine-checks the divisorial dynamics, the affine-chart proof of the
bounding theorem, and the one-divisor geometric theorem `thm:general`, including a
nonnormal ambient scheme.**  Local Zariski–Nagata purity (Stacks `0BMB`) and Abhyankar's
lemma for a regular divisor (Stacks `0EYG`/`0EYH`) are **proved** (2026-10-16/17), so the
characteristic-zero headline `Pcf.pcfAllTheWayDown_charZero_unconditional` (and its compared
form `Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional`, in `Pcf/Palomar/Unconditional.lean`)
assumes nothing beyond its stated geometric and PCF hypotheses; `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`.  The proved local inputs are:

* purity: `Pcf.Stacks.zariskiNagataPurity` (affine, `Pcf/Stacks/Purity/Tag0BMA.lean`), and at
  scheme level `Pcf.Stacks.isStacksEtaleAt_of_zariskiNagataPurity` (Stacks' pointwise notions)
  and `Pcf.Stacks.exists_etale_of_zariskiNagataPurity` (Mathlib vocabulary);
* Abhyankar: `Pcf.Stacks.abhyankarLemma` (every positive integer invertible) and
  `Pcf.Stacks.abhyankarLemmaTame` (tamely ramified in codimension one, any characteristic), both
  affine with the normalization proved finite (`Pcf/Stacks/Abhyankar/FiniteNormalization.lean`),
  and at scheme level `Pcf.Stacks.SchemeLevel.abhyankarLemma_scheme` (`0EYG`) and
  `Pcf.Stacks.SchemeLevel.abhyankarLemma_normalization` (`0EYH`).

Their restrictions relative to the tags are recorded in [AXIOMS.md](AXIOMS.md), first
section.  No two declarations state the same proposition: duplicates were removed on 2026-10-17
(AXIOMS.md, "Phase 4", lists them with their replacements).  The older theorems that take purity and Abhyankar as hypotheses
(`Pcf.pcfAllTheWayDown_charZero`, `Pcf.PCFAllTheWayDownLocalTheorems`) are kept unchanged.
Stacks Tag 00NP, the local-domain consequence of regularity needed after Abhyankar, is proved
in Lean.  Concretely:

* Everything in layer 1 that is a statement about sets of divisors, their pushforward and
  ramification indices is **proved**: `prop:iterates`, the orbit characterization of PCF,
  one direction of `lem:normalization`, and — new in this round — `cor:orbit-unnormalized`
  and the comparison `PC ⊆ PC₀ ⊆ PC₁` of `prop:loci-compare`/`def:pcf-unnormalized`.
* Theorem `thm:normal-invariant` is **proved from its inputs**: given the conclusion of
  `thm:bounding` for every iterate (a structure field), the finite set `Σ`, and PCF-ness of
  `f`, the restriction is `1`-PCF (`Pcf.NonEtalePCFSetup.restriction_isNonEtaleBranchPCF`), hence `0`-PCF and PCF
  (`cor:normal-invariant-pcf`). The older `Pcf.PCFSetup.restriction_isPCF` is the same theorem with the
  normalized (`e > 1`) form of the bounding conclusion. `cor:normal-preperiodic` is
  `Pcf.PCFSetup.restriction_isPCF_of_iterate` / `Pcf.NonEtalePCFSetup.restriction_isNonEtaleBranchPCF_of_iterate`.
* The **descent** along a chain of invariant divisors is a genuine induction
  (`Pcf.isPCF_of_isPCF_restriction`), *given a `PCFSetup` at each stage*.
* The affine divisor substrate is now concrete (`Pcf/Bounding/Divisors.lean`).  For a
  finite injective extension with normal Noetherian base, contraction preserves prime
  height and is surjective on height-one primes; `affineDivisorPointEquiv` identifies
  these with codimension-one points of `Spec`, and `affineDivisorUnder` is the actual
  map on those scheme points.  For a finite normal affine self-map,
  `Pcf.divisorDynamicsOfFiniteNormalSelfAlgebra` constructs the resulting `DivisorDynamics`; its step,
  ramification function, step-surjectivity, positivity and finite branch set are all
  proved.  The local ring at every height-one prime is proved to be a DVR, and
  `heightOneRamificationIdx_eq_dvrExponent` identifies Mathlib's length-theoretic index with the
  exponent of the contracted prime in its maximal ideal. The algebraic shrinking lemma
  `exists_principal_localizationAway_of_atPrime_isPrincipal` turns principality in a local
  ring into one equation on a principal-open neighborhood; its height-one specialization
  principalizes a divisor near its generic point, while
  `exists_principal_localizationAway_of_atPrime_ufd` isolates the precise local-UFD input
  needed at an arbitrary point. `heightOneComapPoint` and
  `SchemeDivisorPoint.imagePoint` keep the normalized and possibly nonnormal carriers
  distinct; `finite_heightOne_comap_fiber` and
  `AlgebraicGeometry.Scheme.Hom.finite_divisorPoint_fiber` prove that these maps have finite fibers without
  assuming the target point has codimension one. `affineNonEtaleLocus` is the actual
  codimension-one non-étale locus, and
  `BoundingChart.affineNonEtaleLocus_restriction_eq_empty` proves that it is empty on every
  bounding chart. This closes items 1--3 and the ring-level part of item 5 of the A6
  handoff. The exact local-principality case needed in Step 0 is also proved without the
  full regular-local-UFD theorem:
  `heightOne_isPrincipal_of_regularLocalRing_dim_two` handles a height-one prime in a
  two-dimensional regular local domain with regular one-dimensional quotient, and
  `exists_principal_localizationAway_of_atPrime_regular_dim_two` spreads its equation to
  a principal open.  The low-dimensional localization theorems
  `isRegularRing_of_isRegularLocalRing_of_ringKrullDim_eq_one` and
  `isRegularRing_of_isRegularLocalRing_of_isIntegrallyClosed_dim_two` then promote the
  one- and two-dimensional stalks to Mathlib's global `IsRegularRing` interface.
  `Pcf.LocalBoundingChart` packages these stalk-level hypotheses and derives the existing
  `BoundingChart`, so a regular affine neighborhood and regular-locus openness are no
  longer needed for the algebraic argument. Its cover Noetherianity is derived from
  module-finiteness, and its pointwise height equality is derived from finite injectivity
  and normality rather than supplied as a field. A single `IsIntegrallyClosed S`
  hypothesis also supplies normality of all cover localizations, and the minimal-component
  condition on `p` supplies its primality. The normalization-away-from-the-divisor
  condition is now a theorem as well:
  `isIntegralClosure_localizationAway_of_finite_of_integrallyClosed` derives it from
  module-finiteness, normality of the cover, and the nonzerodivisor condition. That
  nonzerodivisor condition is itself derived from the local dimension drop `2 → 1` by
  `mem_nonZeroDivisors_of_ringKrullDim_eq_two_of_quotient_eq_one`; it is no longer a
  `LocalBoundingChart` field. The local equation is supplied directly by
  `exists_generator_map_atPrime_regular_dim_two`. Generic étaleness is no longer a
  `LocalBoundingChart` field either:
  `isEtaleAt_height_zero_of_charZero_of_integral` derives it from integrality,
  dominance, and characteristic zero. On the actual finite-cover route,
  `LocalBoundingChart.ofFiniteNormalLocalizationOfDivisors` constructs the canonical
  localized cover, proves its finiteness, injectivity, domain and normality, transports
  the height-one source divisor, proves it is minimal over the pulled-back equation, and
  derives tameness from the rational-algebra structure. Its pointed refinement
  `ofFiniteNormalLocalizationOfHeightOneDivisorsAt` takes honest height-one divisors and
  only the Step 0 condition that the selected prime lies on no other member of
  `heightOneBranch`; this condition is proved sufficient by
  `ramified_heightOne_lies_over_of_avoids_other_branch_at`.
  `Pcf.SchemeStalkBoundingLocalizationPresentation` records the natural quotient-ring
  algebra maps to the two actual stalks, their localization properties, and the
  quotient-ring map square. Lean constructs the two coordinate isomorphisms, their
  localized square and the arrow isomorphism, then derives formal étaleness of the
  original stalk from the chart. On the literal affine quotient morphism the entire
  localization presentation is constructed, not assumed, by
  `LocalBoundingChart.toSchemeStalkBoundingLocalizationPresentation`. The stronger
  open-neighbourhood interfaces remain available when global affine coordinates exist,
  but are not required by the dynamics. For actual closed subschemes,
  `Scheme.IdealSheafData.quotientStalk_isLocalization` constructs the quotient-to-stalk
  localization, while `quotientAppLE`, `comap_quotientPoint_quotientAppLE`, and
  `stalkMap_comp_quotientStalkAlgebraMap` derive the quotient map, contracted point, and
  stalk square. `Pcf.closedSubschemeStalkBoundingLocalizationPresentation` therefore
  constructs the entire dynamics-facing localization presentation from affine
  section-quotient coordinates. For a restriction induced by an actual ambient morphism,
  `quotientAppLE_subschemeMap_eq_quotientMap` proves that the canonical quotient-chart map
  is exactly the quotient of the ambient map on sections, while
  `closedSubschemeStalkBoundingLocalizationPresentationOfAmbientMap` constructs the full
  stalk presentation from only the two equalities identifying the defining ideals. On
  affine ambient schemes this reduces further:
  `affineIdealSheaf_le_map_of_localBoundingChart` derives the ideal-sheaf containment from
  the chart and the single equality `J.ideal ⊤ = (a)`, and
  `affineIdealSheafStalkBoundingLocalizationPresentation` constructs the restricted
  morphism and full stalk presentation. The source ideal is definitionally
  `I.ideal ⊤`. Finally,
  `exists_principal_comap_affineBasicOpen_of_atPrime_regular_dim_two` derives the target
  equality on an actual affine basic-open scheme from the regular two-dimensional ambient
  local ring and regular one-dimensional divisor quotient.
  `Scheme.Hom.stalkQuotientKerEquiv` remains an independent
  first-isomorphism theorem, but no separate stalk-kernel identification is needed on this
  shortest route.
  `Pcf.SchemeNormalizationUnnormalizedDynamics` has no arbitrary `crit₁` field: its
  `crit₁(gᵐ)` is definitionally failure of formal étaleness of the actual stalk map of
  `gᵐ`. `Pcf.SchemeNormalizationPCFSetupChart.notMem_nonEtaleBranch_iterate` therefore derives the bounding
  conclusion without A6's conclusion-equivalent implication. For the actual affine
  divisor morphism `Spec(S/P) → Spec(R/D)`, `Pcf/Bounding/AffineStalkBridge.lean`
  identifies its stalk arrow with the canonical localized chart. The composite
  `toGlobalQuotientSchemeStalkBoundingLocalizationPresentationOfHeightOneDivisorsAt`
  starts from the finite normal algebra, actual divisors, and pointed branch avoidance,
  then returns the exact A6s localization presentation. Finally,
  `Pcf/Bounding/SchemeExtraction.lean` starts with an actual finite dominant scheme
  morphism on affine neighborhoods, actual closed-subscheme ideal sheaves, and an actual
  source point. It obtains the finite faithful section algebra, lifts that quotient point
  to the canonical ambient source prime, contracts it to the target prime, derives both
  divisor incidences and the quotient map, and compares the resulting quotient arrow with
  the actual closed-subscheme stalk arrow. It also identifies the ambient localization
  with the actual ambient stalk and the quotient by the localized divisor ideal with the
  actual divisor stalk. The strongest constructor transports regularity and codimension
  from those geometric stalks and chooses the local equation internally. Thus the
  affine/scheme coordinate, four-prime, quotient-map, stalk-comparison, and local-equation
  plumbing is closed. `pointClosureIdealSheaf` now constructs the reduced divisor ideal
  sheaf from an actual codimension-one point; its affine components are proved to be the
  corresponding prime ideals of height one, and `pointClosureIdealSheaf_map` proves exact
  functoriality under the ambient morphism. The divisor-point specialization
  `pointClosureStalkBoundingLocalizationPresentationOfFiniteDominantNormal` therefore
  constructs both ideal sheaves, their restricted morphism, and their affine height-one
  primes internally. `coheight_apply_eq_one` proves that the finite dominant morphism
  sends a source divisor point to a target divisor point, and
  `pointClosureSubschemeMap_point` proves compatibility of the canonical lifted points.
  The induced map of reduced divisor closures is also proved finite, dominant and
  surjective, so `closurePreimageFiniteDominantNormal` constructs a point above any
  target divisor point. `Pcf/Bounding/DivisorLift.lean` removes the remaining normality
  restriction from the lifting lemma: for any finite dominant morphism of integral
  schemes, a point above a codimension-one point is codimension one. Over a finite-type
  target the canonical map on divisor points is therefore surjective with finite fibres,
  giving the complete scheme-level existence-and-finiteness statement of `lem:lift`.
  `closureStalkBoundingLocalizationPresentationOfFiniteDominantNormal` accepts that
  selected point as a `SchemeDivisorPoint` on the image divisor, so its divisor
  codimension, source preimage, and chart membership are all derived. For the global
  quantifiers, the stronger specified-point constructor
  `closureStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCorrectionAt` keeps the
  particular source point `Q'` and its specified image `Q`. Nonmembership in the literal
  pointwise ambient/divisor singular loci derives both regularity facts, and
  nonmembership in `finiteAffineOtherBranchLocus` derives pointed branch avoidance.
  The exact manuscript route supplies ambient codimension `2` at the selected divisor
  flag. `imageDivisorCartierDataAtOfRegularDimTwo` then uses the proved
  two-dimensional regular-local theorem to construct the equation and its
  nonzerodivisor proof; it does not need the unavailable general theorem that regular
  local rings are UFDs (Stacks 0AG0/0AGA). Functoriality of point-closure restrictions is
  now proved through composition and iteration. `invariantClosureMap` is the actual
  restriction to the reduced invariant divisor, and `invariantClosureMap_iterate`
  identifies its iterate with the restriction of the ambient iterate.
  `invariantClosureStalkBoundingLocalizationOfCorrectionAt` consequently builds the actual
  restricted-iterate stalk chart from the literal Step 0 data and the two named local
  covering inputs. `InvariantDivisorSchemeNormalizationPCFSetup` packages the ambient
  endomorphism, invariant divisor, ordinary dynamical/properness data, and literal Step 0
  facts; `toSchemeNormalizationPCFSetupChart` derives the former A6s chart field, and its
  `notMem_nonEtaleBranch_iterate`, `restriction_isNonEtaleBranchPCF`, `normalized_isPCF`, and `normalized_isPCF_of_iterate` theorems give the downstream
  conclusions. No field states formal étaleness, `crit₁` exclusion, or the bounding
  conclusion. Noether normalization now proves codimension preservation for finite
  dominant maps to finite-type integral schemes even when the target is nonnormal.
  `schemeNormalizationUnnormalizedDynamicsOfFiniteType` consequently constructs the normalized and
  unnormalized divisor maps, finite normalization fibers, and their commuting square
  from actual scheme morphisms. The stronger
  `schemeNormalizationUnnormalizedDynamicsOfFiniteBirational` also proves U1 from the structural
  assertion that the finite normalization map is birational (an isomorphism on generic
  stalks). `NormalizationSchemeBridge.lean` canonically constructs the tensor-image
  branch and its localization; `divisorDynamicsOfFiniteNormalization_iterateRamificationIdx` identifies its
  iterate index with the actual lifted scheme iterate.
* Theorem `thm:bounding` is **derived** on an affine chart (`Pcf/Bounding/Chart.lean`,
  `Pcf.BoundingChart.isEtaleAt_restriction`): from Zariski–Nagata purity (Stacks 0BMB) and
  Abhyankar's lemma (Stacks 0EYG/0EYH), each an explicit hypothesis on this route, stated in the
  TauCeti-facing modules `Pcf/Stacks/Purity.lean` and `Pcf/Stacks/Abhyankar.lean` and proved
  under `Pcf/Stacks/Purity/` and `Pcf/Stacks/Abhyankar/`, through
  the manuscript's Steps 1–4 — the five local
  purity hypotheses are packaged as `Pcf.Stacks.ZariskiNagataPurityHypothesesAt`, and
  `Pcf.Stacks.HasZariskiNagataPurityAt` makes the cover étale at that point; Abhyankar gives the named
  `Pcf.Stacks.HasAbhyankarStandardCoverAt` presentation, whose final clause is
  `Pcf.Stacks.IsFiniteDisjointUnionOfStandardTameCovers`; the restriction of a piece to
  the divisor is an isomorphism (`Pcf.LocalModel.quotientMap_bijective`,
  `radical_span_algebraMap_eq_span_root`); the preimage of `A` is a union of components
  (`Pcf/Bounding/LocalStructure.lean`); étaleness descends. All three standard facts the
  manuscript cites in passing are proved in the form used here: étale algebras over a domain
  are reduced (033B, `Pcf/Bounding/Reduced.lean`), points of fibre products exist (01JT,
  `Pcf/Bounding/FiberProduct.lean`), and the finite-presentation pointwise case of étaleness
  being étale-local on the source (036W, `Pcf.Stacks.etaleLocalOnSource`). The former fields
  `PcfGeometry.standardForm` and `Prop41Data.standardForm` (a `KummerWitness`, equivalent to
  the conclusion) are **removed**; `PCFSetup.notMem_branch_iterate`/`NonEtalePCFSetup.notMem_nonEtaleBranch_iterate` remain the *interface*
  of the dynamics and are **derived** on the chart route (`Pcf.PCFSetupChart.notMem_nonEtaleBranch_iterate`,
  `Pcf/Bounding/Wiring.lean`). The preferred actual-scheme route is
  `Pcf.InvariantDivisorSchemeNormalizationPCFSetup.notMem_nonEtaleBranch_iterate`
  (`Pcf/Bounding/SchemeWiring.lean`): it
  replaces A6's conclusion-equivalent implication by actual scheme divisor points,
  actual stalk-defined critical loci, the actual invariant-divisor restriction and its
  iterates, and a chart constructed from literal Step 0 data plus purity and Abhyankar.
* **Formalized at scheme level:** `Pcf.pcfAllTheWayDown_scheme` is the one-divisor
  statement of `thm:general`. Starting from an actual finite dominant endomorphism of an
  integral finite-type characteristic-zero scheme and a preperiodic divisor point, it
  constructs the canonical finite normalization and lifted dynamics, chooses a periodic
  divisor upstairs, applies the invariant-divisor theorem, descends PCF through the actual
  finite dominant cover of reduced divisor closures, and removes the auxiliary positive
  iterate. The two-way normalization comparison is
  `isNormalizedPCF_iff_normalization`; ramified-cover descent is
  `scheme_isPCF_of_ramified_cover`; and the finite singular correction is
  `invariantDivisorSing_finite_of_perfectField`. U1--U5, divisor lifting, codimension-one
  preservation, normalization finiteness, and iterate compatibility are theorems on this
  route, not supplied fields.
* **Formalized recursively at scheme level:**
  `Pcf.schemePCFAllTheWayDownAtDepth_of_cover` iterates the geometric one-divisor
  theorem on the actual reduced divisor closures and their actual return maps;
  `Pcf.schemePCFAllTheWayDown_of_cover` gives every finite depth.  Its covering-tree
  hypothesis contains only the local purity/Abhyankar inputs at each node, not a PCF
  conclusion.  `Pcf.schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch`
  also proves that the ramification-index branch definition is the normalization-image
  of the nonreduced scheme-fibre branch definition.  `Pcf.SchemeDivisorFlag` turns every
  recursive branch into an actual strict specialization chain, and
  `Pcf.schemePCFAllTheWayDown_of_cover_to_dimension` proves that covering data only
  through a natural upper bound for `topologicalKrullDim X` gives the conclusion at
  every depth.  The source-facing proposition is `Pcf.SchemePCFAllTheWayDown`, and
  `Pcf.pcfAllTheWayDown_charZero` proves it from ambient normalized PCF and a single
  `Pcf.PCFAllTheWayDownLocalTheorems` package.  That package contains only the
  universe-wide statements of Zariski--Nagata purity and Abhyankar's lemma, both now proved
  (`Pcf.pcfAllTheWayDown_charZero_unconditional` discharges the package);
  `Pcf.schemePCFCoveringAtDepthOfLocalTheorems` constructs the entire recursive local
  covering tree, so callers no longer supply it.  The equality clause of
  `prop:loci-compare`(3) and the general composite
  branch-locus clauses of `lem:tower-unnormalized` remain outside the formalization.

There is **no `sorry`, no `axiom`, no `admit` and no `native_decide`** in `Pcf/`. The
assumed inputs are structure fields, so `#print axioms` (run for every headline result in
`Pcf/Audit.lean`) reports only `propext`, `Classical.choice`, `Quot.sound` — read
[AXIOMS.md](AXIOMS.md) before drawing conclusions from that.

Two early adversarial reviews of this development (2026-09-21) changed it. The first caught a claim
that the bounding theorem's per-divisor statement had been *derived*; the second caught a
claim that the assumption had been *weakened*. Both refutations are Lean theorems
(`Pcf.nonempty_kummerWitness_iff`, `Pcf.kummerWitness_iff_unramifiedWitness`,
`Pcf.PurityData.ofAbstractZariskiNagataPurity_toAbstractZariskiNagataPurity`). The interfaces they refuted are no longer
fields of anything; the derivation that replaces them is in `Pcf/Bounding/`, and its own
self-audit is AXIOMS.md §G.  The final actual-scheme theorem was independently attacked
from three directions (2026-10-07).

## Layout

```
lean/
├── Pcf.lean                 ← root module, imports everything
├── Pcf/
│   ├── Dynamics.lean        ← sec:defs, sec:prelim: DivisorDynamics, iterates (prop:iterates), lem:normalization
│   ├── Unnormalized.lean    ← app:other-defs, def:pcf-unnormalized: UnnormalizedDynamics, cor:orbit-unnormalized,
│   │                           thm:normal-invariant in 1-PCF form (NonEtalePCFSetup)
│   ├── Restriction.lean     ← sec:main: PCFSetup, thm:normal-invariant (PCF form), descent
│   ├── AllTheWayDown.lean   ← abstract recursive descent; scheme-level one-step theorem lives below
│   ├── Noetherian.lean      ← lem:finitely-many: primes of a Noetherian space
│   ├── Purity.lean          ← thm:purity: local form ⟹ global form
│   ├── NonEtaleLocus.lean   ← the non-étale locus on Spec S is closed
│   ├── Wiring.lean          ← purity ⟹ step_image_ramified_finite for the restricted system
│   ├── SpectrumDynamics.lean← step_image_ramified_finite fully discharged on Spec S
│   ├── ZariskiNagata.lean   ← Stacks 0BMB restated (interderivable — discharges nothing)
│   ├── Ramification.lean    ← thm:bounding Step 4: an isomorphism has index one
│   ├── Geometry.lean        ← thm:bounding Step 0: BoundingCorrectionLoci, PCFGeometry (join to PCFSetup);
│   │                           the retracted witness interfaces, retained as a record
│   ├── LocalModel.lean      ← thm:bounding Step 3 / eq:standard-piece
│   ├── Kummer.lean          ← Stacks 0EYF clauses 1–2 (namespace `Pcf.Kummer`) (Mathlib + `Pcf.LocalModel`; not load-bearing)
│   ├── Stacks/              ← exact theorem boundaries and their proofs, tag by tag
│   │   ├── Purity.lean      ← Tag 0BMB statement `ZariskiNagataPurity`, with 0BMA dependency map
│   │   ├── Purity/          ← purity PROVED: Tag0BMA.lean (`zariskiNagataPurity`), Tag0BMB*.lean,
│   │   │                       Tag0BMBScheme.lean / Tag0BMBSchemeAPI.lean (scheme level), Hartogs,
│   │   │                       completion and fpqc descent, henselian lifting
│   │   ├── Abhyankar.lean   ← Tags 0EYG/0EYH statement `AbhyankarLemma` and standard-cover interface
│   │   ├── Abhyankar/       ← Abhyankar PROVED
│   │   │   ├── FiniteNormalization.lean ← normalization finite; `abhyankarLemmaTame`, and
│   │   │   │                   `abhyankarLemma` (characteristic zero, derived from the tame one)
│   │   │   ├── Tame/        ← tame statement `AbhyankarLemmaTame`, shared proof `abhyankarLemmaTameOfFinite`
│   │   │   ├── Scheme/      ← scheme level: Tag0EYG.lean (`abhyankarLemma_scheme`),
│   │   │   │                   Tag0EYH.lean (`abhyankarLemma_normalization`), charts, descent
│   │   │   └── Strict*, Kummer*, DVR*, StandardCover* ← strict henselization, Kummer theory, 0BRM, 0EYF
│   │   └── Common/          ← shared regularity/normality lemmas (0567, 033C, 0AFS)
│   ├── Palomar/             ← compared statement and `pcfAllTheWayDown_charZero_unconditional`
│   ├── Vendor/              ← vendored Mathlib PR #29802 by Nailin Guan and Yongle Hu (localization of regular local rings)
│   │   └── TauCeti/         ← vendored Tau Ceti modules: finite integral closure of polynomial rings over any field
│   ├── Bounding/            ← thm:bounding DERIVED from purity and Abhyankar (2026-10-04)
│   │   ├── Stacks.lean      ← supporting Tags 036W and 01JT; imports the theorem boundaries above
│   │   ├── StandardPiece.lean ← Step 3 completed: √(aC) = (z), R/(a) → C/(z) bijective
│   │   ├── LocalStructure.lean ← Steps 3–4 glue: going down, components, local ring = A_𝔮
│   │   ├── Pieces.lean      ← finite products: the piece through a point
│   │   ├── Reduced.lean     ← Tag 033B proved (étale over a domain is reduced)
│   │   ├── FiberProduct.lean ← Tag 01JT proved (points of Spec of a tensor product)
│   │   ├── Divisors.lean    ← height-one primes, pushforward, ramification, affine `DivisorDynamics`
│   │   ├── LocalChart.lean   ← two-dimensional stalk chart; regularity promoted and bounding derived
│   │   ├── SchemeBridge.lean ← quotient-stalk coordinates, affine presentations, actual stalk maps
│   │   ├── CriticalLoci.lean ← openness, finiteness, and iterate behavior of actual critical loci
│   │   ├── AffineStalkBridge.lean ← actual `Spec(S/P) → Spec(R/D)` stalk map equals the chart map
│   │   ├── SchemeExtraction.lean ← finite affine preimages; canonical primes and actual-subscheme A6s
│   │   ├── DivisorLift.lean ← `lem:lift`: divisor lying-over and finite fibres for finite maps
│   │   ├── PeriodicLift.lean ← a periodic divisor exists in each finite invariant fibre
│   │   ├── SchemeWiring.lean ← actual divisor `crit₁`; noncircular notMem_nonEtaleBranch_iterate and PCF route
│   │   ├── SchemeDynamics.lean ← actual scheme divisor dynamics and finite-type normalization wiring
│   │   ├── NormalizationRamification.lean ← local algebra for normalization ramification
│   │   ├── NormalizationSchemeBridge.lean ← actual finite-birational stalk square; U1 proved
│   │   ├── GlobalNormalization.lean ← canonical integral birational normalization and lift framework
│   │   ├── GlobalNormalizationComparison.lean ← functorial comparison is an isomorphism
│   │   ├── GlobalNormalizationNormal.lean ← canonical normalization is normal
│   │   ├── GlobalNormalizationFinite.lean ← finite-type normalization is finite in char. zero
│   │   ├── GlobalNormalizationDynamics.lean ← completed finite lifted map and U1--U5 package
│   │   ├── GlobalNormalizationIteration.lean ← lift/iteration compatibility and PCF power invariance
│   │   ├── NormalizationPcfEquiv.lean ← two-way PCF comparison with the canonical normalization
│   │   ├── ReducedFiberBranch.lean ← nonreduced scheme fibres equal ramification-index branch
│   │   ├── CoverDescent.lean ← `lem:covers` for actual finite dominant commuting covers
│   │   ├── InvariantDivisorGeometry.lean ← actual singular/incidence exceptional sets
│   │   ├── PrincipalQuotientRegular.lean ← local regularity from a principal divisor quotient
│   │   ├── FiniteSingularCorrection.lean ← finite Step 0 correction without regular-locus openness
│   │   ├── InvariantDivisorStep0FiniteType.lean ← actual finite-type invariant-divisor theorem
│   │   ├── PcfAllTheWayDownScheme.lean ← scheme-level `thm:general` for a preperiodic divisor
│   │   ├── SchemeAllTheWayDown.lean ← recursive actual-scheme assembly to every finite depth
│   │   ├── DimensionTermination.lean ← strict divisor flags and the `≤ dim X` termination bound
│   │   ├── PcfAllTheWayDownCharZero.lean ← manuscript-facing `cor:pcfawd` from purity and Abhyankar
│   │   ├── AffineBridge.lean ← concrete affine `crit₁`; empty on every bounding chart
│   │   ├── Chart.lean       ← BoundingChart; Steps 1, 2, 3–4, descent
│   │   └── Wiring.lean      ← PCFSetupChart: notMem_nonEtaleBranch_iterate derived, thm:normal-invariant on this route
│   ├── Audit.lean           ← #print axioms for every headline result
│   └── Examples/
│       ├── Squaring.lean    ← ex:squaring, ex:squaring-P2
│       ├── Pinched.lean     ← ex:pinched (ring level + divisorial dynamics on the nodal line)
│       ├── CofiniteWitness.lean ← a complete PCFGeometry with genuine ramification
│       ├── Cusp.lean        ← ex:cusp, ex:branch-singular
│       └── CharP.lean       ← ex:frobenius-line, ex:wild
├── AXIOMS.md                ← axiom census: everything assumed
├── lakefile.toml, lean-toolchain, lake-manifest.json
└── .lake/                   ← build output, never tracked
```

## The design in one paragraph

The manuscript's `sec:prelim` depends on a variety only through the set of its integral
effective divisors ("primes"), their pushforward along `g`, and the ramification index at
each. `Pcf.DivisorDynamics` packages exactly that. The `m`-th iterate `D.iterate m` has `step := stepᵐ`
and `ramificationIdx := ∏_{i<m} ramificationIdx (stepⁱ ·)`, which builds the tower formula of `lem:tower` into the
definition; `prop:iterates` then becomes a theorem about finite products and forward orbits.
`Pcf.UnnormalizedDynamics` adds the two unnormalized critical predicates `crit₀(gᵐ)`, `crit₁(gᵐ)` *as
data indexed by `m`*, because `lem:tower-unnormalized` gives only one-sided inclusions, which
are fields. `Pcf.PCFSetup`/`Pcf.NonEtalePCFSetup` add the data of `thm:normal-invariant` — the
invariant prime `A`, the restricted system, the finite sets `Sing` and `A ∩ E`, and the
conclusion of `thm:bounding` for every iterate. The decisive point, that `Σ` does **not**
depend on `m`, is `Pcf.PCFSetup.branch_iterate_subset_bound` /
`Pcf.NonEtalePCFSetup.nonEtaleBranch_iterate_subset_bound`.

## Statement-to-declaration map

Status words: **proved** (a Lean theorem with the paper's content, on the abstract carrier);
**assumed** (a structure field); **modelled** (a Lean definition standing for a paper
notion, with the identification itself an assumption); **not formalized**.

| `paper.tex` label | Lean declaration | Status |
| --- | --- | --- |
| `def:branch-loci` (1), (2): `branch₀`, `branch₁` | `Pcf.UnnormalizedDynamics.nonUnramifiedLocus/nonEtaleLocus`, `Pcf.UnnormalizedDynamics.nonUnramifiedBranch/nonEtaleBranch` | modelled: `crit_i(gᵐ)` is data indexed by `m`; `branch_i(gᵐ) := gᵐ(crit_i(gᵐ))` |
| `def:branch-loci` (3) = `def:crit-branch`: `branch` | `Pcf.DivisorDynamics.branch`; `Pcf.mem_schemeReducedFiberBranch_iff` | the ramification-index model is identified with the actual nonreduced scheme-fibre locus for finite dominant maps of normal integral schemes |
| `eq:branch-normalization` / `lem:normalization` | `Pcf.schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch`, `Pcf.isNormalizedPCF_iff_normalization` | the literal normalized branch comparison and the two-way PCF equivalence for the actual finite normalization are **proved** |
| `lem:lift` | `Pcf.finiteDominantFiniteType_divisor_lift`; abstract padding `Pcf.DivisorDynamics.IsChain.extend` | for actual finite dominant morphisms of integral schemes with finite-type target, divisor pushforward is **proved** surjective with finite fibres; only ready-made abstract `DivisorDynamics`s retain surjectivity as a field |
| periodic lift in the proof of `thm:general` | `Pcf.exists_periodic_lift_of_surjective_finite_fibers`, `Pcf.NormalizationUnnormalizedDynamics.exists_periodic_lift` | **proved**: a finite nonempty invariant fibre contains a periodic divisor; no injectivity or surjectivity of the fibre endomorphism is assumed |
| `lem:dictionary` | `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx` | one direction proved on `Spec S` (ramified ⟹ non-étale); the converse is assumption A3 |
| `def:pcf` | `Pcf.DivisorDynamics.postcriticalSet`, `Pcf.DivisorDynamics.IsPCF`, `Pcf.DivisorDynamics.isPCF_iff_forall_orbit_finite` | modelled; orbit characterization proved |
| `lem:restriction` | — | not formalized (`step : P → P` presupposes it, assumption A1) |
| `def:pcfawd` | `Pcf.SchemePCFAllTheWayDown`; supporting definitions `Pcf.SchemePCFAllTheWayDownAtDepth`, `Pcf.SchemePCFDescentBranch` | the actual-scheme recursive property is formalized on the actual reduced divisor closures and return maps; actual branches are bounded by `topologicalKrullDim X` |
| `conj:pcfawd` / `cor:pcfawd` | `Pcf.pcfAllTheWayDown_charZero`; supporting theorem `Pcf.schemePCFAllTheWayDown_of_cover_to_dimension` | **proved at scheme level**: `Pcf.pcfAllTheWayDown_charZero` takes the universe-wide purity and Abhyankar statements (`Pcf.PCFAllTheWayDownLocalTheorems`) as hypotheses, and `Pcf.pcfAllTheWayDown_charZero_unconditional` discharges them with the proved theorems; the recursive covering tree and every descendant PCF conclusion are constructed |
| `prop:pcf-equiv` (1)⟺(2) | `Pcf.DivisorDynamics.isPCF_iff_forall_orbit_finite` | proved in the form "every branch prime has *finite orbit*"; the paper's word "preperiodic" (`∃ r s, fʳ⁺ˢ(D) = fʳ(D)`) is not stated, and (3) is not stated |
| `lem:tower` | `Pcf.DivisorDynamics.iterateRamificationIdx_add`, `Pcf.DivisorDynamics.branchIterate_eq`; actual-stalk route `Pcf.schemeDivisorRamificationIdx_comp`, `Pcf.divisorDynamicsOfFiniteDominantNormal_iterateRamificationIdx` | the abstract product identity is proved from the definition; for actual finite dominant normal scheme dynamics, stalk ramification is proved multiplicative and `iterateRamificationIdx` is identified with the actual iterate's ramification index |
| `prop:iterates` (1) | `Pcf.DivisorDynamics.mem_branch_iterate_iff` | proved |
| `prop:iterates` (2) | `Pcf.DivisorDynamics.mem_branch_iterate_succ` | proved |
| `prop:iterates` (3), (4) | `Pcf.DivisorDynamics.postcriticalSet_iterate`, `Pcf.DivisorDynamics.branch_iterate_subset_postcriticalSet`, `Pcf.DivisorDynamics.isPCF_iterate_iff` | proved |
| `lem:normalization` | `Pcf.isNormalizedPCF_iff_normalization` | **proved in both directions** for the actual canonical normalization; the older abstract finite-cover lemma remains as a supporting one-way result |
| `lem:covers` | `Pcf.scheme_isPCF_of_ramified_cover`, `Pcf.scheme_isPCF_of_ramified_cover_charZero`, `Pcf.isNormalizedPCFOfFiniteType_of_cover` | **proved** for actual finite dominant commuting covers, using normalization and ramification-index multiplicativity |
| `lem:finitely-many` | `Pcf.finite_isProperIrreducibleClosed_subset`, `Pcf.PCFGeometry.singularPrimes_finite`, `Pcf.PCFGeometry.meets_finite` | proved on a Noetherian space, for `Pcf.IsProperIrreducibleClosed` (see AXIOMS.md §C on its fidelity) |
| `lem:restriction` / divisor part of `lem:lift` on affine normal schemes | `Pcf.affineDivisorPointEquiv`, `Pcf.height_under_eq_of_finite_of_normal`, `Pcf.affineDivisorUnder`, `Pcf.affineDivisorUnder_surjective` | proved for codimension-one points under the induced finite affine scheme map |
| normalization divisors over a nonnormal finite-type target | `Pcf.height_under_eq_of_finite_of_finiteType`, `Pcf.heightOneUnderOfFiniteType`, `Pcf.coheight_apply_eq_one_of_finiteType`, `Pcf.schemeNormalizationUnnormalizedDynamicsOfFiniteType` | Noether normalization proves codimension preservation; the affine and scheme divisor maps, surjectivity/finite fibers, and actual two-carrier wiring are constructed once the normalization morphism and lifted self-map are supplied |
| canonical global normalization and lifted map | `Pcf.Palomar.normalizationMap`, `schemeGlobalNormalization_isNormal`, `schemeGlobalNormalizationMap_isFinite`, `schemeNormalizationComparison_isIso`, `schemeGlobalNormalizationLift`, `schemeGlobalNormalizationUnnormalizedDynamicsOfFiniteType` | **proved**: the normalization is normal, and finite over any field (`schemeGlobalNormalizationMap_isFinite`, via the vendored Tau Ceti modules); under the manuscript's finite-type characteristic-zero hypotheses the finite dominant lift exists and commutes, and the actual two-carrier divisor/critical-locus package including U1--U5 is constructed |
| ramification and finiteness on affine divisors | `Pcf.heightOnePrime_localRing_isDiscreteValuationRing`, `Pcf.heightOneRamificationIdx`, `Pcf.heightOneRamificationIdx_eq_dvrExponent`, `Pcf.finite_heightOne_ramified`, `Pcf.divisorDynamicsOfFiniteNormalSelfAlgebra` | the height-one local ring is a DVR; the canonical Mathlib index equals its usual maximal-ideal exponent; affine `DivisorDynamics` constructed, assuming generic étaleness |
| concrete affine and scheme-stalk `crit₁` on a bounding chart | `Pcf.affineNonEtaleLocus`, `Pcf.BoundingChart.affineNonEtaleLocus_restriction_eq_empty`, `Pcf.schemeDivisorNonEtaleLocus`, `Pcf.LocalBoundingChart.schemeDivisorNonEtaleLocus_restriction_eq_empty`, `Pcf.SchemeStalkBoundingLocalizationPresentation.formallyEtale`, `Pcf.LocalBoundingChart.toGlobalQuotientSchemeStalkBoundingChartOfFiniteNormalLocalizationOfDivisors` | the critical sets are defined from the actual localized or stalk map; structural localization data and the quotient-ring square yield both coordinate isomorphisms and the arrow comparison; for honest primes `D ≤ q` and `P ≤ Q`, the actual stalk map of `Spec(S/P) → Spec(R/D)` is proved isomorphic to the canonical localized chart and inherits its purity--Abhyankar conclusion; `SchemeStalkBoundingChart.toSchemeStalkBoundingLocalizationPresentation` converts it to the exact interface consumed by the dynamics |
| ambient morphism restricted to closed subschemes | `Scheme.IdealSheafData.quotientAppLE_subschemeMap_eq_quotientMap`, `Pcf.closedSubschemeStalkBoundingLocalizationPresentationOfAmbientMap`, `Pcf.affineIdealSheaf_le_map_of_localBoundingChart`, `Pcf.affineIdealSheafStalkBoundingLocalizationPresentation`, `Pcf.exists_principal_comap_affineBasicOpen_of_atPrime_regular_dim_two` | proved: the induced map on canonical affine quotient charts is the ordinary quotient of the ambient map on sections; on affine ambient schemes the regular local Step 0 hypotheses produce `J(⊤) = (a)`, after which a local bounding chart derives the ideal-sheaf containment, restricted morphism, and complete stalk-localization presentation |
| `thm:bounding`, Step 0 (properness of `Σ`) | `Pcf.BoundingCorrectionLoci.interOther_ne_univ` etc. | **assumed** (P5, P6) |
| `thm:bounding`, on an affine chart (Steps 1–4 and descent) | `Pcf.BoundingChart.isEtaleAt_restriction` | **proved** from the chart data (Step 0's standing hypotheses), `Pcf.Stacks.ZariskiNagataPurity` (0BMB), and `Pcf.Stacks.AbhyankarLemma` (0EYG/0EYH); 033B, the finite-presentation case of 036W, and 01JT are proved (`Pcf.Stacks.isReduced_of_etale_of_isDomain`, `Pcf.Stacks.etaleLocalOnSource`, `Pcf.Stacks.existsPrimeOverBoth`); see AXIOMS.md §G |
| `thm:bounding`, Step 1 | `Pcf.BoundingChart.isEtaleAt_of_notMem` | proved from purity, verifying 0BMB's hypotheses as the manuscript does |
| `thm:bounding`, Step 2 | `Pcf.BoundingChart.exists_standardPieces` | Abhyankar's lemma applied; its premises discharged by the chart and Step 1 |
| `thm:bounding`, Step 3 (`eq:standard-piece`) | `Pcf.LocalModel.restrictionMap_bijective`, `quotientMap_bijective`, `radical_span_algebraMap_eq_span_root` | proved; `√(aC) = (z)` needs `R/(a)` reduced, as in the manuscript |
| `thm:bounding`, Step 3 (dimension count, union of components) | `Pcf.Bounding.mem_minimalPrimes_span_of_mem_minimalPrimes_map`, `exists_mul_mem_ker_of_mem_minimalPrimes_ker` | proved, without dimensions: going down for flat maps and incomparability in quasi-finite fibres |
| `thm:bounding`, Step 4 (`T → D'` étale at `ξ'`) | `Pcf.Bounding.isLocalization_of_localStructure`, `Pcf.BoundingChart.isEtaleAt_quot_of_pieces` | proved: the local ring of the base change is a localization of `R'/(a)` |
| `thm:bounding`, Step 4 (descent, 036W) | `Pcf.Stacks.etaleLocalOnSource` | **proved** in the finite-presentation pointwise form used by the chart, by shrinking the open image to a basic open and descending flatness and formal unramifiedness through a faithfully flat localization |
| `thm:bounding`, étale conclusion for the dynamics | `Pcf.PCFSetupChart.notMem_nonEtaleBranch_iterate`; structural route `Pcf.SchemeNormalizationPCFSetupChart.notMem_nonEtaleBranch_iterate`; completed invariant-divisor route `Pcf.InvariantDivisorSchemeNormalizationPCFSetup.notMem_nonEtaleBranch_iterate` | the legacy abstract route uses circular A6; the structural scheme route fixes `crit₁` to the actual stalk locus; the completed route also identifies the actual invariant-divisor restriction and its iterates and constructs the structural chart from literal Step 0 data, purity and Abhyankar, with no conclusion-shaped field |
| `thm:bounding`, `e > 1` conclusion (`branch(g) ⊆ Σ`) | `Pcf.PCFSetup.notMem_branch_iterate`, via `Pcf.NonEtalePCFSetup.toPCFSetup` | derived from `notMem_nonEtaleBranch_iterate` and `prop:loci-compare`(2) |
| `thm:bounding`, Steps 1–2 inputs | `Pcf.Stacks.ZariskiNagataPurity`, `Pcf.Stacks.AbhyankarLemma`; also the older `Pcf.PurityData.localPurity`, `Pcf.AbstractZariskiNagataPurity` | **proved**: `Pcf.Stacks.zariskiNagataPurity`, `Pcf.Stacks.abhyankarLemma` (the older `Pcf.PurityData.localPurity`, `Pcf.AbstractZariskiNagataPurity` remain hypotheses of the legacy interfaces); local ⟹ global purity is proved (`Pcf.PurityData.codim_eq_one`), as are Tag 0EYF (1)–(2) and Tag 00NP (`Pcf.Vendor.isDomain_of_isRegularLocalRing`) |
| `thm:bounding`, Step 4's final inference | `Pcf.Ramification.ramificationIdx_eq_one_of_bijective` | proved |
| `ex:cusp` | `Pcf.Examples.Cusp.*` | parametrization, Jacobian `2u`, `k[t]` is the normalization, `B ∩ Z = {0}` proved; `branch(g) = ∅` and the new sentence `branch₀(g) = {(0,0)}` **not formalized** |
| `ex:branch-singular` | `Pcf.Examples.Cusp.coneParam`, `coneMap_restrict` | parametrization and restriction proved; normality, étaleness off the vertex, `branch(g) = {o}` not formalized |
| `thm:normal-invariant` (1-PCF) | `Pcf.NonEtalePCFSetup.restriction_isNonEtaleBranchPCF`; `Pcf.PCFSetupChart.restriction_isNonEtaleBranchPCF`; `Pcf.NormalizationPCFSetup.restriction_isNonEtaleBranchPCF`; `Pcf.SchemeNormalizationPCFSetupChart.restriction_isNonEtaleBranchPCF`; `Pcf.InvariantDivisorSchemeNormalizationPCFSetup.restriction_isNonEtaleBranchPCF` | proved from `notMem_nonEtaleBranch_iterate`, `singularPrimes_finite`, `meets_finite`, PCF-ness of `f`; the final route uses the actual invariant-divisor restriction and derives its chart from literal Step 0 data plus G1/G2 |
| `cor:normal-invariant-pcf` | `Pcf.NormalizationPCFSetup.normalized_isPCF`, `Pcf.NormalizationPCFSetupChart.normalized_isPCF`, `Pcf.SchemeNormalizationPCFSetupChart.normalized_isPCF`, `Pcf.InvariantDivisorSchemeNormalizationPCFSetup.normalized_isPCF`; older one-carrier forms `Pcf.NonEtalePCFSetup.restriction_isPCF`, `Pcf.PCFSetup.restriction_isPCF` | the two-carrier theorem transfers finiteness through explicit finite normalization fibers; the final actual-invariant-divisor route constructs the former A6s chart instead of assuming it |
| `cor:normal-preperiodic` | `Pcf.NonEtalePCFSetup.restriction_isNonEtaleBranchPCF_of_iterate`, `Pcf.PCFSetup.restriction_isPCF_of_iterate` | proved in the form "ambient system is `fˢ` and `B` is `fˢ`-invariant"; the reduction `B = fʳ(A)` is left to the supplier of the `PCFSetup` |
| `thm:general` (= `thm:A`) | `Pcf.pcfAllTheWayDown_scheme` | **proved at scheme level** for the manuscript's normalized-PCF definition, conditional only on the standing geometric/PCF hypotheses and the local purity and Abhyankar statements, which are now proved theorems (see `cor:pcfawd`); normality of the ambient scheme is not assumed |
| `cor:pcfawd` | `Pcf.pcfAllTheWayDown_charZero`; supporting declarations `Pcf.schemePCFAllTheWayDownAtDepth_of_cover`, `Pcf.schemePCFAllTheWayDown_of_cover_to_dimension` | the characteristic-zero theorem has the manuscript's geometric and PCF hypotheses plus only universal purity and Abhyankar, which `Pcf.pcfAllTheWayDown_charZero_unconditional` discharges; recursive actual-scheme assembly and the numerical `≤ topologicalKrullDim X` termination bound are proved |
| `def:pcf-unnormalized` | `Pcf.NormalizationUnnormalizedDynamics.nonUnramifiedPostcriticalSet/nonEtalePostcriticalSet`, `Pcf.NormalizationUnnormalizedDynamics.IsNonUnramifiedBranchPCF/IsNonEtaleBranchPCF`; legacy `Pcf.UnnormalizedDynamics` | modelled on the corrected two-carrier abstraction; the legacy one-carrier type embeds by the identity normalization map |
| `prop:loci-compare` (1) | `Pcf.UnnormalizedDynamics.nonEtaleLocus_finite`; actual route `Pcf.SchemeNormalizationUnnormalizedDynamics.nonEtaleLocus_finite` | **assumed** on legacy abstract interfaces; **proved on the actual-scheme route** from finite dominance, local finite presentation, integrality, Noetherianity, and characteristic zero at the generic stalk; generic formal étaleness is derived |
| `prop:loci-compare` (2) | `mem_nonUnramifiedLocus_of_one_lt_ramificationIdx`, `nonUnramifiedLocus_subset_nonEtaleLocus` and their branch/PC consequences | U1 remains a field of abstract/generic interfaces but is **proved for actual finite birational normalizations** by `mem_schemeDivisorNonUnramifiedLocus_of_one_lt_ramificationIdx_of_birational`; U2 is proved from the actual stalk maps. The consequences for `branch`, `PC` and `i`-PCF are proved. |
| `prop:loci-compare` (3) | — | not formalized |
| `lem:tower-unnormalized` (1), (2) | actual route `Pcf.schemeDivisorNonUnramifiedLocus_tower`, `Pcf.schemeDivisorNonEtaleLocus_tower` | the pointwise U4/U5 implications used downstream are **proved from actual stalk maps**; legacy interfaces still store them, and the general composite branch-locus clauses are not stated |
| `cor:orbit-unnormalized` | `Pcf.UnnormalizedDynamics.orbit_unnormalized_zero`, `orbit_unnormalized_one`, `orbit_unnormalized_one_of_mem` | proved (for all `n ≥ 0`) |
| `ex:pinched`, `f̃*R ⊆ R` | `Pcf.Examples.Pinched.squaringMap_mem_of_mem` (indeed `squaringMap_mem` for all `h`) | proved, any commutative ring |
| `ex:pinched`, `R = k[w, z², z(w−1), z³−4z]` | `Pcf.Examples.Pinched.adjoin_pinchedGenerators_eq` | proved, `k` a field of characteristic zero (uses only `4 ≠ 0`) |
| `ex:pinched`, `R_B` closed under `p ↦ p(z²)` | `Pcf.Examples.Pinched.comp_sq_mem` | proved |
| `ex:pinched`, orbit `4, 16, 256, …` distinct | `Pcf.Examples.Pinched.squaringOrbit_injective`, `point_four_pow_injective` | proved |
| `ex:pinched`, `g` PCF | `Pcf.Examples.Pinched.nodeDivisorDynamics_isPCF` (`PC(g) = {0}`) | proved on the modelled system `nodeDivisorDynamics` (`k` algebraically closed, char. 0) |
| `ex:pinched`, `g` not `0`-PCF, not `1`-PCF | `Pcf.Examples.Pinched.nonUnramifiedPostcriticalSet_infinite`, `nonEtalePostcriticalSet_infinite`; instance `nodeUnnormalizedDynamics_not_isNonUnramifiedBranchPCF/1` | proved **given `o ∈ crit₀(g)`** as a hypothesis (or stipulated in the instance); the fibre-length computation is **not formalized** |
| `ex:pinched`, pushout, variety, normalization, finiteness of `f`, `f` not flat at `o`, `PC(f)` | — | not formalized |
| `ex:squaring` | `Pcf.Examples.squaringProjectiveLine` | proved on the modelled system |
| `ex:squaring-P2` | `Pcf.Examples.diagonalSquaring` | proved on a reduced ambient model (see that file's caveat); `notMem_branch_iterate` **proved** there, so `PCFSetup` is inhabited |
| `ex:wild` | `Pcf.Examples.CharP.orbit_infinite` | the critical orbit of `h(t) = t^{p+1} + c` is infinite: proved; the geometry of `F` not formalized |
| `ex:frobenius-line` | `Pcf.Examples.CharP.restriction_eq_frobenius`, `derivative_charPoly_ne_zero` | concrete identities proved; "index one but not étale" not formalized |
| `thm:purity` (Stacks 0BMB) | `Pcf.Stacks.ZariskiNagataPurity`, with pointwise inputs `Pcf.Stacks.ZariskiNagataPurityHypothesesAt` and conclusion `Pcf.Stacks.HasZariskiNagataPurityAt`; `Pcf.AbstractZariskiNagataPurity`, `Pcf.PurityData.localPurity` are older restatements | **proved**: `Pcf.Stacks.zariskiNagataPurity` (affine), `Pcf.Stacks.isStacksEtaleAt_of_zariskiNagataPurity` and `Pcf.Stacks.exists_etale_of_zariskiNagataPurity` (scheme level); faithful to the tag (AXIOMS.md, first section and §G) |
| `thm:abhyankar` (Stacks 0EYG + 0EYH) | `Pcf.Stacks.AbhyankarLemma`, with conclusion `Pcf.Stacks.HasAbhyankarStandardCoverAt` and standard-cover product `Pcf.Stacks.IsFiniteDisjointUnionOfStandardTameCovers` | **proved**: `Pcf.Stacks.abhyankarLemma`, weaker than the tags (characteristic zero in place of tameness; units `uᵢ` allowed; points of `D` only); the tame form `Pcf.Stacks.abhyankarLemmaTame` (`Pcf.Stacks.AbhyankarLemmaTame`); scheme level `Pcf.Stacks.SchemeLevel.abhyankarLemma_scheme` (0EYG as stated) and `Pcf.Stacks.SchemeLevel.abhyankarLemma_normalization` (0EYH, finite locally free as finite + flat + locally of finite presentation) |
| Stacks 00NP | `Pcf.Vendor.isDomain_of_isRegularLocalRing` (vendored mathlib4 PR #29802) | **proved** by dimension induction, prime avoidance and Nakayama; this removes the former local-domain clause from `Pcf.Stacks.AbhyankarLemma` |
| `lem:jacobian`, `ex:basilica`, `ex:dupont`, `ex:loci-compared`, `rem:why-normalized`, `q:singularPrimes-B` | — | not formalized |

## Building

```sh
elan toolchain install $(cat lean-toolchain)     # first time only
lake exe cache get                               # Mathlib olean cache
lake build
```

`lake build` builds every module listed above; `lake env lean Pcf/<File>.lean`
checks a single file in a few seconds.
