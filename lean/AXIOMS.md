# AXIOMS.md — assumed inputs of the Lean formalization

| Field | Value |
| --- | --- |
| Repo | `pcf` |
| Scope | `lean/` |
| Status | Draft |
| Date | `2026-09-21`; amended through the scheme-level general theorem on `2026-10-07`; purity and Abhyankar proved `2026-10-16` (see the first section); phase-2 Stacks-form statements `2026-10-17` |
| Manuscript | `latex/paper.tex`, cited by `\label` (the file was `pcf.tex` with different numbering when this census was first written) |
| Toolchain | Lean `4.35.0`, Mathlib `v4.35.0` (`56a005855ea1`) since 2026-10-15 (was Lean `4.34.0`, Mathlib `5ed296525643`) |

This is the *axiom census* of the formalization, in the sense used by the
`gq2` project.  The abstract compatibility layers remain deliberately
conditional.  The headline actual-scheme theorem constructs those layers and
leaves only the local purity and Abhyankar packages as mathematical
inputs beyond its stated geometric and PCF hypotheses.

## 2026-10-16: purity and Abhyankar are proved; the headline assumes nothing further

The two local literature inputs listed below as the "only literature packages" are no longer
assumed. Both are theorems, quantified over all rings of the working universe exactly as the
inputs of `Pcf.PCFAllTheWayDownLocalTheorems` and of the compared Palomar statement:

| Input | Theorem | File | `#print axioms` |
| --- | --- | --- | --- |
| Zariski--Nagata purity, Stacks `0BMB` (affine pointwise form) | `Pcf.Stacks.zariskiNagataPurity : ∀ R S, Pcf.Stacks.ZariskiNagataPurity R S`; Palomar form `Pcf.Palomar.zariskiNagataPurity` | `Pcf/Stacks/Purity/Tag0BMA.lean` | `[propext, Classical.choice, Quot.sound]` |
| Abhyankar's lemma for a regular divisor, Stacks `0EYG`/`0EYH` (all positive integers invertible) | `Pcf.Stacks.abhyankarLemma : ∀ R S a, Pcf.Stacks.AbhyankarLemma R S a`; Palomar form `Pcf.Palomar.abhyankarLemma` | `Pcf/Stacks/Abhyankar/FiniteNormalization.lean` (phase 3; previously `Tag0EYG.lean`, now `abhyankarLemmaOfFinite`) | `[propext, Classical.choice, Quot.sound]` |

The headline theorems with these inputs discharged are in `Pcf/Palomar/Unconditional.lean`:

* `Pcf.pcfAllTheWayDown_charZero_unconditional` (development statement);
* `Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional` (the compared statement of
  `Pcf.Palomar.pcfAllTheWayDown_charZero` with its `purity` and `abhyankar` binders removed).

Both report `[propext, Classical.choice, Quot.sound]`. **For these theorems nothing is assumed
beyond the standard axioms and the hypotheses printed in their statements** (characteristic-zero
field, integral locally Noetherian scheme locally of finite type with Noetherian underlying
space, finite dominant self-map, normalized PCF). The statements of `ZariskiNagataPurity` and
`AbhyankarLemma` were not changed in this run. The conditional theorems and the structure
`PCFAllTheWayDownLocalTheorems` remain, unchanged, so the older sections of this file still
describe them correctly; they are now history for the headline. The modelling assumptions of §A
and the abstract-layer fields of §B concern the legacy abstract interfaces, not the headline.

The proofs were written in the run recorded in
the authors' private research note `2026-10-16-purity-abhyankar-completion/` (`FRAME.md`, `PLAN.md`, `STATUS.md`). Mathlib PR
#29802 (Auslander--Buchsbaum--Serre, localization of regular local rings) is vendored, renamed,
under `Pcf/Vendor/RegularLocalization/` and used through `Pcf/Stacks/Common/RegularLocalization.lean`
(Stacks `0AFS`).

### Proof routes that diverge from Stacks

Statements carry `@[stacks]` only where they are the tag's result (with a restriction comment
where they are a clause or case). The following proof routes differ from the Stacks proofs; each
is recorded in the declaration's docstring.

* `0BMA` (`Tag0BMA.lean`): the induction runs over complete regular local rings, and the
  local-cohomology argument of `0BM6`/`0EKS` behind `0BLM` is replaced by an elementary formal
  lifting (`HypersurfaceLiftingComplete.lean`, `FormalEtaleLift.lean`); `0BLM` is proved only in
  the complete regular local case, which is all the induction uses. The passage from `A` to
  `A^∧` replaces `0BLL`/`0BLH` by Hartogs for a regular pair plus fpqc descent of étaleness
  (`CompletionDescent.lean`). The statement proved is clause (2) in the finite-normal form
  `FiniteNormalPuncturedEtalePurity` (finite, torsion-free, Stacks-normal); the torsion-free
  hypothesis is a necessary repair (**divergence from Stacks**): Stacks' literal clause (2) says
  any finite `A → B` with `B` normal inducing a finite étale morphism on punctured spectra is
  étale, which is false as stated, since `B = A × κ(𝔪)` is finite and normal (a product of
  normal domains) and, its `κ(𝔪)` factor lying over the closed point, restricts to `U → U` on the
  punctured spectrum (étale), but is not flat over `A` (`κ(𝔪)` is not flat as `dim A ≥ 2`),
  hence not étale. The Lean statement adds "`B` torsion-free over `A`" (equivalently, no
  component of `Spec B` lies over the closed point), which is exactly what Stacks' proof uses.
  Proof fidelity: the phase-1 proof of `0BMA` does not follow the Stacks proof (see above); that of
  `0BMB` follows it only up to its `0BMA` input.
  Erratum drafted in the authors' private research note `2026-10-16-purity-abhyankar-completion/ERRATUM-0BMA.md`.
* `09ZL` (`HenselianFiniteEtaleLift.lean`): only essential surjectivity, for henselian local
  rings, by induction on the rank via idempotent lifting and characteristic polynomials, instead
  of lifting to an étale algebra and cutting out a direct factor.
* `0567` (`Common/RegularNormal.lean`): regular implies normal without Serre's criterion
  `031S` or the Ext-theoretic depth API: an associated-prime argument reduces to regular local
  rings of dimension one (DVRs), using `00NP` and regularity of localizations (`0AFS`).
* `033C` (`Common/EtaleNormal.lean`): pointwise form (normality needed only at the image point).
* `0BMB` (`Tag0BMB.lean`, `Tag0BMBLocalModel.lean`): strong induction on the height as in Stacks;
  the final descent is done on local rings (Kähler differentials, Tor-free tensor products)
  rather than with `02VN` on schemes.
* `06LJ` (`StrictHenselizationCompletionFlat.lean`): the stages of the colimit are not
  identified with strict henselizations of themselves.
* `04GW` (`StrictHenselizationLocalize.lean`): the comparison is between pcf's colimit models at
  `R → Ω` with kernel `p` and at `R_p`.
* `0EYG`/`0EYH` (`Tag0EYG.lean`, `StrictGenericPresentation.lean`): the strict henselization of
  `R` is compared with that of `R_y` (`04GW`), and the normalization step is done on integral
  models (both are the integral closure of `A` in `K(a^{1/n})`), giving the `0EYH` form
  directly. Any common multiple `E` of the ramification indices is used instead of their
  product; `0BRM` is proved in the divisibility form `e ∣ E` without finiteness of the upper DVR
  (`DVRAbhyankarDivisible.lean`); henselianity of the root cover is replaced by the two
  consequences used (`StrictRootCover.lean`); Stacks' decomposition of `B` over `A_f` is done on
  the integral model (`StrictNormalDecomposition.lean`, `StrictRootComponent.lean`); Stacks'
  final step (the exponent is a unit) is not needed, since every positive integer is invertible.
  (Since phase 3 these differences are recorded at the shared lemmas, see `Tame/Defs.lean`,
  "Shared lemmas", and the module docstring of `Tame/Tag0EYGTame.lean`.)

### Phase 2 (2026-10-17): Stacks-form statements

Additional theorems; at the time of phase 2 nothing above was changed or re-proved (phase 3,
below, later changed the statement `Pcf.Stacks.AbhyankarLemma` and merged the two `0EYG`
proofs). Run record:
the authors' private research note `2026-10-16-purity-abhyankar-completion/` (`FRAME-PHASE2.md`, `STATUS.md`).

| Claim | Theorem | File | `#print axioms` |
| --- | --- | --- | --- |
| Purity of branch locus, Stacks `0BMB`, scheme-level pointwise (literal Stacks pointwise notions) | `Pcf.Stacks.isStacksEtaleAt_of_zariskiNagataPurity` | `Pcf/Stacks/Purity/Tag0BMBScheme.lean` | `[propext, Classical.choice, Quot.sound]` |
| The same in Mathlib vocabulary (`Etale` on an open neighbourhood) | `Pcf.Stacks.exists_etale_of_zariskiNagataPurity` | `Pcf/Stacks/Purity/Tag0BMBSchemeAPI.lean` | `[propext, Classical.choice, Quot.sound]` |
| Abhyankar for a regular divisor, tamely ramified in codimension 1, any characteristic, affine (`0EYG`/`0EYH`) | `Pcf.Stacks.abhyankarLemmaTame : ∀ R S a, Pcf.Stacks.AbhyankarLemmaTame R S a` | `Pcf/Stacks/Abhyankar/FiniteNormalization.lean` (phase 3; previously `Tame/Tag0EYGTame.lean`, now `abhyankarLemmaTameOfFinite`) | `[propext, Classical.choice, Quot.sound]` |
| Stacks `0EYG` (Lemma 58.31.5), scheme level, as stated | `Pcf.Stacks.SchemeLevel.abhyankarLemma_scheme` | `Pcf/Stacks/Abhyankar/Scheme/Tag0EYG.lean` | `[propext, Classical.choice, Quot.sound]` |
| Stacks `0EYH` (Lemma 58.31.6), scheme level, as stated ("finite locally free" written as finite, flat, locally of finite presentation, Tag `02KB`) | `Pcf.Stacks.SchemeLevel.abhyankarLemma_normalization` | `Pcf/Stacks/Abhyankar/Scheme/Tag0EYH.lean` | `[propext, Classical.choice, Quot.sound]` |

Route divergences (each described in the docstring at the declaration):

* `0BMB` scheme form: reduced Zariski-locally to the affine `Pcf.Stacks.zariskiNagataPurity`
  instead of Stacks' étale-local induction on schemes (docstring of
  `isStacksEtaleAt_of_zariskiNagataPurity`).
* `0EYG` tame affine: the phase-1 route (`04GW` comparison, integral models giving the `0EYH`
  form) with `0EYD` proved by comparing ramification indices along the ind-étale base change
  (module docstring of `Tame/Tag0EYGTame.lean`, `Tame/Defs.lean`).
* `0EYG` scheme level: Stacks' affine step takes the cover `B`; here the affine theorem takes the
  normalization, applied at the local rings `A_y` of a chart (module docstring of
  `Scheme/Tag0EYG.lean`).
* `0EYH` scheme level: the étale-local facts are descended explicitly on affine charts
  (faithfully flat descent of finiteness and flatness, descent of principality and regularity),
  which Stacks leaves implicit (module docstring of `Scheme/Tag0EYH.lean`).

### Phase 3 (2026-10-17): the normalization is proved finite

`Module.Finite R S` (the normalization `S` finite over `R`) is no longer a hypothesis of
`Pcf.Stacks.AbhyankarLemma` or `Pcf.Stacks.AbhyankarLemmaTame`.  It is replaced by the hypothesis
of Stacks `0EYG` itself, `Y = Spec S[1/a] → X ∖ D` finite: `Module.Finite R[1/a] (R[1/a] ⊗_R S)`.
The finiteness of `S` (first assertion of `0EYH`) is proved:

| Claim | Theorem | File | `#print axioms` |
| --- | --- | --- | --- |
| The normalization is finite, tame case (`0EYH`, first assertion, affine) | `Pcf.Stacks.finite_of_isIntegralClosure_away` | `Pcf/Stacks/Abhyankar/FiniteNormalization.lean` | `[propext, Classical.choice, Quot.sound]` |
| The same, every positive integer invertible (no tameness hypothesis) | `Pcf.Stacks.finite_of_isIntegralClosure_away_of_isUnit_natCast` | same | `[propext, Classical.choice, Quot.sound]` |
| `0EYG`/`0EYH` affine, normalization not assumed finite | `Pcf.Stacks.abhyankarLemma`, `Pcf.Stacks.abhyankarLemmaTame` | same | `[propext, Classical.choice, Quot.sound]` |

The previous statements are kept as `Pcf.Stacks.AbhyankarLemmaOfFinite` and
`Pcf.Stacks.AbhyankarLemmaTameOfFinite`, proved by `Pcf.Stacks.abhyankarLemmaOfFinite`
(`Tag0EYG.lean`) and `Pcf.Stacks.abhyankarLemmaTameOfFinite` (`Tame/Tag0EYGTame.lean`); the
scheme layer applies them at local rings.  The Palomar statement `Pcf.Palomar.AbhyankarLemma`
still assumes the normalization finite (it is `AbhyankarLemmaOfFinite`); `Pcf.Palomar.abhyankarLemma_iff`
now proves its equivalence with `Pcf.Stacks.AbhyankarLemma` using the finiteness theorem, and the
headline statements are unchanged.

The two `0EYG` proofs are now one: `Pcf.Stacks.abhyankarLemmaOfFinite` supplies tameness from
"every positive integer is invertible" (`isTamelyRamifiedInCodimensionOneAlong_of_isUnit_natCast`)
and applies `hasAbhyankarStandardCoverAt_of_mem_divisor_of_tame`; each of the 16 former
characteristic-zero/tame lemma pairs has one proof (map in `Tame/Defs.lean`, "Shared lemmas"), and
the six `Tame/` files that held the tame duplicates were deleted.  So the characteristic-zero
results, including `finite_of_isIntegralClosure_away_of_isUnit_natCast` and the PCFAWD headline,
now go through the tame proof; their statements are unchanged.  The former consistency check
`Pcf.Stacks.abhyankarLemma_of_tame` (same statement and route as `abhyankarLemmaOfFinite`) was
removed.

`Module.Finite R S` could not simply be dropped: pcf's `Algebra.IsEtaleAt` is formal étaleness of
the local rings and does not give finite type.  For `R = ℚ[t]_{(t)}`, `a = t`, and `S` the integral
closure of `R` in `ℚ(ζ_{ℓ^∞})(t)`, every other hypothesis holds and `S` is not finite over `R`; the
conclusion would make `S` finite by faithfully flat descent, so the statement would be false.

Route: `S[1/a]` is finite étale over `R[1/a]` (`etale_away`); the tameness of `S` is read on the
chart `Spec S[1/a] → Spec R[1/a]` (`isTamelyRamifiedAlongDivisor_of_isTamelyRamifiedInCodimensionOneAlong`, via the
localization invariance of tameness, `isTamelyRamifiedAt_map_of_isLocalization`); then the
scheme layer's `hasLocalizedStandardCoverAt_of_tame` and `integralClosure_finite` give the
normalization finite, as in the Stacks proof of `0EYH` (étale-local structure from `0EYG`).

## How to read `#print axioms` here

`#print axioms` on every theorem in this development reports only the standard
logical axioms `propext`, `Classical.choice`, `Quot.sound`. **That is not a
claim that nothing is assumed.** The assumed mathematics enters as *fields of
structures* (`Pcf.DivisorDynamics`, `Pcf.PCFSetup`), i.e. as hypotheses, not as Lean
`axiom` declarations — so it is invisible to `#print axioms` by construction.
A theorem of the form `theorem t (h : P) : Q` has no axioms and still proves
only `P → Q`.

There is no `sorry`, no `axiom`, no `admit` and no `native_decide` anywhere in
`lean/Pcf/`. The conditionality is entirely in the list below.

## Current boundary of the scheme-level theorem

`Pcf.pcfAllTheWayDown_scheme` formalizes the one-divisor statement of
`thm:general`, while `Pcf.pcfAllTheWayDown_charZero` formalizes the recursive
conclusion `cor:pcfawd`.  Its explicit non-literature hypotheses are the ordinary data of
the theorem: a characteristic-zero field, an integral locally Noetherian scheme
locally of finite type over that field with Noetherian underlying space, a finite
dominant self-map, a codimension-one point with a stated preperiodicity relation,
and normalized PCF of the ambient map.  Normality of the ambient scheme is not
assumed.

Its only literature packages are required on every relevant affine chart and
iterate of the canonical normalization:

* `Stacks.ZariskiNagataPurity`, the 0BMB implication with its five pointwise geometric
  hypotheses named by `Stacks.ZariskiNagataPurityHypothesesAt` and its local conclusion named
  by `Stacks.HasZariskiNagataPurityAt`; and
* `Stacks.AbhyankarLemma`, the 0EYG/0EYH local standard-form conclusion, now named
  explicitly as `Stacks.HasAbhyankarStandardCoverAt`; its finite disjoint union is the
  ring-product predicate `Stacks.IsFiniteDisjointUnionOfStandardTameCovers`.

For the final theorem these are quantified once, for all rings in the working
universe, by `Pcf.PCFAllTheWayDownLocalTheorems`.  The theorem
`Pcf.schemePCFCoveringAtDepthOfLocalTheorems` constructs the complete recursive
covering tree from those two fields.  Thus `Pcf.pcfAllTheWayDown_charZero` has no
caller-supplied descendant PCF claim, local chart, or recursively prepared tree.

The formerly adjoined local-domain clause is now derived from the proved theorem
`Pcf.Stacks.isDomain_of_isRegularLocalRing` (Stacks Tag 00NP).

Everything else used by the proof is constructed: divisor pushforward and
finite fibres, ramification indices and their tower law, critical-locus
finiteness and U1--U5, the canonical finite normal normalization and commuting
lift, two-way normalized-PCF comparison, periodic lifting, finite singular
correction, and PCF descent through a finite dominant commuting cover.  No A6 or
A6s conclusion-shaped chart field occurs in the theorem.  The scheme-level
recursive assembly of `cor:pcfawd` is packaged by
`Pcf.pcfAllTheWayDown_charZero`, and the reduced-fibre definition of the branch
locus is identified with the ramification-index definition by
`Pcf.schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch`.

## A. Modelling assumptions (the abstraction itself)

The manuscript is scheme-theoretic. Mathlib has no complete theory of normal varieties,
normalization, branch divisors, Zariski–Nagata purity or Abhyankar's lemma.  The development
now constructs a `DivisorDynamics` from a finite normal affine ring self-map and from an actual
finite dominant normal scheme self-map. On the completed
invariant-divisor route it also starts from an actual finite dominant scheme endomorphism,
restricts it to the reduced closure of an invariant divisor, identifies all iterates, and
constructs the Step 0 stalk charts. The remaining ordinary dynamical/properness facts are
explicit structure fields. The critical locus is fixed definitionally from stalk maps;
no field contains A6's conclusion-equivalent implication.

| ID | Assumption | Manuscript source |
| --- | --- | --- |
| A1 | The primes of the normalized model of a variety form a type `P`, and a finite dominant self-map induces a *function* `step : P → P` (image of a prime is a prime). **Proved:** `affineDivisorUnder` and `divisorDynamicsOfFiniteDominantNormal` handle normal schemes; `height_under_eq_of_finite_of_finiteType` and `finiteDominantFiniteType_divisor_lift` handle divisors on nonnormal finite-type targets. The `GlobalNormalization*.lean` modules construct the canonical finite normal birational normalization and its finite dominant commuting lift, and `schemeGlobalNormalizationUnnormalizedDynamicsOfFiniteType` assembles the actual divisor maps, finite fibres, commuting square and U1--U5. Only abstract ready-made interfaces retain this as data. | §`sec:intro` Conventions |
| A2 | Ramification indices are captured by a function `ram : P → ℕ` with `ram P' = e(P'/g(P'))`, positive everywhere. **Constructed affinely and on actual schemes** as `heightOneRamificationIdx` and `schemeDivisorRamificationIdx`, with positivity proved. Codimension-one stalks of normal locally Noetherian integral schemes are proved to be DVRs. | the ramification paragraph before Definition `def:crit-branch` |
| A3 | Branching is modelled by `1 < ram`, i.e. by `e > 1` alone. **The affine ramified divisor set is proved finite** by `finite_heightOne_ramified`, and the index has the expected DVR meaning by `heightOneRamificationIdx_eq_dvrExponent`. the ramification paragraph before Definition `def:crit-branch`'s second clause (inseparable residue extension) is **not** modelled. | the ramification paragraph before Definition `def:crit-branch`, Definition `def:crit-branch` and Lemma `lem:dictionary` |
| A4 | The ramification index of the `m`-th iterate equals `∏_{i<m} ram (stepⁱ ·)`. `DivisorDynamics.iterateRamificationIdx` is defined by this product. `heightOneRamificationIdx_tower` proves the affine tower identity, `schemeDivisorRamificationIdx_comp` proves the stalk identity under finite dominant normal geometry, and `divisorDynamicsOfFiniteDominantNormal_iterateRamificationIdx` identifies the product with the actual scheme iterate's stalk index. | §`sec:prelim`, proof of Proposition `prop:iterates`(1) |
| A5 | On legacy abstract interfaces, the geometric objects `Sing(X)`, `Sing(A)` and `A ∩ E` are represented by sets of primes (`PCFSetup.singularPrimes`, `PCFSetup.meets`). On the actual finite-type invariant-divisor route, `InvariantDivisorGeometry.lean` constructs the incidence and singular sets and `invariantDivisorSing_finite_of_perfectField` proves the required finite correction from generic smoothness and local principal generation. | Theorem `thm:bounding` |
| A6 | **The chart link** (`Pcf.PCFSetupChart.chart`, §G.4). For every `m ≥ 1`, every prime `Q` of `A` outside `Σₘ` and every `Q'` with `gᵐ(Q') = Q`, there is an affine chart of `fᵐ` around `Q` (a `Pcf.BoundingChart`) with a point `ξ` representing `Q'`, such that `Q' ∈ crit₁(gᵐ)` implies the chart's restriction `R/(a) → S/𝔭` is not étale at `ξ`. This identifies the abstract predicate `crit₁` with non-étaleness computed on charts, and encodes Step 0's choice of `U` avoiding `Σ`. Relative to the derived theorem it is exactly as strong as `notMem_nonEtaleBranch_iterate`; see §G.4. | Theorem `thm:bounding`, Step 0 and Step 4; Definition `def:branch-loci` |

The preferred replacement for the legacy A6 row is:

| ID | Structural input | Manuscript source |
| --- | --- | --- |
| A6s | **Legacy structural stalk-chart input** (`Pcf.SchemeNormalizationPCFSetupChart.chart`, §G.4). Its supplied `SchemeStalkBoundingLocalizationPresentation` contains only local algebra, canonical maps to actual stalks, localization properties, and a commutative square; all coordinate/arrow comparisons and formal étaleness are theorems. It is not conclusion-equivalent, but callers of this generic interface still supply it. | Theorem `thm:bounding`, Steps 0--4; Definition `def:branch-loci` |
| A6i | **Literal invariant-divisor Step 0 interface** (`Pcf.InvariantDivisorCorrectionLocalData`). For the actual finite dominant endomorphism, invariant divisor, iterate and specified preimage, it records an affine neighborhood, characteristic zero, source/target incidence, ambient codimension two, regularity away from the finite correction, avoidance of every other height-one branch component, and G1/G2. It contains no chart, formal-étaleness assertion, `crit₁`, `notMem_nonEtaleBranch_iterate`, or bounding conclusion. `invariantDivisorSetupOfFiniteType` constructs this interface from the actual finite-type geometry plus only the local G1/G2 packages; no caller of `pcfAllTheWayDown_scheme` supplies A6i. | Theorem `thm:bounding`, Step 0; G1/G2 in Steps 1--2 |

**Consequence.** A3 restricts the development to the characteristic-zero
setting of Theorem `thm:normal-invariant`, where non-étaleness at a source DVR is exactly `e > 1`.
Example `ex:wild` shows that the wild positive-characteristic statement is false, so
nothing is lost for Theorem `thm:normal-invariant` and nothing is claimed beyond it.

## B. Assumed theorems (the interfaces to the literature)

The development has **two layers**, and it matters which one a statement lives in.

* The **abstract layer** (`Pcf/Dynamics.lean`, `Pcf/Restriction.lean`) proves Theorem `thm:normal-invariant`
  from structure fields. It is what §C below describes.
* The **geometric layer** (`Pcf/Noetherian.lean`, `Pcf/Purity.lean`,
  `Pcf/Ramification.lean`, `Pcf/LocalModel.lean`, `Pcf/Geometry.lean`) proves
  Theorem `thm:bounding` and the finiteness statements outright, from strictly smaller inputs.

The two layers **are now joined**. `Pcf.PCFGeometry.toPCFSetup` constructs a
`Pcf.PCFSetup` from geometric data with `singularPrimes_finite`, `meets_finite` and `key` **proved**,
and `Pcf.PCFGeometry.restriction_isPCF` is Theorem `thm:normal-invariant` on that route. `Pcf.divisorDynamicsOfGeometry` likewise
constructs a `Pcf.DivisorDynamics` with `step_image_ramified_finite` proved.

So there are three routes to Theorem `thm:normal-invariant`:

* **Abstract route** — `Pcf.PCFSetup.restriction_isPCF` on a hand-built `PCFSetup`. Assumes B1–B5.
* **Geometric route** — `Pcf.PCFGeometry.restriction_isPCF`. Assumes B1 and B2 (they are fields of
  the two `DivisorDynamics`s inside `PCFGeometry`, so they must be supplied twice), P3–P6, and the
  bounding conclusion `key` as an **explicit argument** (since 2026-10-04; it was the field
  P2, equivalent to B5 — see the warning below). What it genuinely no longer assumes is B3
  and B4.
* **Chart route** (2026-10-04, §G) — `Pcf.PCFSetupChart.restriction_isNonEtaleBranchPCF`. Assumes B1, B2, B3, B4,
  U1–U5, the chart link A6, and **derives** B5/U6 from Zariski–Nagata purity (G1),
  Abhyankar's lemma (G2), both stated faithfully to the Stacks text. Tags 033B, the needed
  finite-presentation case of 036W, and 01JT are proved (G3–G5).
* **Two-carrier chart route** (2026-10-05) —
  `Pcf.NormalizationPCFSetupChart.normalized_isPCF`.  It has the same chart assumptions, but
  `NormalizationUnnormalizedDynamics` keeps divisors of the normalization separate from divisors of
  the possibly nonnormal restriction.  The final PCF transfer is proved from finite fibers;
  it no longer assumes or suggests that the two carriers are definitionally identical.
* **Actual-scheme chart route** (2026-10-05) —
  `Pcf.SchemeNormalizationPCFSetupChart.normalized_isPCF`. Its divisor carrier is
  `SchemeDivisorPoint A`, and `Pcf.SchemeNormalizationUnnormalizedDynamics` defines every
  `crit₀(gᵐ)` and `crit₁(gᵐ)` from the actual stalk map. Its generic structure stores U1,
  but `schemeNormalizationUnnormalizedDynamicsOfFiniteBirational` proves U1 from the actual finite
  commuting maps and generic-stalk birationality. It assumes the structural chart input
  A6s, but not A6's implication; U2–U5 are proved. `notMem_nonEtaleBranch_iterate` is proved by deriving formal étaleness of
  the localized quotient map and transporting it across the derived arrow isomorphism
  supplied by the quotient-ring algebra maps, their localization properties, and their
  commutative square; the coordinate isomorphisms are derived.
* **Actual invariant-divisor route** (2026-10-05) —
  `Pcf.InvariantDivisorSchemeNormalizationPCFSetup.normalized_isPCF`. It starts with an actual
  finite dominant endomorphism and invariant codimension-one point, identifies the
  restricted self-map and every iterate with the canonical reduced point-closure map,
  and constructs the A6s chart from A6i. Its only unproved local covering theorems are G1
  and G2; the remaining A6i fields are the literal Step 0 hypotheses and incidences, not
  a reformulation of formal étaleness or the conclusion. The constructor
  `InvariantDivisorSchemeNormalizationPCFSetup.ofActualAmbient` forces its ambient
  dynamics and fixed prime to come from the actual endomorphism and invariant divisor.

**A correction, retained.** An earlier version of this file claimed Theorem `thm:bounding` (per-divisor form) is
*proved* from purity and Abhyankar's lemma. It was not.
`Pcf.nonempty_unramifiedWitness_iff` proves that the interface then in use,
`UnramifiedWitness n`, is inhabited exactly when `n = 1`, and that an inhabitant can be
taken to be the identity map `ℤ → ℤ`, with no geometry in it at all. So that interface
carried exactly the conclusion of Theorem `thm:bounding` (per-divisor form), and the step to `notMem_branch` was
a one-line repackaging. The correction was produced by an adversarial review of the
development, retained at the authors' private research note `2026-09-21-prop41-formalization/adversarial-review.md`.

**What has since changed, and what has not.** Abhyankar's lemma has two halves, and one
of them is now machine-checked:

* **Assumed** (P2, Stacks Tag 0EYG) — the cover is, étale-locally, a disjoint union of
  standard tamely ramified pieces. Scheme-theoretic; a field.
* **Proved** (Stacks Tag 0EYF, *clauses 1 and 2 only*) — such a piece is finite free, and
  is étale where the divisor equation is invertible: `Pcf.Kummer.finrank_adjoinRoot_kummerPoly`, `Pcf.Kummer.etale_adjoinRoot_kummerPoly`,
  `Pcf.Kummer.ramificationIdx_adjoinRoot_kummerPoly_eq_one`. Clause 3, tameness in codimension one, is stated
  (`Pcf.Stacks.IsTamelyRamifiedInCodimensionOneAlong`) and proved only when every positive
  integer is invertible (`Pcf.Stacks.standardCover_isTamelyRamifiedInCodimensionOne_charZero`). See §B.4.

The interface is now `Pcf.KummerWitness` rather than `Pcf.UnramifiedWitness`.

**This changed nothing about what is assumed.** A second adversarial review proved
`Pcf.kummerWitness_iff_unramifiedWitness`: the two witness types are interderivable,
uniformly in `n`, with no hypotheses and no geometry. An intermediate version of this file
said the assumption had been "shrunk" and that Theorem `thm:bounding` (per-divisor form) was "conditional on
less"; **that is retracted**. The assumption was *restated*, in the same sense in which
§F records that `key` was restated as P2.

The reason is structural. Nothing in `KummerWitness` ties its `Base`, `deg`, `unit` or
`prime` to the prime whose index is `ram q`; the supplier chooses all four freely. So
`Pcf.Kummer.ramificationIdx_adjoinRoot_kummerPoly_eq_one` gets applied to an algebra the supplier invented rather
than to the cover under discussion, and no content crosses. `Pcf.KummerWitness.ofEqOne`
makes the cost explicit: a proof of `n = 1` plus a closed constant, which is exactly what
`UnramifiedWitness` cost.

An intermediate version of this file also argued that equivalence-to-conclusion is
unavoidable for any sufficient interface and therefore not a defect. **That argument is
wrong and is retracted**: a sufficient hypothesis need only *imply* its conclusion. A
genuinely weaker interface is describable — fix the local extension at `q` as data of the
ambient structure and have `standardForm` supply an `AlgEquiv` from that extension onto a
Kummer algebra, so `Algebra.Etale.of_equiv` transports content. That is not what is built.

So: the new material in `Pcf/Abhyankar.lean` is real mathematics, correctly proved, and
**not load-bearing**. *As of 2026-09-21*, Theorem `thm:bounding` (per-divisor form) was
assumed, exactly as before.

**2026-10-04.** The interface `KummerWitness` is no longer a field of anything. Theorem
`thm:bounding` is derived on an affine chart from purity and Abhyankar's lemma in
`Pcf/Bounding/`; see §G, which also records the remaining modelling link A6 and what it is
worth. The paragraphs above are kept as the history that §G answers.

The table below describes what the *structures* demand.

### B.1 Fields of `DivisorDynamics` and `PCFSetup` (what Theorem `thm:normal-invariant` still assumes)

| ID | Lean field | Statement assumed | Now proved elsewhere? |
| --- | --- | --- | --- |
| B1 | `DivisorDynamics.step_surjective` | Lying over: every prime is the image of a prime (proof of Lemma `lem:lift`; Stacks 00HS / 00H8). | **Discharged for actual finite dominant integral schemes with finite-type target** by `finiteDominantFiniteType_divisor_lift`, which also proves finite fibres and needs no normality. It remains a field only on abstract ready-made `DivisorDynamics`s. |
| B2 | `DivisorDynamics.step_image_ramified_finite` | The branch divisor has finitely many components (§`sec:defs`, after Definition `def:crit-branch`). | **Discharged for the affine constructor** by `finite_heightOne_ramified` and for the actual normal-scheme constructor by finiteness of the actual critical divisor locus; in characteristic zero the latter follows from finite dominance, integrality, Noetherianity, and local finite presentation, with generic formal étaleness derived from separability. It remains a field of abstract ready-made `DivisorDynamics`s. |
| B3 | `PCFSetup.singularPrimes_finite` | `Sing(Y) ∩ B` and `Sing(B)` contain finitely many primes (Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`). | **Genuinely discharged** by `Pcf.PCFGeometry.singularPrimes_finite`, from properness plus Noetherianness. |
| B4 | `PCFSetup.meets_finite` | `B ∩ Z` contains finitely many primes (Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`). | **Genuinely discharged** by `Pcf.PCFGeometry.meets_finite`, from properness plus Noetherianness. |
| B5 | `PCFSetup.notMem_branch_iterate` | **Theorem `thm:bounding` (per-divisor form)**, applied to every iterate. | **Derived on chart routes** (§G): the legacy `Pcf.PCFSetupChart.notMem_nonEtaleBranch_iterate` uses A6; the preferred `Pcf.SchemeNormalizationPCFSetupChart.notMem_nonEtaleBranch_iterate` uses actual divisor points, actual stalk-defined `crit₁`, and A6s, with no conclusion-equivalent implication. `Pcf.NonEtalePCFSetup.toPCFSetup` turns the étale form into `key`. On the abstract route and on `Pcf.PCFGeometry.toPCFSetup` it is an explicit argument. The former `standardForm` (P2) is **removed**. |

### B.2 What the geometric layer actually assumes

These are the irreducible inputs — the statements that are genuinely quoted from the
literature rather than derived.

| ID | Lean field | Statement assumed | Source |
| --- | --- | --- | --- |
| P1 | `PurityData.localPurity` | **More than Stacks Tag 0BMB.** `Pcf.AbstractZariskiNagataPurity` (§B.5) restates the tag with all five hypotheses, but is *interderivable* with this field and so does not reduce it. The field says: if a point has codimension ≥ 1 and the morphism is étale at every codimension-one generization, it is étale there — quantified over *every* such point, with none of 0BMB's hypotheses (1) `𝒪_{X,x}` normal, (2) `𝒪_{Y,y}` regular, (3) `f` quasi-finite at `x`, (4) the dimension equality. Those hold throughout §`sec:bounding`'s application and are absorbed into the field rather than carried as data, so the field is 0BMB *plus* the standing hypotheses of §`sec:bounding`. Separately, substituting "étale at `x'`" for 0BMB's "unramified at `x'`" strengthens the hypothesis and so weakens the implication — that substitution alone is harmless. | Stacks Tag 0BMB plus §`sec:bounding`'s standing hypotheses |
| P2 | *(removed 2026-10-04)* formerly `Prop41Data.standardForm`, `PcfGeometry.standardForm` | **Was Theorem `thm:bounding` (per-divisor form) itself**, phrased as a `Pcf.KummerWitness` at each prime above a good prime, and **logically equivalent to its own conclusion** (`Pcf.nonempty_kummerWitness_iff`, `Pcf.kummerWitness_iff_unramifiedWitness`). Both fields are gone. Their replacement is the pair `Pcf.Stacks.ZariskiNagataPurity` / `Pcf.Stacks.AbhyankarLemma` of §G, which are statements about the cover `R → S` and cannot mention the restriction. The witness types and the refutation theorems remain in `Pcf/Geometry.lean`, consumed by nothing. | Stacks Tags 0EYF, 0EYG; SGA 1 Exp. XIII Prop. 5.2 |
| P3 | `PurityData.closure_eq_univ_of_codim_eq_zero` | A point of codimension zero is a generic point. **Discharged** for `Pcf.purityDataOfAlgebra` (§B.5); still a field of the abstract structure. | Bookkeeping; true in an irreducible scheme |
| P4 | `PurityData.nonEtale_isClosed`, `nonEtale_ne_univ` | The étale locus is open, and the morphism is generically étale (separability). The **first is discharged** for `Pcf.purityDataOfAlgebra` from `Algebra.isOpen_etaleLocus` (§B.5); the second remains assumed. | §`sec:bounding`, and §`sec:defs`'s separability hypothesis |
| P5 | `BoundingCorrectionLoci.singSelf_isClosed`, `singSelf_ne_univ` | `Sing(B)` is a proper closed subset — a variety in characteristic zero is generically regular. | Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` |
| P6 | `Prop41Data.singAmbient_*`, `interOther_*` | The other two loci are proper closed. For `B ∩ Z` this is **proved** by `Pcf.IsProperIrreducibleClosed.inter_sUnion_ne_self`; for `Sing(Y) ∩ B` it follows from `Pcf.not_subset_of_two_le_codim` given that `Sing(Y)` has codimension ≥ 2 (normality of `Y`). | Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` |

**The global form of purity is no longer assumed.** The manuscript derives it from the
local form by hand, remarking that the SGA reference was "difficult to parse for the
present application". That derivation is now machine-checked:
`Pcf.PurityData.codim_eq_one`.

**Non-vacuity of P2.** `Pcf.KummerWitness.cubic` inhabits the witness type, so P2 is not
unsatisfiable-by-construction. That is *all* it shows. Its degree `3` is a free choice —
degree-1 witnesses exist too, and in those the Kummer algebra is the base ring itself, so
the structure map is bijective. And the prime inside `cubic` is produced by
`Ideal.exists_maximal` composed with `Classical.choice`: nothing identifies it, and
nothing excludes the rational point of `ℚ[y]/(y³ − 1)` at which the local extension is
trivial. An intermediate version of this file presented the degree `3` as evidence that
the interface demands something non-trivial; it is not, and that is retracted.

`Pcf.UnramifiedWitness.trivial` and `Pcf.LocalModel.unramifiedWitness` remain in the
development but **are no longer consumed by any field**. They record the manuscript's own
Step 3/4 route (the restriction to the divisor is an isomorphism). In that route the two
`e`s are different quantities — the `e` of the local model is the degree of the *cover*,
while the index parameter is that of the *restriction*, which is `1` in every case.

**Non-vacuity of the join.** `Pcf/Examples/CofiniteWitness.lean` builds a complete
`Pcf.PCFGeometry` over `ℕ` with the cofinite topology, in which
`Pcf.IsProperIrreducibleClosed s ↔ ∃ x, s = {x}` is proved, the restricted system **genuinely ramifies**
(`restrictionDynamics_branch : resDyn.branch = {zeroPrime}` with `ram zeroPrime = 2`), the ramified
prime sits inside a correction locus exactly as Theorem `thm:bounding` permits, and `res.PCF` is
obtained by *applying* `Pcf.PCFGeometry.restriction_isPCF`. So the join is not vacuous.

That witness is deliberately cheap in one respect, and the file says so: because its
restricted system is the identity with `ram ≡ 1` away from the ramified prime, its
`standardForm` is discharged by `Pcf.KummerWitness.cubic` — transported along a proof that
the index is `1`, via `Pcf.KummerWitness.ofEqOne` — and exercises **no** purity or
Abhyankar content. It establishes consistency and inhabitation of `PCFGeometry`, not the
geometric substance. `CofiniteNat` is a toy space, not a variety.

## B.3 A trap this layer closes

An independent check of this development produced the following, as a purported
counterexample to Step 3:

> Take `R = ℤ`, `a = 2`, `u = 1`, `e = 2`, so `C = ℤ[√2]` and `z = √2`. Then
> `C/(z) ≅ ℤ/2 ≅ R/(a)`, yet `2` is totally ramified in `ℤ[√2]`: `(2) = (√2)²`,
> ramification index `2`.

The computation is correct, and it refutes the claim "the two quotient *rings* are
isomorphic, therefore the ramification index is 1" — a claim the manuscript never makes.
Step 4 is about the **restriction** `g = f|_A`, whose local model is the specific map
`R/(a) → C/(z)`; the *cover* `R → C` really is ramified with index `e`, and the manuscript
says so.

The formalization now pins both halves so the confusion cannot recur:

* `Pcf.LocalModel.restrictionMap_bijective` — the named map `R/(a) → C/(z)` is bijective.
  This, not the abstract isomorphism `quotientRootEquiv`, is what Step 4 consumes.
* `Pcf.LocalModel.root_ne_zero_mod_algebraMap` — under `2 ≤ e`, `Nontrivial R` and
  `¬ IsUnit a`, the class of `z` in `C ⧸ (a)` is a **nonzero** nilpotent, so the fibre of
  the cover over the divisor is genuinely non-reduced. This is the ramification direction,
  and it is proved.

  An earlier version of this file pointed instead at
  `Pcf.LocalModel.isNilpotent_root_mod_algebraMap`, which was wrong: that lemma carries no
  hypothesis on `e`, holds at `e = 0` and `e = 1`, and at `e = 1` exhibits the nilpotent
  `0`, since `z = ua` there. A statement true of the unramified case is not evidence of
  ramification. The adversarial review caught this; the three hypotheses above are what it
  takes to exclude those cases.

  Note what is still *not* proved: that the ramification index of the cover is exactly `e`.
  Non-reducedness of the fibre is weaker than that, and nothing here computes the index.

## B.4 Stacks Tag 0EYF: which clauses are proved, and what they are worth

`lean/Pcf/Abhyankar.lean` imports only Mathlib and `Pcf.LocalModel`. Tag 0EYF makes three
assertions about `C = A[x]/(x^e − f)`; that file addresses the first two, and
`lean/Pcf/Stacks/Abhyankar/StandardCover.lean` addresses the third in characteristic zero.

| Tag 0EYF clause | Status | Lean declaration |
| --- | --- | --- |
| 1. `Spec(C) → Spec(A)` finite locally free | **proved**, as free of rank `e` | `Pcf.Kummer.finrank_adjoinRoot_kummerPoly`; freeness and finiteness are Mathlib's `Polynomial.Monic.free_adjoinRoot` / `Monic.finite_adjoinRoot` |
| 2. étale over `Spec(A_f)` | **proved** | `Pcf.Kummer.etale_adjoinRoot_kummerPoly`, `Pcf.Kummer.ramificationIdx_adjoinRoot_kummerPoly_eq_one`, `Pcf.Kummer.etale_adjoinRoot_localPoly_of_isUnit` |
| 3. tamely ramified over `Spec(A)` in codimension 1 | **stated; proved only when every positive integer is a unit in `A`** (the PCFAWD characteristic-zero setting). The general tame case is not proved. | predicate `Pcf.Stacks.IsTamelyRamifiedInCodimensionOneAlong`; `Pcf.Stacks.standardCover_isTamelyRamifiedInCodimensionOne_charZero`, for the cover `x^e − u·a` with `u` a unit |

Clause 3 is what the name "standard *tamely ramified* morphism" refers to, and it is the
clause the proof of Tag 0EYG consumes.

Supporting results:

| Statement | Lean declaration |
| --- | --- |
| the Bézout identity `f' · p₁ + f · p₂ = 1` for `f = X^e − u` | **Mathlib's** `Polynomial.separable_X_pow_sub_C_unit` (this is `Polynomial.Separable`, which unfolds to `IsCoprime f (derivative f)`) |
| monic + separable ⟹ standard étale root algebra | `Pcf.Kummer.isStandardEtale_adjoinRoot_of_separable` — **the general form**, and the one genuine library gap found |
| `R[y]/(y^e − u)` is a standard étale `R`-algebra | `Pcf.Kummer.isStandardEtale_adjoinRoot_kummerPoly` |
| it is nontrivial and has primes | `Pcf.Kummer.nontrivial_adjoinRoot_kummerPoly`, `Pcf.Kummer.exists_isPrime_adjoinRoot_kummerPoly` |
| **tameness is necessary** — in characteristic 2 with `e = 2` the conclusion fails | `Pcf.Kummer.not_etale_adjoinRoot_X_sq_sub_one_of_two_eq_zero` |
| **the unit hypothesis is necessary** — at `a = 0` the model `k[y]/(y^e)` is not reduced | `Pcf.Kummer.not_etale_of_not_isUnit` |
| the substitution `x ↦ t·y`, an isomorphism when `t` is a unit | `Pcf.Kummer.localPolyToKummerPoly`, `Pcf.Kummer.localPolyEquivKummerPoly` |

Two cautions about the table above.

* **`localPolyEquivKummerPoly` is not Tag 0EYF.** It assumes the divisor equation is already `t^e` for a
  unit `t` — a perfect `e`-th power. Inverting `f` makes it a unit, not an `e`-th power;
  making it an `e`-th power is the extra base change performed inside the proof of Tag
  0EYG. An intermediate version of this file sourced `Pcf.Kummer.etale_adjoinRoot_localPoly` to
  "Tag 0EYF, `Spec(C_f) → Spec(A_f)`"; that is wrong and is corrected. The statement that
  does correspond to inverting `f` is `Pcf.Kummer.etale_adjoinRoot_localPoly_of_isUnit`, which needs
  no `e`-th power hypothesis. Nothing in the development consumes either.
* **`Pcf.Kummer.ramificationIdx_adjoinRoot_kummerPoly_eq_one` is about Mathlib's `Ideal.ramificationIdx`**, a
  `Module.length`. `Pcf.heightOneRamificationIdx_eq_dvrExponent` now identifies this length with the
  usual exponent for a finite extension of normal Noetherian domains at a height-one
  prime.  That theorem does **not** turn this particular Kummer statement into the
  manuscript's restriction index: the index here is over a base with the divisor equation
  inverted and belongs to the *cover*, whereas the paper uses the DVR of the divisor prime
  for the *restriction* `g = f|_A`.

**What this is worth to the development: standalone mathematics, still not load-bearing.**
The derivation of Theorem `thm:bounding` in `Pcf/Bounding/` (§G) does not go through
`Pcf/Abhyankar.lean`: Steps 3–4 use `Pcf.LocalModel` (the restriction of a standard piece to
the divisor is an isomorphism), which holds for any `e ≥ 1`, and tameness is consumed only
inside the assumed `Pcf.Stacks.AbhyankarLemma`. The remark that a genuinely weaker interface
would "fix the local extension as data and have Abhyankar's lemma supply an `AlgEquiv` from
that extension" is what §G now does: the extension is the chart's `R → S`, and G2 supplies
`R' ⊗[R] S ≃ₐ[R'] ∏ R'[zᵢ]/(zᵢ^{eᵢ} − uᵢ a)` for it.

## B.5 Zariski–Nagata purity: two fields discharged, and the tag stated faithfully

`lean/Pcf/NonEtaleLocus.lean` and `lean/Pcf/ZariskiNagata.lean` address entries P1, P3 and
P4. **Purity itself is still assumed** — Mathlib does not have it — but two of the four
fields of `Pcf.PurityData` become theorems once the abstraction is instantiated at the
spectrum of an actual algebra, and the assumed field is restated so that it matches Stacks
Tag 0BMB instead of exceeding it.

### Discharged

| Field | Was | Now | Why |
| --- | --- | --- | --- |
| `nonEtale_isClosed` (part of P4) | assumed | **proved** for `Pcf.purityDataOfAlgebra` | `Algebra.isOpen_etaleLocus`: Mathlib proves the étale locus is open, so its complement is closed |
| `closure_eq_univ_of_codim_eq_zero` (P3) | assumed | **proved** for `Pcf.purityDataOfAlgebra` | over a domain a prime of height zero is `⊥`, and `V(⊥) = Spec S` |

Both are consumed by the manuscript's own deduction:
`Pcf.PurityData.notMem_nonEtale_of_specializes` uses the first and
`Pcf.PurityData.one_le_codim` uses the second. So within the purity layer these are real
discharges, not decoration.

The truncation `Pcf.primeSpectrumCodimension p = (p.asIdeal.height).toNat` from `ℕ∞` to `ℕ` is a junk-value
hazard — a prime of infinite height would read as codimension zero — so
`Pcf.purityDataOfAlgebra` takes finiteness of heights as an explicit hypothesis rather than
hiding it behind Noetherianness.

### Not made faithful — a retraction

`Pcf.AbstractZariskiNagataPurity` states Tag 0BMB with all five of its hypotheses present, and
`Pcf.PurityData.ofAbstractZariskiNagataPurity` derives `localPurity` from it plus four standing
hypotheses. An earlier version of this section claimed that this made P1 match the
literature instead of exceeding it, and that "the assumption is now exactly the cited
theorem".

**That is false and is retracted.** The hypothesis fields `normal`, `regularBelow`,
`quasiFinite` are bare `X → Prop` and `codimTarget` a bare `X → ℕ`, tied to no morphism,
no local ring and no scheme. `Pcf.PurityData.toAbstractZariskiNagataPurity` therefore builds a
`AbstractZariskiNagataPurity` from *any* `PurityData` by instantiating them at `True`, and
`Pcf.PurityData.ofAbstractZariskiNagataPurity_toAbstractZariskiNagataPurity` proves the roundtrip is the identity —
**definitionally**; the proof is `cases D; rfl`. The two are interderivable, so nothing was
reduced.

This is the third time in this repository that an interface decorated with content-free
predicates has been presented as an axiom reduction. The first two were
`Pcf.UnramifiedWitness` and `Pcf.KummerWitness` (§B.2). The corresponding refutations are
now all stated as Lean theorems: `Pcf.nonempty_unramifiedWitness_iff`,
`Pcf.kummerWitness_iff_unramifiedWitness`, and
`Pcf.PurityData.ofAbstractZariskiNagataPurity_toAbstractZariskiNagataPurity`.

A related claim is also retracted: the docstring of `ofAbstractZariskiNagataPurity` said requiring the
standing hypotheses at every point was "much less than the previous field, which required
none of them". By the roundtrip it is *exactly* the previous field. Its `hdim` field
additionally asks for global equidimensionality, which is **more** than §`sec:bounding` uses.

What the structure is actually worth: a caller holding genuine normality, regularity and
quasi-finiteness predicates can state the tag with them rather than absorbing them
silently. That is expressive value, not a theorem.

### A sharper fact, found by the same review

`Pcf.localPurity_of_codim_le_one` proves that the `localPurity` field holds **for free**
when every point of the non-étale locus has codimension at most one, because `Specializes`
is reflexive and the field's own hypothesis applied at the point itself closes the goal.

So all of the content of Tag 0BMB, as this development uses it, lies at points of
codimension at least two — which is exactly where the manuscript applies it
(`Pcf.PurityData.notMem_nonEtale_of_specializes` assumes `2 ≤ codim η`).
`Pcf.PurityData.ofCodimLeOne` packages this.

A practical consequence, not yet exploited: a non-degenerate example with `E ≠ ∅` but `E`
of pure codimension one would need **no purity input at all**. The only obstacle to
building one is computing a non-étale locus in Mathlib, not purity.

### Not discharged, and not claimed

* **Purity itself** (`AbstractZariskiNagataPurity.purity`, Stacks Tag 0BMB) is a field. Nothing here
  proves any part of it.
* **`nonEtale_ne_univ`** — generic étaleness — remains a hypothesis. In the manuscript it
  is the separability of the function-field extension; it is a real condition on `S`.
* **Non-vacuity is degenerate.** `Pcf.purityDataOfEtale` inhabits the datum, but only with
  `E = ∅`, where there are no components of `E` and `Pcf.codim_eq_one_of_algebra` has no
  instances. No example with `E ≠ ∅` is built, so global purity is not exercised
  non-trivially on any concrete algebra.
* **`Pcf.PurityData` was not consumed by Theorem `thm:normal-invariant` when §B.5 was written.** It is now, via
  `Pcf/Wiring.lean`; see §B.6 for exactly how much that buys and how much it does not.
* **The two new files do not talk to each other.** `Pcf/NonEtaleLocus.lean` does not
  import `Pcf/ZariskiNagata.lean`, and `Pcf.purityDataOfAlgebra` takes the plain
  `localPurity`-shaped hypothesis, not a `Pcf.AbstractZariskiNagataPurity`. Nothing outside
  `Pcf/ZariskiNagata.lean` references that structure except the audit. They are two
  separate pieces of work on the same layer, not a chain.

## B.6 The purity layer wired into Theorem `thm:normal-invariant`

`lean/Pcf/Wiring.lean` is the first place in this development where the purity layer
reaches Theorem `thm:normal-invariant`. Before it, §B.5's discharges improved a side branch;
`Pcf.divisorDynamicsOfGeometry` existed but nothing was built through it.

### The chain

| Step | Status |
| --- | --- |
| `Algebra.isOpen_etaleLocus` | Mathlib |
| ⟹ `Pcf.isClosed_nonEtaleLocus` | proved (§B.5) |
| ⟹ `Pcf.finite_isProperIrreducibleClosed_subset` | proved, needs Noetherian |
| ⟹ `DivisorDynamics.step_image_ramified_finite` for the restricted system | **proved** — `Pcf.restrictionDivisorDynamicsOfPurity` |
| ⟹ `Pcf.PCFGeometry.restriction_isPCF` | proved |

Each arrow is a theorem. That is **not** the claim that nothing is assumed: the inputs —
generic étaleness (`nonEtale_ne_univ`), purity itself (`localPurity`),
`ramified_subset_nonEtale`, and `standardForm` — are all still hypotheses. What changes is
that `step_image_ramified_finite` is no longer among them on this route.

`Pcf.restrictionDivisorDynamicsOfAlgebra` is the composite over an honest `R`-algebra, and takes **no
closedness argument**: Mathlib supplies it.

### Exactly what is and is not discharged

* **Discharged:** `step_image_ramified_finite` for the **restricted** system `restriction`, on the
  `Pcf.PCFGeometry.ofPurityData` route.
* **Still assumed:** `step_image_ramified_finite` for the **ambient** system `ambient`. It is a field of
  `ambient : DivisorDynamics PX`, and `PX` is a bare type with no topology, so there is nothing to run
  the argument on.
* **Still assumed:** `step_image_ramified_finite` on the plain `Pcf.PCFGeometry` and `Pcf.PCFSetup`
  routes, which take `restriction` as a ready-made `DivisorDynamics`. The field was not removed from the
  structure; an alternative constructor was added that does not need it.

### The trade, and its converse

`step_image_ramified_finite` is exchanged for `ramified_subset_nonEtale` (ramified primes lie in the
non-étale locus — Definition `def:crit-branch` in the direction the argument needs), plus properness of
that locus, plus Noetherianness.

**This is a trade, not a reduction in logical strength**, and
`Pcf.exists_nonEtale_of_branch_finite` proves the converse: given `step_image_ramified_finite`, the
union of the finitely many branch primes is a closed set with the required property, so
the trade reverses as soon as that union is not the whole space. Three earlier tasks in
this repository claimed reductions that were not reductions (§B.2, §B.5); the converse is
stated here so that this one cannot be read as a fourth.

What the trade is worth: the hypothesis it introduces is the one the manuscript actually
states, and one of its three components — closedness — is now supplied by Mathlib instead
of assumed.

### Non-vacuity

`Pcf.Examples.restrictionDynamicsOfPurity` is an inhabitant with **genuine ramification**:
`resDynOfPurity.branch = {zeroPrime}`, and `Pcf.Examples.restrictionDynamicsOfPurity_isPCF` obtains
`IsPCF` by *applying* `Pcf.PCFGeometry.restriction_isPCF_of_purityData`. Its `step_image_ramified_finite` is
proved, not supplied.

Two caveats the file itself records. Its purity datum is built by
`Pcf.PurityData.ofCodimLeOne`, so `localPurity` costs nothing there (§B.5) and no
Zariski–Nagata content is exercised; and its closedness comes from the singleton `{0}`
being finite, not from `Algebra.isOpen_etaleLocus`. It exercises the *finiteness* half of
the wiring. The Mathlib half is exercised by `Pcf.restrictionDivisorDynamicsOfAlgebra`, whose only
available instances have an unramified restricted system, because the sole inhabitant of
the spectrum route so far is `Pcf.purityDataOfEtale` with `E = ∅`.

## B.7 `step_image_ramified_finite` fully discharged on `Spec S`

§B.6 derived `DivisorDynamics.step_image_ramified_finite` for a restricted system from a `Pcf.PurityData`, but
still assumed `ramified_subset_nonEtale`. `lean/Pcf/SpectrumDynamics.lean` removes that
too, and more besides. The comparison is the clearest way to state it:

| Input | `Pcf.restrictionDivisorDynamicsOfPurity` (§B.6) | `Pcf.divisorDynamicsOfSpectrum` |
| --- | --- | --- |
| `step`, `step_surjective` (lying over, B1) | supplied | supplied |
| `ram` | **supplied by the caller** | canonical — `Ideal.ramificationIdx` at the generic point |
| `ramificationIdx_pos` | **supplied** | **proved** (`Ideal.ramificationIdx_pos`) |
| ramified ⟹ non-étale | **supplied** (`hbranch`) | **proved** |
| a `Pcf.PurityData`, including `localPurity` = Tag 0BMB | **required** | **not required at all** |
| generic étaleness | a field of the datum | the one remaining hypothesis |
| `step_image_ramified_finite` (B2) | derived | derived |

So on this route a `Pcf.DivisorDynamics` over `Spec S` costs exactly two assumptions: **lying over**
and **`nonEtaleLocus R S ≠ univ`** (the separability hypothesis of §`sec:defs`). Zariski–Nagata is
not among them — `step_image_ramified_finite` never needed purity, only closedness of the locus,
properness, and Noetherianness.

### The two new theorems

* `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx` — **ramified implies non-étale.** From
  `Ideal.ramificationIdx_eq_one`, which derives index `1` from unramifiedness, together
  with "étale implies unramified". This is Definition `def:crit-branch` in the direction §`sec:bounding` uses it, and
  it was previously a hypothesis on every route.
* `Pcf.subset_nonEtaleLocus_of_one_lt_primeSpectrumRamificationIdx` — the same statement for a whole prime
  rather than a point. `PrimeSpectrum` is sober, so a prime is the closure of its generic
  point, and the locus is closed.

### Is this another restatement? No, and here is the check

The three earlier failures (§B.2, §B.5) were interfaces logically equivalent to their own
conclusions. This one is not, and the reason is structural: the surviving hypothesis
`nonEtaleLocus R S ≠ univ` mentions only `R` and `S`. It refers to no `step`, no `ram` and
no branch set, so no field of `Pcf.DivisorDynamics` can imply it and the derivation cannot be
circular. The content that replaced `hbranch` is a Mathlib theorem, not a new field.

### Lying over, now restricted to divisors

`Pcf.comap_surjective_of_isIntegral_of_injective` proves Stacks Tag 00HS: for an injective
integral ring map the induced map on prime spectra is surjective. That is the content of
B1, from `Ideal.nonempty_primesOver`.

`Pcf.height_under_eq_of_finite_of_normal` supplies the missing dimension statement for a
finite injective extension of Noetherian domains with normal base: every prime has the same
height as its contraction.  The proof combines going down with integrality, which makes the
prime minimal over the extended contraction.  Thus `Pcf.heightOneUnder` is a map on
height-one primes and `Pcf.heightOneUnder_surjective` restricts lying over to that subtype.
`Pcf.affineDivisorPointEquiv` identifies this subtype with codimension-one points of
`Spec`, and `Pcf.affineDivisorUnder_surjective` is the corresponding scheme-point theorem.

For the normalization comparison, `Pcf.heightOneComapPoint` and
`Pcf.SchemeDivisorPoint.imagePoint` deliberately land in the full target spectrum or
underlying space instead of silently identifying normalized and unnormalized divisors.
`Pcf.finite_heightOne_comap_fiber` proves finite fibers for the affine map under
quasi-finiteness, with no normality or height hypothesis on the target; the scheme-level
`AlgebraicGeometry.Scheme.Hom.finite_divisorPoint_fiber` proves the same for every locally quasi-finite,
quasi-compact morphism.  When both affine rings are normal,
`Pcf.finite_heightOneUnder_fiber` specializes this to the actual height-one contraction
map.  Thus the finite-fiber clause used by the normalization bookkeeping is available.

That comparison is now isolated rather than folded into the bookkeeping.
`Pcf.heightOneUnderOfCodim` takes exactly
`hcodim : ∀ Q, height (Q ∩ R) = 1`; from it,
`heightOneUnderOfCodim_surjective` and `finite_heightOneUnderOfCodim_fiber` prove the two
set-theoretic properties needed of the divisor map.  The reverse height direction used for
surjectivity is the theorem `height_eq_one_of_liesOver_heightOne` and needs no target
normality.  The forward direction `hcodim` was the remaining finite-type/catenary
geometry; it is now proved by `height_under_eq_of_finite_of_finiteType`, using Noether
normalization, and packaged scheme-theoretically by
`finiteDominantFiniteType_divisor_lift`.

`Pcf.NormalizationUnnormalizedDynamics` then uses this kind of map between two carriers.  Its theorem
`normalized_isPCF_of_isNonEtaleBranchPCF` proves the normalized system PCF from unnormalized `1`-PCF by taking the
finite-fiber preimage of `PC₀`.  Thus the former one-carrier conflation in `UnnormalizedDynamics` is
not part of the corrected chart route.

`Pcf.exists_principal_localizationAway_of_atPrime_isPrincipal` proves the algebraic
shrinking step needed for Step 0: if the divisor ideal becomes principal in `R_q`, then on
some principal open containing `q` it is generated by one equation. Its height-one
specialization obtains the local principality from the DVR theorem and therefore
principalizes the divisor near its own generic point. The intermediate theorem
`exists_principal_localizationAway_of_atPrime_ufd` proves the needed conclusion at an
arbitrary point from exactly a UFD instance on the local ring.  The full UFD theorem is no
longer needed for the point occurring in Step 0.  The theorem
`isDomain_of_isRegularLocalRing_of_ringKrullDim_eq_one` proves the dimension-one case of
Stacks 00NP directly from Krull intersection.  The full tag is now proved as
`Pcf.Stacks.isDomain_of_isRegularLocalRing`, by cotangent-space induction, prime avoidance,
Krull intersection, and Nakayama.  In addition,
`heightOne_isPrincipal_of_regularLocalRing_dim_two` proves that a height-one prime in a
two-dimensional regular local domain is principal when its one-dimensional quotient is
regular.  Finally,
`exists_principal_localizationAway_of_atPrime_regular_dim_two` feeds that result into the
shrinking theorem.  These are exactly the local dimensions at the generic point of a
divisor inside `B`.  Two further theorems close the regular-ring interface in these exact
dimensions: `isRegularRing_of_isRegularLocalRing_of_ringKrullDim_eq_one` identifies the
one-dimensional stalk as a DVR/Dedekind domain, while
`isRegularRing_of_isRegularLocalRing_of_isIntegrallyClosed_dim_two` checks all primes of
the normal two-dimensional regular local domain (generic, height one, and maximal).
`Pcf.LocalBoundingChart.toBoundingChart` consequently derives the original affine chart
package directly from the two stalks.  This eliminates the need to construct a regular
affine neighborhood or formalize openness of the regular locus.

`Pcf.SchemeStalkBoundingLocalizationPresentation` is now the dynamics-facing
scheme-to-stalk interface. It contains a `LocalBoundingChart`, the natural algebra maps
from its quotient rings to the actual stalks, proofs that the stalks are the corresponding
localizations, and the quotient-ring map square. Its
`toSchemeStalkBoundingPresentation` constructs the two coordinate isomorphisms and their
localized square; formal étaleness then transports the purity--Abhyankar conclusion. This
corrects an over-strong intermediate interface: the chart rings are local rings, so an
actual open restriction need not globally be their spectra. The open-neighbourhood
interfaces `SchemeLocalBoundingPresentation` and
`SchemeAffineLocalBoundingPresentation` remain proved alternatives when such global
coordinates are available. For the literal affine quotient map, the localization
presentation is constructed by
`LocalBoundingChart.toSchemeStalkBoundingLocalizationPresentation` from the canonical
structure-sheaf localizations and functoriality of `Spec`. For a morphism between actual
closed subschemes, `Scheme.IdealSheafData.quotientStalk_isLocalization` proves the same
localization statement on the canonical affine section quotients;
`quotientAppLE`, `comap_quotientPoint_quotientAppLE`, and
`stalkMap_comp_quotientStalkAlgebraMap` prove the quotient map, point contraction, and
stalk square. Consequently `closedSubschemeStalkBoundingLocalizationPresentation`
constructs the entire stalk interface from quotient-ring equivalences and their
section-level square. More specifically,
`quotientAppLE_subschemeMap_eq_quotientMap` proves that an actual ambient morphism induces
the ordinary quotient of its map on sections, and
`closedSubschemeStalkBoundingLocalizationPresentationOfAmbientMap` needs only equalities
identifying the target and source defining ideals with `(a)` and `p`. On affine ambient
schemes, `affineIdealSheaf_le_map_of_localBoundingChart` derives the sheaf containment
from the chart and `J.ideal ⊤ = (a)`, while
`affineIdealSheafStalkBoundingLocalizationPresentation` constructs the entire restricted
stalk presentation with source ideal `I.ideal ⊤`.
`exists_principal_comap_affineBasicOpen_of_atPrime_regular_dim_two` derives the target
principal equation on the actual open scheme from the regular local hypotheses. For
honest affine primes `D ≤ q` and `P ≤ Q`,
`LocalBoundingChart.toGlobalQuotientSchemeStalkBoundingChart` now connects the canonical
localized construction to the actual stalk map of `Spec(S/P) → Spec(R/D)`. Its direct
composite
`toGlobalQuotientSchemeStalkBoundingLocalizationPresentationOfHeightOneDivisorsAt`
has no formal-étaleness premise and accepts exactly the pointed avoidance of the other
branch divisors used in Step 0. The scheme-extraction constructor now obtains the affine
section algebra, canonical primes, quotient morphism and actual stalk comparison from the
ambient finite morphism, ideal sheaves and source point. It also identifies the two local
coordinate rings with the actual ambient and divisor stalks, transports their regularity
and dimensions, and derives the local equation. What remains is to construct the intended
height-one ideal sheaves and prove the Step 0 geometric regularity/codimension statements
and pointed avoidance.

Two formerly explicit local-chart obligations are now theorems.
`LocalBoundingChart.toBoundingChart` derives Noetherianity of the cover from
module-finiteness over the regular local base, and derives its pointwise height equality
from module-finiteness, `FaithfulSMul`, and normality of the base via
`height_under_eq_of_finite_of_normal`. The geometric input is therefore injectivity of the
local algebra map, not a supplied dimension formula. The cover's formerly quantified
local-normality field is now the ordinary `IsIntegrallyClosed S` condition, from which
normality of every prime localization is derived. The separate primality field for the
selected component was also removed: membership in `minimalPrimes (aS)` already proves it.
Moreover `isEtaleAt_height_zero_of_charZero_of_integral` derives generic étaleness from
integrality, dominance, and characteristic zero, so `LocalBoundingChart.generic_etale`
has been removed. The constructor
`LocalBoundingChart.ofFiniteNormalLocalizationOfHeightOneDivisorsAt` starts from a finite
dominant normal algebra and honest target/source height-one divisors. It canonically
localizes the cover over the chosen point, derives finiteness, injectivity, domain and
normality, transports the source component, proves it is minimal over the local equation,
obtains tameness from the rational-algebra structure, and derives codimension-one
unramifiedness from the Step 0 condition that the selected prime lies on no other member
of `heightOneBranch`. The last implication uses
`ramified_heightOne_lies_over_of_avoids_other_branch_at`,
`isUnramifiedAt_of_ramificationIdx_eq_one_of_algebraRat` and
`isUnramifiedAt_localization_algebraMapSubmonoid`.

For a finite normal affine self-map, `Pcf.divisorDynamicsOfFiniteNormalSelfAlgebra` uses this map as
`DivisorDynamics.step`, proves `step_surjective`, and
`divisorDynamicsOfFiniteNormalSelfAlgebra_branch` identifies its abstract branch set with
`heightOneBranch`. The older conclusion that Mathlib's Krull API could not reach
codimension preservation was therefore too pessimistic and is retracted.
`Pcf/Bounding/SchemeExtraction.lean` now extracts the finite affine preimage, finite
faithful section algebra, canonical source and target primes, divisor incidences,
quotient morphism and actual closed-subscheme stalk comparison from an ambient finite
dominant scheme morphism, ideal sheaves and a source point. It further identifies the
ambient localization and localized divisor quotient with the actual ambient and divisor
stalks; the strongest constructor transports regularity and dimension from the geometric
stalk/codimension statements and chooses the local equation internally.
`pointClosureIdealSheaf` constructs the reduced ideal sheaf of a divisor point,
identifies its affine components with the point primes, proves them prime of height one,
and proves functoriality under the ambient morphism. The finite-map height theorem also
constructs the target divisor point and proves compatibility of lifted points. The
point-closure specialization of the strongest constructor removes the ideal-sheaf,
compatibility, primality and height inputs. Its selected-point refinement takes an actual
codimension-one point on the target divisor, chooses the source point above it, proves
chart membership, and uses that point's type for divisor codimension one. The newer
specified-point refinement preserves the exact source point required by the global
quantifier. It derives ambient/divisor regularity and pointed avoidance from the literal
Step 0 exclusions. On the exact manuscript route ambient codimension two is supplied by
the divisor flag, and `imageDivisorCartierDataAtOfRegularDimTwo` constructs the Cartier
equation by the proved low-dimensional regular-local theorem. Thus the general
regular-local-implies-UFD theorem (Stacks 0AG0/0AGA) is not needed. The point-closure map
is functorial under composition and iteration; `invariantClosureMap_iterate` identifies
the actual invariant-divisor restriction iterate with the restriction of the ambient
iterate, and `InvariantDivisorSchemeNormalizationPCFSetup.toSchemeNormalizationPCFSetupChart`
constructs the global consumer chart from A6i.

### What it does not do

* **It does not prove purity**, and does not reduce P1. No `PurityData` is involved.
* **It discharges B1 and B2 on the affine height-one constructor**, but not on the abstract
  or scheme-global routes.
* **It constructs the divisor bridge for Theorem `thm:bounding` from the original finite
  dominant endomorphism plus literal Step 0 data.** The algebraic
  shrinking implication, exact low-dimensional local-principality theorem, and the
  stalk-level `LocalBoundingChart → BoundingChart` promotion are proved. The comparison
  of the affine quotient morphism with its stalk localization is also proved, as is the
  canonical finite normal localized cover and its source component. For actual affine
  quotient schemes,
  `toGlobalQuotientSchemeStalkBoundingLocalizationPresentationOfHeightOneDivisorsAt`
  connects that local algebra to the actual scheme-stalk presentation using only pointed
  avoidance of the other branch divisors. The scheme-extraction constructor now obtains
  its affine section algebra, canonical primes, incidences, quotient map, and stalk
  comparison from an actual ambient morphism, ideal sheaves and point. The two local
  coordinate rings are now identified with the actual ambient and divisor stalks, and
  the pointwise singular/other-branch exclusions now yield regularity and avoidance.
  On the exact dimension-two route, the local Cartier data are constructed directly from
  ambient/divisor regularity and codimension; no UFD instance is required. The actual
  invariant restriction and every iterate are identified with the point-closure
  construction, and A6s is produced as a theorem. The Step 0 neighborhood, incidence,
  codimension, regularity and branch-avoidance statements remain hypotheses in A6i, as do
  G1 and G2; none is conclusion-shaped.
* **A1 is discharged over normal targets and finite-type nonnormal targets.** `HeightOnePrime` and
  `heightOneUnder` are tied to the ring map.  For a possibly nonnormal target, the honest
  affine and scheme-level point maps and their finite fibers are built.  The corrected
  dynamics has separate normalized and unnormalized carriers, and
  `heightOneUnderOfCodim` packages the divisor map once codimension preservation is known.
  `height_under_eq_of_finite_of_finiteType` and
  `coheight_apply_eq_one_of_finiteType` prove the missing codimension statement by
  Noether normalization. `schemeNormalizationUnnormalizedDynamicsOfFiniteType` builds the two
  divisor carriers, normalization map, finite fibers, and commuting square from actual
  scheme morphisms. The new scheme route constructs the honest critical-locus
  consumer and removes A6's circular implication. Its coordinate/primes/stalk plumbing,
  reduced divisor ideal sheaves, actual restricted iterate, and resulting chart are built
  from the original finite morphism once the literal Step 0 facts are supplied.
* **A2 is discharged for the affine and actual normal-scheme constructors.** `ram` is definitionally
  Mathlib's `Ideal.ramificationIdx`; the height-one source localization is a DVR, and
  `heightOneRamificationIdx_eq_dvrExponent` proves that the length equals the maximal-ideal exponent
  `e(𝔮/𝔪)`. `schemeDivisorRamificationIdx` is the corresponding actual stalk index and
  `divisorDynamicsOfFiniteDominantNormal` installs it as the scheme-level dynamics.
  `divisorDynamicsOfFiniteDominantNormal_iterateRamificationIdx` proves equality of the actual iterate index with
  `DivisorDynamics.iterateRamificationIdx`.
* **Non-vacuity is weak.** `Pcf.divisorDynamicsOfSpectrum` is inhabited (checked, with `R = S = ℚ`),
  but no instance with a genuinely ramified prime is exhibited; that needs a concrete
  ramification-index computation which Mathlib does not make easy.

## B.8 The unnormalized loci and the two-carrier correction

Added 2026-10-04 for Appendix `app:other-defs` and the `1`-PCF form of Theorem
`thm:normal-invariant`. `Pcf/Unnormalized.lean` extends `DivisorDynamics` by two critical predicates
`nonUnramifiedLocus m`, `nonEtaleLocus m` (for `crit₀(gᵐ)`, `crit₁(gᵐ)` of Definition `def:branch-loci`) and
stores U1–U5 because that abstract layer has no morphism of schemes. The actual-scheme
layer now defines both predicates from the actual stalk maps and proves U2–U5.

Since 2026-10-05 the faithful abstract route uses `Pcf.NormalizationUnnormalizedDynamics PN PA`: U1–U5 have
the same mathematical content, but normalized ramification divisors live on `PN` and the
unnormalized critical loci live on `PA`.  `Pcf.UnnormalizedDynamics` remains as the legacy one-carrier
interface and embeds by `NormalizationUnnormalizedDynamics.ofUnnormalizedDynamics`. On the newer actual-scheme
route, `Pcf.SchemeNormalizationUnnormalizedDynamics A PN` has no arbitrary critical-locus fields:
`crit₀(gᵐ)` and `crit₁(gᵐ)` are definitionally the formal-unramified and formal-étale
failure loci of the actual stalk map.

| ID | Abstract field / actual-scheme result | Status on the actual-scheme route | Manuscript source |
| --- | --- | --- | --- |
| U1 | `SchemeNormalizationUnnormalizedDynamics.mem_nonUnramifiedLocus_of_one_lt_ramificationIdx` | **proved on the actual finite-birational route** by `mem_schemeDivisorNonUnramifiedLocus_of_one_lt_ramificationIdx_of_birational` and installed by `schemeNormalizationUnnormalizedDynamicsOfFiniteBirational`. The proof constructs the tensor-image branch and localization from the commuting stalk square, uses the generic-stalk isomorphism to obtain the common fraction field at every source stalk, and uses the proved iterate-index identification. It remains a field only on abstract/generic interfaces. | `prop:loci-compare`(2), first inclusion |
| U2 | `SchemeNormalizationUnnormalizedDynamics.nonUnramifiedLocus_subset_nonEtaleLocus` | **proved**: formal étaleness implies formal unramifiedness for the actual stalk map. | `prop:loci-compare`(2), second inclusion |
| U3 | `SchemeNormalizationUnnormalizedDynamics.nonEtaleLocus_finite` | **proved** from finite dominance, local finite presentation, integrality, Noetherianity, and characteristic zero at the generic stalk; the finite generic field extension is separable and hence formally étale, and composition handles every iterate. | `prop:loci-compare`(1) |
| U4 | `SchemeNormalizationUnnormalizedDynamics.nonUnramifiedLocus_tower` | **proved** for actual stalk maps. | `lem:tower-unnormalized`(1) with `h = gⁿ` |
| U5 | `SchemeNormalizationUnnormalizedDynamics.nonEtaleLocus_tower` | **proved** for actual stalk maps. | `lem:tower-unnormalized`(2) with `h = gⁿ` |
| U6 | `NonEtalePCFSetup.notMem_nonEtaleBranch_iterate` | the **étale** conclusion of `thm:bounding` for `fᵐ`, every `m ≥ 1`: a prime of `A` outside `Σ_m` is not in `branch₁(gᵐ)` | `thm:bounding` |

U6 is the new primitive of the manuscript. It is *stronger* than B5 (`PCFSetup.notMem_branch_iterate`), and
`Pcf.NonEtalePCFSetup.toPCFSetup` derives B5 from U6 and U1–U2; so the `NonEtalePCFSetup` route assumes
U6 in place of B5, not in addition to it. `notMem_nonEtaleBranch_iterate` is stated only for `m ≥ 1`; the `m = 0`
case of `key` is proved from `iterateRamificationIdx 0 = 1`.

**U6 is derived on the chart route** (§G, 2026-10-04): `Pcf.PCFSetupChart.notMem_nonEtaleBranch_iterate` proves it from
Zariski–Nagata purity and Abhyankar's lemma on charts, given the modelling link A6 and the
three proved standard facts G3–G5. `Pcf.NonEtalePCFSetup` keeps `notMem_nonEtaleBranch_iterate` as a field so that the
abstract route and the examples are unchanged; `Pcf.PCFSetupChart.toNonEtalePCFSetup` fills it.
On the actual-scheme route, `Pcf.SchemeNormalizationPCFSetupChart.notMem_nonEtaleBranch_iterate` instead derives
U6 from A6s; there is no implication from abstract critical membership to chart
non-étaleness because critical membership already unfolds to the actual stalk predicate.

### Modelling caveats specific to this layer

* **The legacy carrier conflation is not used by the corrected route.** `UnnormalizedDynamics` still
  puts `crit₀`, `crit₁` and normalized `ram` on one type for compatibility with the older
  examples.  `NormalizationUnnormalizedDynamics` instead records a finite-fiber map `PN → PA`, its
  commutation with pushforward, and U1 after applying that map.  Theorems
  `normalization_image_postcriticalSet_subset_nonUnramifiedPostcriticalSet` and `normalized_isPCF_of_isNonEtaleBranchPCF` perform the transfer
  without injectivity. For actual finite dominant morphisms to finite-type integral
  targets, `schemeNormalizationUnnormalizedDynamicsOfFiniteBirational` constructs the divisor map,
  finite fibers, commuting square, and U1 from generic-stalk birationality. The
  `GlobalNormalization*.lean` modules now construct the canonical normal finite
  normalization, prove the comparison isomorphism, construct the finite dominant commuting
  lift, and feed it to `schemeGlobalNormalizationUnnormalizedDynamicsOfFiniteType`. Thus this geometry
  is fully discharged under the finite-type characteristic-zero hypotheses.
* **On the legacy and two-carrier abstract interfaces, `crit_i(gᵐ)` is data.** On
  `SchemeNormalizationUnnormalizedDynamics`, both are derived from the actual iterate's stalk map.
  There is no equality formula for `crit₀(gᵐ)` in terms of `crit₀(g)`; U4 is the inclusion
  required downstream.
* **Only the instance `h = gⁿ` of `lem:tower-unnormalized` is proved**, which is all
  `cor:orbit-unnormalized` and `thm:normal-invariant` use. The lemma's branch-locus
  inclusions for a general tower `h ∘ g`, and the failure of converse inclusions, are not stated.
* **`prop:loci-compare`(3)** (agreement of the three loci where both local rings are
  normal) is not stated.

### What is proved from U1–U6

`Pcf.UnnormalizedDynamics.orbit_unnormalized_zero/one` (`cor:orbit-unnormalized`),
`Pcf.UnnormalizedDynamics.isNonEtaleBranchPCF_of_nonEtaleBranch_subset` (the dynamical half of `thm:normal-invariant`),
`Pcf.UnnormalizedDynamics.isNonUnramifiedBranchPCF_of_isNonEtaleBranchPCF`, `Pcf.UnnormalizedDynamics.isPCF_of_isNonUnramifiedBranchPCF` (`1`-PCF ⟹ `0`-PCF ⟹ PCF),
`Pcf.NonEtalePCFSetup.restriction_isNonEtaleBranchPCF` (`thm:normal-invariant`), `Pcf.NonEtalePCFSetup.restriction_isNonUnramifiedBranchPCF/res_pcf`
(`cor:normal-invariant-pcf`), `Pcf.NonEtalePCFSetup.restriction_isNonEtaleBranchPCF_of_iterate` (`cor:normal-preperiodic`).
On the corrected route the corresponding results are
`Pcf.NormalizationPCFSetup.restriction_isNonEtaleBranchPCF`, `normalized_isPCF`, and `normalized_isPCF_of_iterate`; the last PCF
step is a theorem from finite normalization fibers.

### `ex:pinched`

`Pcf/Examples/Pinched.lean` proves the ring-level claims outright (any commutative ring for
`f̃*R ⊆ R` and `R_B` closed under `p ↦ p(z²)`; a field of characteristic zero, using only
`4 ≠ 0`, for `R = k[w, z², z(w−1), z³−4z]`; characteristic zero for the injectivity of the
orbit `4, 16, 256, …`). The dynamical conclusion — `PC₀(g)` and `PC₁(g)` infinite while
`PC(g) = {0}` — is proved for **any** `UnnormalizedDynamics` on the points of `B` with step `z ↦ z²`
and `o ∈ crit₀(g)` (`nonUnramifiedPostcriticalSet_infinite`), and instantiated by `nodeUnnormalizedDynamics`, whose critical
loci `{o, 0}` are **stipulated**, not computed. The manuscript's fibre-length argument for
`o ∈ crit₀(g)` (`ℓ(𝒪_{B,o}/g*t) = 2`), the Ferrand pushout, the normalization `ν`, the
finiteness of `f`, and the non-flatness of `f` at `o` are not formalized.

## C. What is proved outright (no assumption beyond A, B and U)

The conjecture the project is named after — Conjecture `conj:pcfawd` of `latex/paper.tex`, due to the
authors and quoted on p. 2 of Bridy–Ingram–Jones–Juul–Levy–Manes–Rubinstein-Salzedo–Silverman,
*Finite ramification for preimage fields of post-critically finite morphisms*, Math. Res.
Lett. **24** (2017), no. 6, 1633–1647, `arXiv:1511.00194` — has **both** of its paragraphs
proved in this layer. See `lean/Pcf/AllTheWayDown.lean`, and read its header for the
conditionality: these are theorems about `Pcf.DivisorDynamics` and `Pcf.PCFSetup`, not about
varieties, and Theorem `thm:bounding` (per-divisor form) is assumed (P2).


Everything in `Pcf/Dynamics.lean` and `Pcf/Restriction.lean`:

| Manuscript | Lean declaration |
| --- | --- |
| Lemma `lem:lift` (scheme-level existence and finiteness; abstract padding) | `Pcf.finiteDominantFiniteType_divisor_lift`; `Pcf.DivisorDynamics.IsChain.extend` |
| chains ↔ iterates dictionary | `Pcf.DivisorDynamics.exists_isChain_iff` |
| multiplicativity in towers | `Pcf.DivisorDynamics.iterateRamificationIdx_add` |
| Proposition `prop:iterates`(1) | `Pcf.DivisorDynamics.mem_branch_iterate_iff` |
| Proposition `prop:iterates`(2) | `Pcf.DivisorDynamics.mem_branch_iterate_succ` |
| Proposition `prop:iterates`(3)–(4) | `Pcf.DivisorDynamics.postcriticalSet_iterate`, `Pcf.DivisorDynamics.isPCF_iterate_iff`, `Pcf.DivisorDynamics.branch_iterate_subset_postcriticalSet`, `Pcf.DivisorDynamics.step_image_postcriticalSet_subset` |
| Definition `def:pcf`, last clause | `Pcf.DivisorDynamics.isPCF_iff_forall_orbit_finite` |
| Lemma `lem:normalization` | `Pcf.DivisorDynamics.isPCF_of_finite_cover` |
| periodic-divisor selection in the proof of `thm:general` | `Pcf.exists_periodic_lift_of_surjective_finite_fibers`, `Pcf.NormalizationUnnormalizedDynamics.exists_periodic_lift` |
| Theorem `thm:normal-invariant` = Theorem `thm:normal-invariant` | `Pcf.PCFSetup.restriction_isPCF` |
| uniformity of `Σ` in `m` (the crux) | `Pcf.PCFSetup.branch_iterate_subset_bound` |
| Corollary `cor:normal-preperiodic` | `Pcf.PCFSetup.restriction_isPCF_of_iterate` |
| Corollary `cor:pcfawd`, normalized form | `Pcf.PCFSetup.normalization_isPCF` |
| Corollary `cor:pcfawd`, descent (**"PCF all the way down"**, Conjecture `conj:pcfawd` second paragraph) | `Pcf.isPCF_of_isPCF_restriction`, restated as `Pcf.pcfAllTheWayDown_divisorDynamics` |
| Corollary `cor:normal-preperiodic` (Conjecture `conj:pcfawd` first paragraph) | `Pcf.PCFSetup.restriction_isPCF_of_iterate`, restated as `Pcf.isPCF_restriction_of_periodic` |

And, in the geometric layer, all of §`sec:bounding` except P1–P6:

| Manuscript | Lean declaration |
| --- | --- |
| the integral-effective-divisor convention of §`sec:intro` (prime), topologically | `Pcf.IsProperIrreducibleClosed` — **correct only in an irreducible ambient space.** In any space, "no irreducible closed set strictly between `P` and `X`" is exactly codimension one; but `Pcf.IsProperIrreducibleClosed` is stated for an arbitrary space, where it also holds of the irreducible *components*, which have codimension zero. `IrreducibleSpace` is never assumed. A variety is irreducible by the manuscript's Conventions, so this is a fidelity gap in the abstraction, not an error. |
| primes are incomparable | `Pcf.IsProperIrreducibleClosed.eq_of_subset_of_isProperIrreducibleClosed` |
| Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`, the `Z` term | `Pcf.IsProperIrreducibleClosed.not_subset_sUnion`, `Pcf.IsProperIrreducibleClosed.inter_sUnion_ne_self` — *available, not wired in*: `BoundingCorrectionLoci` still takes `interOther_ne_univ` as a field |
| Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`, the `Sing(Y)` term | `Pcf.not_subset_of_two_le_codim` — *available, not wired in*, and weaker than it looks: `codim` there is an arbitrary `X → ℕ` unconnected to `IsProperIrreducibleClosed` or to the topology, so it also needs "`B` has codimension 1", which `IsProperIrreducibleClosed` does not supply. The two notions cannot currently be composed. |
| Theorem `thm:bounding` (per-divisor form), first paragraph (finiteness) | `Pcf.finite_isProperIrreducibleClosed_subset` |
| §`sec:defs`, finiteness of `Branch(g)` | `Pcf.PurityData.finite_isProperIrreducibleClosed_subset_nonEtale`; wired in through `Pcf.restrictionDivisorDynamicsOfPurity` (§B.6), and **fully discharged** over `Spec S` by `Pcf.divisorDynamicsOfSpectrum` (§B.7) |
| Definition `def:crit-branch`, ramified ⟹ non-étale | `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx` — **proved** from `Ideal.ramificationIdx_eq_one`; previously a hypothesis (§B.7) |
| the converse trade | `Pcf.exists_nonEtale_of_branch_finite` — a **negative** result (§B.6) |
| §`sec:bounding`, purity: local form ⟹ global form | `Pcf.PurityData.codim_eq_one`. `Pcf.codim_eq_one_of_algebra` and `Pcf.AbstractZariskiNagataPurity.codim_eq_one` are *restatements* of it at a spectrum and through `AbstractZariskiNagataPurity`; no result combines them |
| the étale locus is open ⟹ `E` is closed | `Pcf.isClosed_nonEtaleLocus` — **discharges a field** of `PurityData`, which is itself not consumed by Theorem `thm:normal-invariant` (§B.5) |
| height-zero points are generic | `Pcf.closure_eq_univ_of_primeSpectrumCodimension_eq_zero` — same status |
| purity is free below codimension two | `Pcf.localPurity_of_codim_le_one` |
| the `AbstractZariskiNagataPurity`/`PurityData` roundtrip is the identity | `Pcf.PurityData.ofAbstractZariskiNagataPurity_toAbstractZariskiNagataPurity` — a **negative** result (§B.5) |
| §`sec:bounding`, the inner maximality step | `Pcf.PurityData.notMem_nonEtale_of_specializes` |
| Theorem `thm:bounding`, Step 3 (as a *map*) | `Pcf.LocalModel.restrictionMap_bijective` |
| Stacks Tag 0EYF, clauses 1–2 only | `Pcf.Kummer.finrank_adjoinRoot_kummerPoly`, `Pcf.Kummer.etale_adjoinRoot_kummerPoly`, `Pcf.Kummer.ramificationIdx_adjoinRoot_kummerPoly_eq_one`, `Pcf.Kummer.etale_adjoinRoot_localPoly_of_isUnit` — see §B.4. **Not consumed by any assumption of the development.** |
| necessity of both hypotheses of Tag 0EYF(2) | `Pcf.Kummer.not_etale_adjoinRoot_X_sq_sub_one_of_two_eq_zero`, `Pcf.Kummer.not_etale_of_not_isUnit` |

| Theorem `thm:bounding`, Step 4's final inference | `Pcf.Ramification.ramificationIdx_eq_one_of_bijective`, `Pcf.UnramifiedWitness.eq_one` |
| Theorem `thm:bounding` (per-divisor form) | `Pcf.BoundingCorrectionLoci.notMem_branch` |
| the containment `branch(g) ⊆ Σ` after Theorem `thm:bounding` | `Pcf.BoundingCorrectionLoci.branch_subset_bound`, `Pcf.BoundingCorrectionLoci.finite_bound`, `Pcf.BoundingCorrectionLoci.finite_branch` |

## D. Supporting formalizations

| Manuscript | Lean file | Status |
| --- | --- | --- |
| Strategy §`sec:intro` / Theorem `thm:bounding`, Step 3 (`O[z]/(z^e − ua, z) = O/(a)`) | `Pcf/LocalModel.lean` | proved |
| Example `ex:cusp`: `k[t]` is the integral closure of `k[t²,t³]` in their common fraction field, and `t ∉ k[t²,t³]` | `Pcf/Examples/Cusp.lean` (`isIntegralClosure_cuspAlg`, `isFractionRing_cuspAlg`, `X_notMem_cuspAlg`) | proved |
| Example `ex:cusp`: the parametrization `k[x,y]/(y²−x³) → k[t]` and the Jacobian `2u` | `Pcf/Examples/Cusp.lean` (`cuspParam`, `jacobian_cuspSource`) | proved |
| Example `ex:cusp`: `B ∩ Z = {(0,0)}` | `Pcf/Examples/Cusp.lean` (`cusp_inter_branch`) | proved |
| Example `ex:branch-singular`: the quadric cone parametrization and the restriction `g(u) = u²` | `Pcf/Examples/Cusp.lean` (`coneParam`, `coneMap_restrict`) | proved |
| Example `ex:squaring` (squaring map on `P¹`), Example `ex:squaring-P2` (diagonal squaring) | `Pcf/Examples/Squaring.lean` | proved |
| Example `ex:wild` (wild counterexample, `deg_c(a_n) = (p+1)^{n−1}`) | `Pcf/Examples/CharP.lean` | proved |

## E. Not formalized at all

* `lem:restriction`, `prop:loci-compare`(3),
  `prop:pcf-equiv`(3), `lem:jacobian`, `ex:basilica`, `ex:dupont`, `ex:loci-compared`,
  `rem:why-normalized`, `q:singularPrimes-B`.
* In `ex:pinched`: everything scheme-theoretic (§B.8).
* In `ex:cusp`: the new sentence `branch₀(g) = branch₁(g) = {(0,0)} = B ∩ Z`.

* **Zariski–Nagata purity, any part of it.** It is assumed — faithfully, as
  `Pcf.Stacks.ZariskiNagataPurity` (§G.1), and in the older stronger form P1. What *is*
  machine-checked is the manuscript's own deduction of the global form **from** the local
  form (`Pcf.PurityData.codim_eq_one`), and now the manuscript's Step 1, which applies the
  local form (`Pcf.BoundingChart.isEtaleAt_of_notMem`).
* **Abhyankar's lemma itself** (Tags 0EYG/0EYH) is assumed as `Pcf.Stacks.AbhyankarLemma`
  (§G.1). Clauses 1 and 2 of Stacks Tag 0EYF are machine-checked standalone (§B.4). What is
  now **derived** from Abhyankar's lemma is Theorem `thm:bounding` (§G.3); the former
  disguised assumption P2 is removed.
* **The cited standard facts**: Tags 033B and 01JT and the finite-presentation pointwise case
  of Tag 036W are proved (G3–G5). The last is exactly the case used by the finite chart map.
* Example `ex:cusp`'s conclusion `Branch(g) = ∅` *as a statement about a branch
  divisor*: the file proves the normalization facts that give it
  (`integralClosure_cuspAlg_eq_top` and `isIntegrallyClosed_polynomial`, so
  `B̃ = k[t] = A = Ã`), but there is no scheme-level `Branch(·)` in the model to
  state it against. Likewise `Crit(f) = V(u)` and `Branch(f) = V(x)` are not
  formalized: only the Jacobian `2u` is.
* Example `ex:branch-singular`'s assertions that `Y` is normal and singular only at the vertex,
  and that `f` is étale away from it.
* §`sec:intro`'s literature discussion, the remarks formerly numbered 4.3 and 4.6 (not in `paper.tex`),
  the paragraph after Example `ex:wild` (the tame case), and Examples `ex:dupont` and `ex:frobenius-line` beyond the
  concrete identities recorded in `Pcf/Examples/CharP.lean`.
## G. Theorem `thm:bounding` derived (2026-10-04): the inputs, side by side with the Stacks text

Human direction (Taylor Dupuy, 2026-10-04): "We need [the bounding theorem's conclusion] to
follow from the ZN purity and Abhyankar. ZN-regularity and Abhyankar are good to assume."
`lean/Pcf/Bounding/` does this. The conclusion of Theorem `thm:bounding` on an affine chart —
the restriction `R/(a) → S/𝔭` is étale at every prime of `S/𝔭` — is the theorem
`Pcf.BoundingChart.isEtaleAt_restriction`. Its inputs are the chart data (Step 0's standing
hypotheses) and two classical theorems, stated as `Prop`s about rings in
`Pcf/Stacks/Purity.lean` and `Pcf/Stacks/Abhyankar.lean`. Their interfaces were checked
against the Stacks text on 2026-10-04 and their tag-by-tag proof spines were rechecked on
2026-10-09; the authors' private research note `2026-10-09-pcfawd-completeness/stacks-tag-proof-spine.md` records the exact
dependency map. The
three standard facts used by the derivation are proved. Nothing valued in `KummerWitness`
or `UnramifiedWitness` survives as a field.

### G.1 The two theorem-level inputs

| ID | Lean | Stacks | Verdict |
| --- | --- | --- | --- |
| G1 | `Pcf.Stacks.ZariskiNagataPurity R S`: for `Spec S → Spec R` with `R`, `S` Noetherian and `S` of finite type, every prime `w` satisfying `Pcf.Stacks.ZariskiNagataPurityHypothesesAt R S w` has `Pcf.Stacks.HasZariskiNagataPurityAt R S w`.  The input structure says that `S_w` is an integrally closed domain, `R_{w∩R}` is regular local, `S` is quasi-finite at `w`, `ht w = ht (w ∩ R) ≥ 1`, and `S` is unramified over `R` at every `w' ≤ w` of height `1`; the conclusion is étaleness at `w`. | **0BMB**: `f : X → Y` locally Noetherian, `x ∈ X`, `y = f(x)`; (1) `𝒪_{X,x}` normal, (2) `𝒪_{Y,y}` regular, (3) `f` quasi-finite at `x`, (4) `dim 𝒪_{X,x} = dim 𝒪_{Y,y} ≥ 1`, (5) for `x' ⤳ x` with `dim 𝒪_{X,x'} = 1`, `f` unramified at `x'`. Then `f` étale at `x`. | **Faithful** (the affine special case). `x' ⤳ x` is `w' ≤ w` (`PrimeSpectrum.le_iff_specializes`); "normal" is integrally closed domain; `dim 𝒪_{X,x}` is `Ideal.height`; "quasi-finite at `x`" in Stacks presupposes finite type, so `Algebra.FiniteType R S` is a premise alongside `Algebra.QuasiFiniteAt`; `IsUnramifiedAt`/`IsEtaleAt` are the local-ring forms, which for finite-type algebras over Noetherian rings are the Stacks meaning. |
| G2 | `Pcf.Stacks.AbhyankarLemma R S a`: if `R` is Noetherian, `a` a nonzerodivisor, `R/(a)` regular, `S` finite over `R` and étale at every prime not containing `a`, `S` the integral closure of `R` in `S_a`, and every positive integer invertible in `R`, then every prime `y ∋ a` satisfies `Pcf.Stacks.HasAbhyankarStandardCoverAt R S a y`.  This names an étale `R`-algebra `R'` with a prime over `y`, Noetherian, with `a` a nonzerodivisor in `R'`, `R'/(a)` regular, and `Pcf.Stacks.IsFiniteDisjointUnionOfStandardTameCovers R' (R' ⊗_R S) a`, i.e. `R' ⊗_R S ≅ ∏ᵢ R'[zᵢ]/(zᵢ^{eᵢ} − uᵢ a)` as `R'`-algebras, `eᵢ ≥ 1` invertible in `R'`. | **0EYG**: `X` locally Noetherian, `D ⊂ X` effective Cartier and regular, `Y → X ∖ D` finite étale and tamely ramified over `X` in codim 1 ⟹ étale locally on `X`, `Y → X` is a finite disjoint union of standard tamely ramified morphisms. **0EYH**: the normalization `Y'` of `X` in `Y` is finite locally free and étale locally on `X` a finite disjoint union of `Spec(A[x]/(x^e − f)) → Spec(A)`, `A` Noetherian, `f` a nonzerodivisor, `A/fA` regular, `e ≥ 1` invertible in `A`. | **Weaker** than 0EYG + 0EYH. Weaker because: (i) the premise "tamely ramified in codimension 1" is replaced by the stronger "every positive integer is invertible" (characteristic zero, the manuscript's standing hypothesis); (ii) the conclusion allows units `uᵢ` (the manuscript's form; 0EYH has `uᵢ = 1`); (iii) only points of `D` are covered; (iv) "finite étale over `X ∖ D`" is written pointwise, which for a finite algebra over a Noetherian ring is equivalent. The local-domain consequence used in Step 3 is derived from the regularity conclusion by the proved Tag 00NP theorem. |

**Could either be equivalent to the conclusion?** No, and for a reason visible in the types:
neither Prop mentions `𝔭`, the quotient `S/𝔭`, or the map `R/(a) → S/𝔭`. Both are statements
about the cover `R → S` alone. The conclusion is about a different ring map. Moreover both
are *true theorems* (special cases of the cited tags), so assuming them assumes nothing false,
and `Pcf.Stacks.ZariskiNagataPurity.of_etale` shows purity is satisfied by any étale cover
with no information about any divisor. The self-check required by the task — try to prove the
conclusion from each input alone — fails structurally: from G1 alone one reaches Step 1
(`Pcf.BoundingChart.isEtaleAt_of_notMem`, étaleness of `S` over `R` off `a`) and nothing about
`S/𝔭`; from G2 alone one cannot even discharge G2's premise "étale off `a`", which only G1
supplies, and G2's conclusion is a decomposition of `R' ⊗_R S`, which reaches the restriction
only through Step 3 (`Pcf.LocalModel.quotientMap_bijective`, `radical_span_algebraMap_eq_span_root`)
and Step 4 (`Pcf/Bounding/LocalStructure.lean`), both proved.

### G.2 The three standard facts

| ID | Lean | Stacks | Verdict |
| --- | --- | --- | --- |
| G3 | `Pcf.Stacks.isReduced_of_etale_of_isDomain`: an étale algebra over a **domain** is reduced. | **033B**: `φ : R → S` smooth, `R` reduced ⟹ `S` reduced. | **PROVED** (`Pcf/Bounding/Reduced.lean`), for the case used: the étale algebra is flat, so it injects into its base change to the fraction field, which is étale over a field and hence reduced (Mathlib `Algebra.FormallyUnramified.isReduced_of_field`). Used once: the base change `S/𝔭 → (R' ⊗_R S)/𝔭` of the integral `A ∩ V` is reduced, Step 3's "`T` is reduced because `V' → V` is étale". |
| G4 | `Pcf.Stacks.EtaleLocalOnSource`: for all finitely presented `A → B` and étale `B → B'`, if `A → B'` is étale at every prime and `ξ ∈ Spec B` is under some prime of `B'`, then `A → B` is étale at `ξ`. | **036W**: "`f` is étale" is étale local on the source; with **03WT** (étale morphisms are open) for the passage from a covering of the open image to the point. | **PROVED; weaker** (`Pcf.Stacks.etaleLocalOnSource`), in the finite-presentation pointwise case used by the chart. The proof shrinks the open image of `Spec B' → Spec B` around `ξ` to a basic open, localizes both rings, proves the localized map faithfully flat from surjectivity on spectra, descends flatness by tensor associativity and formal unramifiedness through Kähler differentials, and recombines these with finite presentation. |
| G5 | `Pcf.Stacks.ExistsPrimeOverBoth`: for all `R → S`, `R → T`, primes `p ⊂ S`, `q ⊂ T` over the same prime of `R` lie under a common prime of `T ⊗_R S`. | **01JT**: points of `X ×_S Y` ↔ quadruples `(x, y, s, 𝔭)` with `𝔭` a prime of `κ(x) ⊗_{κ(s)} κ(y)`, a nonzero ring. | **PROVED** (`Pcf.Stacks.existsPrimeOverBoth`, `Pcf/Bounding/FibreProduct.lean`) from Mathlib's `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback` and `pullbackSpecIso`. Used once: "choose a point `ξ'` of `T` over `ξ`". |

G4 is universally quantified over the rings of a universe and has now been proved in the
finite-presentation form used by the chart. Its statement cannot encode the chart's
conclusion: it mentions neither `a` nor `𝔭` nor either quotient ring.

### G.3 What is proved in `Pcf/Bounding/`

| Manuscript | Lean | Status |
| --- | --- | --- |
| Step 1 | `Pcf.BoundingChart.isEtaleAt_of_notMem` | proved from G1 and the chart's standing hypotheses; on the preferred local route, `Pcf.isEtaleAt_height_zero_of_charZero_of_integral` derives the generic-point case from finiteness, dominance, and characteristic zero |
| Step 2 | `Pcf.BoundingChart.exists_standardPieces` | G2 applied; its seven premises discharged by the chart and Step 1 |
| `eq:standard-piece`: `(C/aC)_red = C/zC` | `Pcf.LocalModel.radical_span_algebraMap_eq_span_root` | proved: `√(aC) = (z)` when `R/(a)` is reduced |
| Step 3, `V(z) → V(a)` an isomorphism | `Pcf.LocalModel.quotientMap_bijective` | proved (the canonical map; this is `restrictionMap_bijective`) |
| Step 3, the dimension count | `Pcf.Bounding.mem_minimalPrimes_span_of_mem_minimalPrimes_map` | proved without dimensions: a minimal prime over `𝔭C` is minimal over `aC`, by going down for flat maps (Mathlib `Algebra.HasGoingDown.of_flat`) and incomparability in quasi-finite fibres (Mathlib `Algebra.QuasiFiniteAt.eq_of_le_of_under_eq`) |
| Step 3, "union of connected components" | `Pcf.Bounding.exists_mul_mem_ker_of_mem_minimalPrimes_ker` | proved at a point: a minimal prime over `(z)` vanishes locally where the local ring of `R'/(a)` is a domain |
| Step 4, `T → D'` étale at `ξ'` | `Pcf.Bounding.isLocalization_of_localStructure`, `formallyEtale_of_localStructure`, `Pcf.BoundingChart.isEtaleAt_quot_of_pieces` | proved: the local ring of the base-changed restriction is a localization of `R'/(a)` |
| the piece through a point | `Pcf.Bounding.exists_isUnit_evalRingHom_single`, `exists_lift_of_isUnit_single`, `isLocalizationAway_evalRingHom` | proved |
| Step 4, descent to `g` | `Pcf.BoundingChart.isEtaleAt_restriction` | proved from the above plus G4 and G5, both proved; G3 (proved) is used inside |
| concrete codimension-one `crit₁` of the chart restriction | `Pcf.affineNonEtaleLocus`, `Pcf.BoundingChart.affineNonEtaleLocus_restriction_eq_empty` | proved: `affineNonEtaleLocus` is definitionally non-étaleness at a height-one prime, so the chart theorem makes it empty |
| local chart at the generic point of `E ⊂ B` | `Pcf.exists_generator_map_atPrime_regular_dim_two`, `Pcf.mem_nonZeroDivisors_of_ringKrullDim_eq_two_of_quotient_eq_one`, `Pcf.isEtaleAt_height_zero_of_charZero_of_integral`, `Pcf.LocalBoundingChart.ofFiniteNormalLocalizationOfDivisors`, `Pcf.LocalBoundingChart.toBoundingChart`, `Pcf.isIntegralClosure_localizationAway_of_finite_of_integrallyClosed`, `isEtaleAt_restriction`, `affineNonEtaleLocus_restriction_eq_empty` | proved from a finite dominant normal algebra, honest target/source height-one divisor ideals, a normal two-dimensional regular ambient stalk, and a one-dimensional regular divisor stalk; the canonical localized cover, selected minimal component, local equation, nonzerodivisor property, generic-point étaleness, tameness over `ℚ`, low-dimensional regular-ring promotions, cover Noetherianity, finite-map height equality, and normalization inside the principal localization are theorems |
| localization presentation and actual stalk map of the affine quotient chart | `Pcf.LocalBoundingChart.toSchemeStalkBoundingLocalizationPresentation`; `Pcf.SchemeStalkBoundingLocalizationPresentation.toSchemeStalkBoundingPresentation`, `formallyEtale` | proved: the quotient-ring algebra maps, their localization properties and their square construct the two coordinate isomorphisms and the arrow isomorphism, across which the pointwise purity--Abhyankar conclusion is transported; the literal affine quotient uses the canonical structure-sheaf localizations and functoriality of `Spec` |
| actual affine divisor quotient and its global-to-local stalk comparison | `Pcf.LocalBoundingChart.toGlobalQuotientSchemeStalkBoundingChart`; `toGlobalQuotientSchemeStalkBoundingLocalizationPresentationOfHeightOneDivisorsAt` | proved: for primes `D ≤ q` and `P ≤ Q`, with `Q` over `q`, the actual stalk arrow of `Spec(S/P) → Spec(R/D)` at `Q/P` is isomorphic to the canonical localized chart arrow; the composite constructor derives the exact dynamics-facing presentation from the finite dominant normal algebra, honest height-one divisors, pointed avoidance of every other branch divisor, purity and Abhyankar |
| closed-subscheme affine quotients to actual stalks | `Scheme.IdealSheafData.quotientPoint`, `quotientStalk_isLocalization`, `quotientAppLE`, `comap_quotientPoint_quotientAppLE`, `stalkMap_comp_quotientStalkAlgebraMap`, `quotientAppLE_subschemeMap_eq_quotientMap`; `Pcf.closedSubschemeStalkBoundingLocalizationPresentation`, `closedSubschemeStalkBoundingLocalizationPresentationOfAmbientMap`, `affineIdealSheaf_le_map_of_localBoundingChart`, `affineIdealSheafStalkBoundingLocalizationPresentation`, `exists_principal_comap_affineBasicOpen_of_atPrime_regular_dim_two` | proved: canonical closed-subscheme section quotients localize to the actual stalks; their induced quotient map contracts the selected prime and commutes with the actual stalk map; for a morphism induced from the ambient schemes it is exactly the ordinary quotient of the ambient section map; on affine ambient schemes, the Step 0 regular local hypotheses produce the target principal equation, after which the chart derives the sheaf containment, restricted morphism, and complete dynamics-facing localization presentation |
| the étale conclusion for the dynamics | `Pcf.PCFSetupChart.notMem_nonEtaleBranch_iterate`; corrected two-carrier route `Pcf.NormalizationPCFSetupChart.notMem_nonEtaleBranch_iterate`, `normalized_isPCF`, `normalized_isPCF_of_iterate` | proved from the chart link A6; the corrected PCF transfer uses an explicit finite-fiber normalization map |
| the étale conclusion with actual divisors and stalk-defined `crit₁` | `Pcf.SchemeNormalizationPCFSetupChart.notMem_nonEtaleBranch_iterate`, `restriction_isNonEtaleBranchPCF`, `normalized_isPCF` | proved from A6s, purity and Abhyankar; no field states or implies the critical-to-chart non-étaleness implication |
| the invariant-divisor conclusion from the ambient endomorphism | `Pcf.InvariantDivisorSchemeNormalizationPCFSetup.toSchemeNormalizationPCFSetupChart`, `notMem_nonEtaleBranch_iterate`, `restriction_isNonEtaleBranchPCF`, `normalized_isPCF`, `normalized_isPCF_of_iterate` | A6s is constructed from the actual restricted iterate and A6i; the local equation uses the exact dimension-two theorem, so the only external local covering inputs are G1 and G2 |

Tameness of the `eᵢ` is consumed only inside G2; Steps 3–4 hold for any `e ≥ 1`
(`Pcf.BoundingChart.isEtaleAt_quot_of_pieces` takes `e i ≠ 0` only).

### G.4 The chart link A6, and exactly what it is worth

`Pcf.PCFSetupChart` is `Pcf.NonEtalePCFSetup` with `notMem_nonEtaleBranch_iterate` replaced by `chart`: for each `m ≥ 1`,
good `Q`, and `Q'` over `Q`, a `Pcf.BoundingChart` and a point `ξ` representing `Q'`, with
`Q' ∈ crit₁(gᵐ) → ¬ IsEtaleAt (R/(a)) ξ`. `Pcf.PCFSetupChart.notMem_nonEtaleBranch_iterate` then derives `notMem_nonEtaleBranch_iterate`.
`Pcf.NormalizationPCFSetupChart` has the same chart link on the unnormalized carrier but
keeps the normalized ramification carrier separate; its `normalized_isPCF` theorem is the faithful
normalization conclusion.

`Pcf.LocalBoundingChart` is now the preferred geometric source of that affine chart.  It
uses the local ring of the ambient variety at the codimension-two point and the local ring
of `B` there; `toBoundingChart` proves the regular-ring fields required by Steps 1–4.  Thus
A6 no longer requires choosing a regular affine neighborhood.  It still requires the
scheme/stalk construction and, crucially, the identification of the actual divisor and
non-étale point with the abstract dynamics.

The new `Pcf.SchemeNormalizationPCFSetupChart` is the preferred replacement for this
legacy interface. Its unnormalized carrier is literally `SchemeDivisorPoint A`, and its
`Pcf.SchemeNormalizationUnnormalizedDynamics` has no `nonUnramifiedLocus` or `nonEtaleLocus` field: the loci for `g ^ m`
unfold to failure of formal unramifiedness and formal étaleness of `(g ^ m).stalkMap`.
Its `chart` field returns a
`SchemeStalkBoundingLocalizationPresentation`, which contains only local algebra, the
natural quotient-ring algebra maps to the actual stalks, their localization properties,
and their commutative square. The coordinate and arrow isomorphisms are derived.
`SchemeNormalizationPCFSetupChart.notMem_nonEtaleBranch_iterate` is therefore a genuine proof by contradiction
between the definition of `crit₁` and the formal étaleness derived from purity and
Abhyankar.

For `Spec (S/p) → Spec (R/(a))`, the localization presentation is a theorem
(`LocalBoundingChart.toSchemeStalkBoundingLocalizationPresentation`). The finite normal
localized cover, source divisor, minimal-prime condition, generic-point étaleness,
tameness and codimension-one unramifiedness are constructed by
`LocalBoundingChart.ofFiniteNormalLocalizationOfHeightOneDivisorsAt` from literal pointed
branch avoidance. The affine quotient and closed-subscheme extraction constructors then
derive the section algebra, canonical primes, quotient morphism, ambient/divisor stalk
coordinates, and actual stalk comparison from the ambient finite dominant morphism.
`pointClosureIdealSheaf` constructs the two reduced divisor ideals and their restricted
morphism.

The exact dimension-two constructor
`imageDivisorCartierDataAtOfRegularDimTwo` transports regularity from the actual ambient
and divisor stalks and applies `exists_generator_map_atPrime_regular_dim_two`; hence it
does not require a UFD instance or Stacks 0AG0/0AGA. The composite
`invariantClosureStalkBoundingLocalizationOfCorrectionAt` also proves the formerly missing
global identification: `invariantClosureMap_iterate` identifies the categorical iterate
of the actual invariant-divisor restriction with the point-closure map of the ambient
iterate, and the specified source/target points contract correctly. Finally,
`InvariantDivisorSchemeNormalizationPCFSetup.toSchemeNormalizationPCFSetupChart`
translates the abstract good-point hypotheses through its literal A6i `localData` field
and constructs A6s for the dynamics. Thus A6s remains a useful generic interface, but it
is a theorem rather than an assumption on the actual invariant-divisor route.
For actual closed subschemes, the quotient-to-stalk localization and stalk square are now
theorems, so no separate identification of a closed-immersion stalk kernel with a
localized defining ideal is required. `Scheme.Hom.stalkQuotientKerEquiv` still gives the
canonical quotient by the kernel of any surjective stalk map, but it is auxiliary rather
than an open A6s obligation. The section-level square is also no longer an obligation:
`quotientAppLE_subschemeMap_eq_quotientMap` derives it from the actual ambient morphism,
and `closedSubschemeStalkBoundingLocalizationPresentationOfAmbientMap` reduces the
coordinate input to equalities of the two defining ideals. On affine ambient schemes,
`affineIdealSheafStalkBoundingLocalizationPresentation` reduces it once more to the
target principal equation; that equation is itself derived by
`exists_principal_comap_affineBasicOpen_of_atPrime_regular_dim_two` from the Step 0 local
regularity and dimension hypotheses. The older open-restriction presentation remains available,
but is no longer the dynamics-facing requirement because a spectrum of a local ring is
not generally an open neighbourhood in the original scheme.

**Honesty check.** On the legacy abstract carrier `PA`, no rings are attached (A1–A5), so
the old A6 link is
necessarily supplied by whoever supplies the data, and it is exactly as strong as `notMem_nonEtaleBranch_iterate`
*relative to the derived theorem*: given `notMem_nonEtaleBranch_iterate`, `chart` could be discharged for every `Q'`
with a trivial chart (the identity cover `ℚ[x] → ℚ[x]`, `a = x`, satisfies every field of
`Pcf.BoundingChart`); given `chart`, `notMem_nonEtaleBranch_iterate` follows. This is **not** the situation the reviews
of §B.2 refuted: there, the supplier chose the algebra to which Abhyankar's lemma was applied,
and no geometry crossed. Here the algebra is the chart's own `R → S`, G1 and G2 are applied
to *it*, and the only thing left to the supplier is to say which chart represents which
abstract prime. What has changed is where the mathematics lives — Steps 1–4 are theorems — and
not the trust boundary of that abstraction. The actual invariant-divisor route is
different: its carrier is `SchemeDivisorPoint`, `crit₁` is defined by the actual stalk
map, the restriction and its iterates are identified as concrete scheme morphisms, and
the chart is constructed from A6i. A6i contains G1/G2 and ordinary Step 0 facts, but no
field from which formal étaleness or `notMem_nonEtaleBranch_iterate` follows without G1/G2. The adversarial record
at the authors' private research note `2026-10-04-divisor-bridge/fidelity.md` checks these fields one by one.

### G.5 Removed

`Prop41Data.over`, `Prop41Data.ram`, `Prop41Data.standardForm`, `Prop41Data.branch`,
`Prop41Data.notMem_branch`, `Prop41Data.branch_subset_bound`, `Prop41Data.finite_branch`,
`PcfGeometry.standardForm`, `PcfGeometry.key` (the theorem); `PCFGeometry.toPCFSetup`,
`restriction_isPCF`, `restriction_isPCF_of_iterate` and `PCFGeometry.ofPurityData` / `restriction_isPCF_of_purityData` now take
the bounding conclusion as an explicit argument. The cofinite witness
(`Pcf/Examples/CofiniteWitness.lean`) supplies it directly (`Pcf.Examples.notMem_branch_iterate_restrictionDynamics`), with
no `KummerWitness`.

## F. Status of the formalization

* `Pcf/Unnormalized.lean` — **LEAN-PROVED** given U1–U6; Theorem `thm:normal-invariant` in
  its `1`-PCF form via `Pcf.NonEtalePCFSetup.restriction_isNonEtaleBranchPCF` is **CONDITIONAL** on A1–A5, B1–B4 and U1–U6.
* `Pcf/Examples/Pinched.lean` — ring-level statements **LEAN-PROVED**; the dynamical
  statements are **CONDITIONAL** on `o ∈ crit₀(g)` (a hypothesis or a stipulated field).

Using the vocabulary of the formalization-evidence contract:

* `Pcf/Dynamics.lean`, `Pcf/Restriction.lean`, `Pcf/LocalModel.lean`,
  `Pcf/Examples/*` — **LEAN-PROVED**: they compile, and `#print axioms`
  reports only standard logical axioms.
* Theorem `thm:normal-invariant` via `Pcf.PCFSetup.restriction_isPCF` — **CONDITIONAL** on A1–A5 and B1–B5,
  because those are fields of the structure it takes as input.
* Theorem `thm:normal-invariant` via `Pcf.PCFGeometry.restriction_isPCF` — **CONDITIONAL** on A1–A5, B1, B2 and
  P1–P6. B3 and B4 are genuinely discharged; B5 is *restated* as P2, not discharged.
* Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` and (3) — the finiteness half is **proved**; the properness half
  is assumed (P5, P6).
* Theorem `thm:bounding` on an affine chart — **LEAN-PROVED, CONDITIONAL** on the chart's
  standing hypotheses, G1 (Zariski–Nagata purity, Tag 0BMB), G2 (Abhyankar's lemma, Tags
  0EYG/0EYH): `Pcf.BoundingChart.isEtaleAt_restriction` (§G). Tags 033B, the needed
  finite-presentation case of 036W, and 01JT are proved along the way.
* Theorem `thm:normal-invariant` via `Pcf.PCFSetupChart.restriction_isNonEtaleBranchPCF` — **CONDITIONAL** on
  A1–A6, B1–B4, U1–U5, G1 and G2. The former P2/U6 primitive is derived.  The corrected
  two-carrier conclusion is `Pcf.NormalizationPCFSetupChart.normalized_isPCF`; its finite-fiber PCF
  transfer is proved. The actual finite-type constructor supplies the codimension theorem,
  divisor map and finite fibers once the normalization morphism and lifted map are given.
* Theorem `thm:normal-invariant` via `Pcf.SchemeNormalizationPCFSetupChart.normalized_isPCF` —
  **CONDITIONAL** on the supplied finite commuting normalization and lifted maps,
  generic-stalk birationality, A5, A6s, characteristic zero at the generic stalk, G1 and
  G2. U1–U5 are proved on this finite-birational route. Unlike A6,
  A6s contains no implication equivalent to `notMem_nonEtaleBranch_iterate`: `crit₁` is the actual stalk-defined
  locus and the local chart supplies only concrete local algebra, localization properties,
  and a quotient-ring map square. The coordinate and arrow comparisons are derived.
  The canonical finite normal localized cover and its selected source divisor are now
  constructed from the affine algebra, and characteristic-zero branch-index support is
  transported to codimension-one unramifiedness. Its comparison with the actual affine
  quotient stalks is proved, and the branch input has the exact pointed-avoidance form of
  Step 0. The canonical affine data are now extracted from an actual scheme morphism and
  closed-subscheme point; its ambient and divisor local rings are identified with the
  actual stalks, and the local equation is derived. The reduced divisor ideal sheaves,
  their restricted morphism, and their affine prime/height facts are now constructed from
  the source divisor point, whose target divisor image is also proved. The selected-point
  constructor additionally chooses the source preimage and derives divisor codimension
  one. The quantifier-faithful specified-point constructor instead keeps the requested
  source preimage and derives regularity and pointed avoidance from the literal Step 0
  exclusions. This generic route still accepts A6s as a field.
* Theorem `thm:normal-invariant` via
  `Pcf.InvariantDivisorSchemeNormalizationPCFSetup.normalized_isPCF` — **CONDITIONAL** on the
  ordinary properness fields, the supplied finite commuting normalization and lifted maps,
  generic-stalk birationality, characteristic zero at the generic stalk, A6i, G1 and G2.
  U1–U5 are proved when `restriction` is built by the finite-birational constructor. Unlike the preceding
  generic route, it constructs A6s. The local equation is derived by the exact
  dimension-two regular-local theorem, the actual invariant-divisor restriction and all
  iterates are identified with the ambient point-closure maps, and the specified source
  point is preserved. `ofActualAmbient` forces the ambient `DivisorDynamics` and fixed divisor to
  be the ones belonging to `f` and `A`. No regular-local-UFD theorem and no
  conclusion-shaped chart field is assumed.
* Theorem `thm:general` via `Pcf.pcfAllTheWayDown_scheme` — **LEAN-PROVED,
  CONDITIONAL** on its stated finite-type characteristic-zero geometry, ambient
  normalized PCF, and `InvariantDivisorCoveringHypotheses`.  The latter consists
  only of `Pcf.Stacks.ZariskiNagataPurity` and
  `Pcf.Stacks.AbhyankarLemma` on the actual local rings of every relevant
  iterate.  Tag 00NP supplies the needed local-domain conclusion from the
  regularity clause of Abhyankar.  The
  finite singular correction, canonical finite normalization and lift,
  two-way normalization PCF equivalence, periodic divisor lift, finite cover of
  reduced divisor closures, cover descent, and positive-iterate invariance are
  constructed inside the formalization.
* The comparison of the reduced-fibre and ramification-index branch definitions —
  **LEAN-PROVED** by `Pcf.mem_schemeReducedFiberBranch_iff`; its normalized form is
  `Pcf.schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch`.  The proof
  uses Mathlib's intrinsic `Scheme.Hom.fiber`, not a replacement fibre predicate.
* The recursive scheme-level assembly of `cor:pcfawd` — **LEAN-PROVED TO EVERY FINITE
  DEPTH** by `Pcf.schemePCFAllTheWayDownAtDepth_of_cover` and
  `Pcf.schemePCFAllTheWayDown_of_cover`.  Its recursive covering input contains the
  local purity/Abhyankar packages at each actual divisor closure and no PCF conclusion.
  The source-facing theorem `Pcf.pcfAllTheWayDown_charZero` removes this intermediate
  input: `Pcf.schemePCFCoveringAtDepthOfLocalTheorems` builds it recursively from one
  universe-wide pair of the purity and Abhyankar statements.
* The numerical termination assertion in `cor:pcfawd` — **LEAN-PROVED** by
  `Pcf.SchemeDivisorFlag.length_le_topologicalKrullDim` and
  `Pcf.SchemePCFDescentBranch.isEmpty_succ_of_topologicalKrullDim_le`.  Every actual
  recursive branch gives a strict specialization chain in the initial scheme, so a
  natural dimension bound `n` permits at most `n` restrictions.
  `Pcf.schemePCFAllTheWayDown_of_cover_to_dimension` consequently needs recursive
  purity/Abhyankar covering data only through depth `n`, not at every finite depth.
* The global form of Zariski–Nagata purity, given the local form — **PROVED**
  (`Pcf.PurityData.codim_eq_one`).

Thus the one-divisor geometric content of "PCF All the Way Down" is machine-checked as
`Pcf.pcfAllTheWayDown_scheme`, its recursive actual-scheme assembly is checked as
`Pcf.schemePCFAllTheWayDownAtDepth_of_cover`, and the manuscript-facing characteristic-zero
result is `Pcf.pcfAllTheWayDown_charZero`.  The result is conditional exactly because
purity and Abhyankar are supplied as universal local theorems, not
because divisor dynamics, normalization, singular corrections, cover descent, or the
recursive PCF conclusion are postulated.  The recursion's numerical dimension bound is
proved from the actual point-closure chain and Mathlib's `topologicalKrullDim`.

Purity and Abhyankar's lemma themselves are **assumed**.  Stacks Tag 00NP is proved and
used to obtain the local-domain consequence from Abhyankar's regularity conclusion.
No part of purity or of the existence statement in
Abhyankar's lemma is proved here; the standard-model algebra after that existence
statement, including clauses 1–2 of Tag 0EYF, is machine-checked.
