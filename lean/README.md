# Lean formalization of "PCF All the Way Down"

A Lean 4 + Mathlib formalization of parts of `../latex/paper.tex`.

| Field | Value |
| --- | --- |
| Lean | `4.34.0` |
| Mathlib | `v4.34.0` (rev `5ed296525643`) |
| Build | `lake build` from this directory |
| Assumed inputs | [AXIOMS.md](AXIOMS.md) |
| Manuscript | `../latex/paper.tex`, cited below **by `\label`**, never by number (see [HANDOFF.md](HANDOFF.md) §1 for why) |
| Provenance | [`../ai/ai-usage.md`](../ai/ai-usage.md), [`../ai/tokens.md`](../ai/tokens.md) |

## What the paper proves, and what this development proves

The paper's Theorem A (`thm:A` = `thm:general`) and Corollary `cor:pcfawd` say: every finite
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

**This development machine-checks layer 1 and layer 3's normal case, on an abstract carrier,
with layer 2 assumed.** Concretely:

* Everything in layer 1 that is a statement about sets of divisors, their pushforward and
  ramification indices is **proved**: `prop:iterates`, the orbit characterization of PCF,
  one direction of `lem:normalization`, and — new in this round — `cor:orbit-unnormalized`
  and the comparison `PC ⊆ PC₀ ⊆ PC₁` of `prop:loci-compare`/`def:pcf-unnormalized`.
* Theorem `thm:normal-invariant` is **proved from its inputs**: given the conclusion of
  `thm:bounding` for every iterate (a structure field), the finite set `Σ`, and PCF-ness of
  `f`, the restriction is `1`-PCF (`Pcf.PcfSetup1.res_pcf1`), hence `0`-PCF and PCF
  (`cor:normal-invariant-pcf`). The older `Pcf.PcfSetup.res_pcf` is the same theorem with the
  normalized (`e > 1`) form of the bounding conclusion. `cor:normal-preperiodic` is
  `Pcf.PcfSetup.res_pcf_of_iter` / `Pcf.PcfSetup1.res_pcf1_of_iter`.
* The **descent** along a chain of invariant divisors is a genuine induction
  (`Pcf.pcf_descent` = `Pcf.pcf_all_the_way_down`), *given a `PcfSetup` at each stage*.
* Theorem `thm:bounding` itself is **assumed** (`PcfSetup.key`, `PcfSetup1.key1`,
  `Prop41Data.standardForm`). Zariski–Nagata purity and Abhyankar's structure theorem are
  assumed. Clauses 1–2 of Stacks Tag 0EYF *are* proved (`Pcf/Abhyankar.lean`) but nothing
  consumes them.
* **Not formalized**: `thm:general` and therefore `thm:A`/`cor:pcfawd` *as stated* for
  non-normal `X` — the passage to the normalization (`lem:lift`'s finiteness, `lem:covers`,
  the periodic point of a finite set) has no Lean counterpart, and `Pcf.pcf_descent`
  asserts nothing about non-normal stages. Nothing constructs a `Pcf.DivDyn` from a
  morphism of schemes (assumptions A1–A5 in AXIOMS.md); "prime", "ramification index",
  "singular locus", `crit₀`, `crit₁` are abstract data.

There is **no `sorry`, no `axiom`, no `admit` and no `native_decide`** in `Pcf/`. The
assumed inputs are structure fields, so `#print axioms` (run for every headline result in
`Pcf/Audit.lean`) reports only `propext`, `Classical.choice`, `Quot.sound` — read
[AXIOMS.md](AXIOMS.md) before drawing conclusions from that.

Two adversarial reviews of this development are retained, at
`../ai/2026-09-21-prop41-formalization/adversarial-review.md` and
`../ai/2026-09-21-abhyankar-formalization/adversarial-review.md`. The first caught a claim
that the bounding theorem's per-divisor statement had been *derived*; the second caught a
claim that the assumption had been *weakened*. Both refutations are Lean theorems
(`Pcf.nonempty_kummerWitness_iff`, `Pcf.kummerWitness_iff_unramifiedWitness`,
`Pcf.PurityData.ofZariskiNagata_toZariskiNagata`).

## Layout

```
lean/
├── Pcf.lean                 ← root module, imports everything
├── Pcf/
│   ├── Dynamics.lean        ← sec:defs, sec:prelim: DivDyn, iterates (prop:iterates), lem:normalization
│   ├── Unnormalized.lean    ← app:other-defs, def:pcf-unnormalized: UnnormDyn, cor:orbit-unnormalized,
│   │                           thm:normal-invariant in 1-PCF form (PcfSetup1)
│   ├── Restriction.lean     ← sec:main: PcfSetup, thm:normal-invariant (PCF form), descent
│   ├── AllTheWayDown.lean   ← conj:pcfawd, abstract normal-case form, conjecture-facing names
│   ├── Noetherian.lean      ← lem:finitely-many: primes of a Noetherian space
│   ├── Purity.lean          ← thm:purity: local form ⟹ global form
│   ├── NonEtaleLocus.lean   ← the non-étale locus on Spec S is closed
│   ├── Wiring.lean          ← purity ⟹ branch_finite' for the restricted system
│   ├── SpectrumDynamics.lean← branch_finite' fully discharged on Spec S
│   ├── ZariskiNagata.lean   ← Stacks 0BMB restated (interderivable — discharges nothing)
│   ├── Ramification.lean    ← thm:bounding Step 4: an isomorphism has index one
│   ├── Geometry.lean        ← thm:bounding assembled: Prop41Data, PcfGeometry
│   ├── LocalModel.lean      ← thm:bounding Step 3 / eq:standard-piece
│   ├── Abhyankar.lean       ← Stacks 0EYF clauses 1–2 (Mathlib-only; not load-bearing)
│   ├── Audit.lean           ← #print axioms for every headline result
│   └── Examples/
│       ├── Squaring.lean    ← ex:squaring, ex:squaring-P2
│       ├── Pinched.lean     ← ex:pinched (ring level + divisorial dynamics on the nodal line)
│       ├── CofiniteWitness.lean ← a complete PcfGeometry with genuine ramification
│       ├── Cusp.lean        ← ex:cusp, ex:branch-singular
│       └── CharP.lean       ← ex:frobenius-line, ex:wild
├── AXIOMS.md                ← axiom census: everything assumed
├── HANDOFF.md               ← session handoff; §1 explains why labels, not numbers
├── lakefile.toml, lean-toolchain, lake-manifest.json
└── .lake/                   ← build output, never tracked
```

## The design in one paragraph

The manuscript's `sec:prelim` depends on a variety only through the set of its integral
effective divisors ("primes"), their pushforward along `g`, and the ramification index at
each. `Pcf.DivDyn` packages exactly that. The `m`-th iterate `D.iter m` has `step := stepᵐ`
and `ram := ∏_{i<m} ram (stepⁱ ·)`, which builds the tower formula of `lem:tower` into the
definition; `prop:iterates` then becomes a theorem about finite products and forward orbits.
`Pcf.UnnormDyn` adds the two unnormalized critical predicates `crit₀(gᵐ)`, `crit₁(gᵐ)` *as
data indexed by `m`*, because `lem:tower-unnormalized` gives only one-sided inclusions, which
are fields. `Pcf.PcfSetup`/`Pcf.PcfSetup1` add the data of `thm:normal-invariant` — the
invariant prime `A`, the restricted system, the finite sets `Sing` and `A ∩ E`, and the
conclusion of `thm:bounding` for every iterate. The decisive point, that `Σ` does **not**
depend on `m`, is `Pcf.PcfSetup.branch_iter_subset_bound` /
`Pcf.PcfSetup1.branch1_iter_subset_bound`.

## Statement-to-declaration map

Status words: **proved** (a Lean theorem with the paper's content, on the abstract carrier);
**assumed** (a structure field); **modelled** (a Lean definition standing for a paper
notion, with the identification itself an assumption); **not formalized**.

| `paper.tex` label | Lean declaration | Status |
| --- | --- | --- |
| `def:branch-loci` (1), (2): `branch₀`, `branch₁` | `Pcf.UnnormDyn.crit0/crit1`, `Pcf.UnnormDyn.branch0/branch1` | modelled: `crit_i(gᵐ)` is data indexed by `m`; `branch_i(gᵐ) := gᵐ(crit_i(gᵐ))` |
| `def:branch-loci` (3) = `def:crit-branch`: `branch` | `Pcf.DivDyn.branch` | modelled, as `{g(Q) : e(Q/g(Q)) > 1}` (char. 0, assumption A3) |
| `eq:branch-normalization` | — | not formalized (no `ν` on primes; one direction of its consequence is `pcf_of_finite_cover`) |
| `lem:lift` | `Pcf.DivDyn.step_surjective` (existence), `Pcf.DivDyn.IsChain.extend` (iterated) | existence **assumed** as a field; finiteness of the fibre **not formalized** |
| `lem:dictionary` | `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx` | one direction proved on `Spec S` (ramified ⟹ non-étale); the converse is assumption A3 |
| `def:pcf` | `Pcf.DivDyn.pcSet`, `Pcf.DivDyn.PCF`, `Pcf.DivDyn.pcf_iff_forall_orbit_finite` | modelled; orbit characterization proved |
| `lem:restriction` | — | not formalized (`step : P → P` presupposes it, assumption A1) |
| `def:pcfawd` | `Pcf.pcf_descent` hypotheses (a chain of `PcfSetup`s) | modelled for *normal* stages only; dimension not modelled |
| `conj:pcfawd` | `Pcf.pcf_all_the_way_down` | proved **in the abstract normal case** with `thm:bounding` assumed at every stage; the general case (`thm:general`) is **not formalized** |
| `prop:pcf-equiv` (1)⟺(2) | `Pcf.DivDyn.pcf_iff_forall_orbit_finite` | proved in the form "every branch prime has *finite orbit*"; the paper's word "preperiodic" (`∃ r s, fʳ⁺ˢ(D) = fʳ(D)`) is not stated, and (3) is not stated |
| `lem:tower` | `Pcf.DivDyn.iterRam_add`, `Pcf.DivDyn.branch_iter` | **not stated** for a general tower `g ∘ f`; multiplicativity of `e` in towers is the *definition* of `iterRam` (assumption A4), and the iterate consequence is `prop:iterates`(1) |
| `prop:iterates` (1) | `Pcf.DivDyn.mem_branch_iter_iff` | proved |
| `prop:iterates` (2) | `Pcf.DivDyn.mem_branch_iter_succ` | proved |
| `prop:iterates` (3), (4) | `Pcf.DivDyn.pcSet_iter`, `Pcf.DivDyn.branch_iter_subset_pcSet`, `Pcf.DivDyn.pcf_iter_iff` | proved |
| `lem:normalization` | `Pcf.DivDyn.pcf_of_finite_cover` | the direction "`f` PCF ⟹ `f̃` PCF" proved, with `ν` finite-to-one and `ν(branch f̃) ⊆ PC(f)` as hypotheses; the equality `PC(f) = ν(PC(f̃))` and the converse direction not formalized |
| `lem:covers` | — | **not formalized** |
| `lem:finitely-many` | `Pcf.finite_isPrime_subset`, `Pcf.PcfGeometry.sing_finite`, `Pcf.PcfGeometry.meets_finite` | proved on a Noetherian space, for `Pcf.IsPrime` (see AXIOMS.md §C on its fidelity) |
| `thm:bounding`, Step 0 (properness of `Σ`) | `Pcf.Prop41Data.interOther_ne_univ` etc. | **assumed** (P5, P6) |
| `thm:bounding`, étale conclusion | `Pcf.PcfSetup1.key1` | **assumed**, for every iterate |
| `thm:bounding`, `e > 1` conclusion (`branch(g) ⊆ Σ`) | `Pcf.PcfSetup.key`, `Pcf.Prop41Data.standardForm` ⟹ `Pcf.Prop41Data.branch_subset_bound` | **assumed**; `standardForm` is logically equivalent to its conclusion (`Pcf.nonempty_kummerWitness_iff`) |
| `thm:bounding`, Steps 1–2 (purity, Abhyankar) | `Pcf.PurityData.localPurity`, `Pcf.ZariskiNagata` (restated), `Abhyankar.*` | purity **assumed**; local ⟹ global form proved (`Pcf.PurityData.codim_eq_one`); Tag 0EYF (1)–(2) proved but not consumed |
| `thm:bounding`, Step 3 (`eq:standard-piece`) | `Pcf.LocalModel.restrictionMap_bijective`, `Pcf.LocalModel.quotientRootEquiv` | proved as a statement about `R[z]/(zᵉ − ua)` |
| `thm:bounding`, Step 4 | `Pcf.Ramification.ramificationIdx_eq_one_of_bijective` | proved |
| `ex:cusp` | `Pcf.Examples.Cusp.*` | parametrization, Jacobian `2u`, `k[t]` is the normalization, `B ∩ Z = {0}` proved; `branch(g) = ∅` and the new sentence `branch₀(g) = {(0,0)}` **not formalized** |
| `ex:branch-singular` | `Pcf.Examples.Cusp.coneParam`, `coneMap_restrict` | parametrization and restriction proved; normality, étaleness off the vertex, `branch(g) = {o}` not formalized |
| `thm:normal-invariant` (1-PCF) | `Pcf.PcfSetup1.res_pcf1` | proved from `key1`, `sing_finite`, `meets_finite`, PCF-ness of `f` |
| `cor:normal-invariant-pcf` | `Pcf.PcfSetup1.res_pcf0`, `Pcf.PcfSetup1.res_pcf`, `Pcf.PcfSetup.res_pcf` | proved |
| `cor:normal-preperiodic` | `Pcf.PcfSetup1.res_pcf1_of_iter`, `Pcf.PcfSetup.res_pcf_of_iter`, `Pcf.pcf_periodic_prime` | proved in the form "ambient system is `fˢ` and `B` is `fˢ`-invariant"; the reduction `B = fʳ(A)` is left to the supplier of the `PcfSetup` |
| `thm:general` (= `thm:A`) | — | **not formalized** (needs `lem:normalization` both ways, `lem:covers`, `lem:lift` finiteness) |
| `cor:pcfawd` | `Pcf.pcf_descent`, `Pcf.pcf_all_the_way_down` | abstract descent **proved** (a genuine induction) for a chain of `PcfSetup`s; each stage assumes `thm:bounding`; non-normal stages and dimension **not formalized** |
| `def:pcf-unnormalized` | `Pcf.UnnormDyn.pcSet0/pcSet1`, `Pcf.UnnormDyn.PCF0/PCF1` | modelled |
| `prop:loci-compare` (1) | `Pcf.UnnormDyn.crit1_finite` ⟹ `branch1_finite`, `branch0_finite` | **assumed** for `crit₁`; `crit₀` derived |
| `prop:loci-compare` (2) | `Pcf.UnnormDyn.crit_subset_crit0`, `crit0_subset_crit1` ⟹ `branch_subset_branch0`, `branch0_subset_branch1`, `pcSet_subset_pcSet0`, `pcSet0_subset_pcSet1`, `pcf0_of_pcf1`, `pcf_of_pcf0` | **assumed** on `crit`; the consequences for `branch`, `PC` and `i`-PCF proved |
| `prop:loci-compare` (3) | — | not formalized |
| `lem:tower-unnormalized` (1), (2) | `Pcf.UnnormDyn.crit0_tower`, `Pcf.UnnormDyn.crit1_tower` | **assumed**, for `g` and `h = gⁿ` only; the inclusions of branch loci and the failure of the converse not stated |
| `cor:orbit-unnormalized` | `Pcf.UnnormDyn.orbit_unnormalized_zero`, `orbit_unnormalized_one`, `orbit_unnormalized_one'` | proved (for all `n ≥ 0`) |
| `ex:pinched`, `f̃*R ⊆ R` | `Pcf.Examples.Pinched.sqMap_mem_of_mem` (indeed `sqMap_mem` for all `h`) | proved, any commutative ring |
| `ex:pinched`, `R = k[w, z², z(w−1), z³−4z]` | `Pcf.Examples.Pinched.adjoin_gens_eq` | proved, `k` a field of characteristic zero (uses only `4 ≠ 0`) |
| `ex:pinched`, `R_B` closed under `p ↦ p(z²)` | `Pcf.Examples.Pinched.comp_sq_mem` | proved |
| `ex:pinched`, orbit `4, 16, 256, …` distinct | `Pcf.Examples.Pinched.sqOrbit_injective`, `pt_four_pow_injective` | proved |
| `ex:pinched`, `g` PCF | `Pcf.Examples.Pinched.nodeDivDyn_pcf` (`PC(g) = {0}`) | proved on the modelled system `nodeDivDyn` (`k` algebraically closed, char. 0) |
| `ex:pinched`, `g` not `0`-PCF, not `1`-PCF | `Pcf.Examples.Pinched.pcSet0_infinite`, `pcSet1_infinite`; instance `nodeUnnormDyn_not_pcf0/1` | proved **given `o ∈ crit₀(g)`** as a hypothesis (or stipulated in the instance); the fibre-length computation is **not formalized** |
| `ex:pinched`, pushout, variety, normalization, finiteness of `f`, `f` not flat at `o`, `PC(f)` | — | not formalized |
| `ex:squaring` | `Pcf.Examples.squaringP1` | proved on the modelled system |
| `ex:squaring-P2` | `Pcf.Examples.diagonalSquaring` | proved on a reduced ambient model (see that file's caveat); `key` **proved** there, so `PcfSetup` is inhabited |
| `ex:wild` | `Pcf.Examples.CharP.orbit_infinite` | the critical orbit of `h(t) = t^{p+1} + c` is infinite: proved; the geometry of `F` not formalized |
| `ex:frobenius-line` | `Pcf.Examples.CharP.restriction_eq_frobenius`, `derivative_charPoly_ne_zero` | concrete identities proved; "index one but not étale" not formalized |
| `thm:purity` (Stacks 0BMB) | `Pcf.ZariskiNagata`, `Pcf.PurityData.localPurity` | **assumed** (restated with all hypotheses; interderivable with the old field) |
| `thm:abhyankar` (Stacks 0EYG) | `Pcf.Prop41Data.standardForm` | **assumed** |
| `lem:jacobian`, `ex:basilica`, `ex:dupont`, `ex:loci-compared`, `rem:why-normalized`, `q:sing-B` | — | not formalized |

## Building

```sh
elan toolchain install $(cat lean-toolchain)     # first time only
lake exe cache get                               # Mathlib olean cache
lake build
```

`lake build` builds every module listed above; `lake env lean Pcf/<File>.lean`
checks a single file in a few seconds.
