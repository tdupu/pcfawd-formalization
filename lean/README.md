# Lean formalization of "PCF All the Way Down"

A Lean 4 + Mathlib formalization of `../latex/pcf.tex`.

| Field | Value |
| --- | --- |
| Lean | `4.34.0` |
| Mathlib | `v4.34.0` (rev `5ed296525643`) |
| Build | `lake build` from this directory |
| Assumed inputs | [AXIOMS.md](AXIOMS.md) |
| Provenance | [`../ai/ai-usage.md`](../ai/ai-usage.md), [`../ai/tokens.md`](../ai/tokens.md) |

## What is and is not claimed

This is a **conditional** formalization in the style of the `gq2` project: the
whole argument is machine-checked *down to a named list of interfaces to the
classical literature*, which are assumed rather than proved.

* **Proved in Lean.** The entire dynamical and combinatorial half of the paper:
  Lemma 3.2, Propositions 3.3, 3.4 and 3.5, Remark 2.5, Theorem 5.1 (= Theorem
  A), Corollary 5.2, Corollary 5.5, plus the algebraic core of Proposition 4.1
  Step 3, the fact that `k[t]` is the normalization of the cuspidal cubic's
  coordinate ring, and the computations behind Examples 4.4, 4.5, 6.1, 6.2
  and 7.4.
  Proposition 4.1's **finiteness** statements are also proved, and the *global*
  form of purity is derived from the *local* form exactly as the manuscript argues.
  **Half of Abhyankar's lemma** is proved: Stacks Tag 0EYF, that the standard tamely
  ramified model `R[y]/(y^e − u)` is étale over `R` when `e` is invertible and `u` is
  a unit, hence unramified at every prime (`Pcf/Abhyankar.lean`).
* **Assumed in Lean.** Zariski–Nagata purity (in a form *stronger* than Stacks Tag
  0BMB — see AXIOMS.md §B.2), **Abhyankar's structure theorem** (Stacks Tag 0EYG),
  lying-over, finiteness of the branch divisor, and the scheme-theoretic meaning of
  "prime", "ramification index" and "singular locus".

  On Proposition 4.1(2): it is still conditional, but on less than before. The
  hypothesis `standardForm` now asks for a `Pcf.KummerWitness` — a tame Kummer
  presentation `y^e = u`, which is what Abhyankar's lemma *outputs* — and the step
  from there to "ramification index `1`" is the theorem
  `Pcf.KummerWitness.eq_one`, proved via `Abhyankar.etale`. What remains assumed is
  Tag 0EYG, that the cover is étale-locally of that shape.

  An earlier version used `Pcf.UnramifiedWitness`, whose `bijective` field made the
  hypothesis **logically equivalent to its own conclusion**; this file and the
  manuscript claimed a derivation that did not exist. An adversarial review caught it,
  and the review is retained at
  `../ai/2026-09-21-prop41-formalization/adversarial-review.md`.
  `Pcf.nonempty_unramifiedWitness_iff` keeps that fact stated in Lean, and
  `Pcf.nonempty_kummerWitness_iff` records the analogous — and unavoidable —
  equivalence for the new interface, alongside `Pcf.KummerWitness.cubic`, a
  degree-`3` inhabitant built from `ℚ[y]/(y³ − 1)`.
  See [AXIOMS.md](AXIOMS.md). The two layers are joined:
  `Pcf.PcfGeometry.toPcfSetup` builds the structure Theorem A consumes with
  `sing_finite`, `meets_finite` and `key` proved, so `Pcf.PcfGeometry.res_pcf`
  reaches Theorem A assuming only purity, Abhyankar's structure theorem, lying over,
  and the properness of the three correction loci.

There is **no `sorry`, no `axiom`, no `admit` and no `native_decide`** in
`Pcf/`. The assumed inputs are structure fields, so `#print axioms` reports
only `propext`, `Classical.choice`, `Quot.sound` — read
[AXIOMS.md](AXIOMS.md) before drawing conclusions from that.

## Layout

```
lean/
├── Pcf.lean               ← root module, imports everything
├── Pcf/
│   ├── Dynamics.lean      ← §2–§3: divisorial dynamics, ramification of iterates
│   ├── Restriction.lean   ← §5: Theorem A and its corollaries
│   ├── Noetherian.lean    ← §4: primes of a Noetherian space; the finiteness engine
│   ├── Purity.lean        ← §4: Zariski–Nagata purity, local form ⟹ global form
│   ├── Ramification.lean  ← §4 Step 4: an isomorphism has ramification index one
│   ├── Geometry.lean      ← §4: Proposition 4.1, assembled and proved
│   ├── LocalModel.lean    ← §4 Step 3: the standard tame local model
│   ├── Abhyankar.lean     ← Abhyankar's lemma, Stacks Tag 0EYF (Mathlib-only)
│   ├── Audit.lean         ← `#print axioms` for every headline result
│   └── Examples/
│       ├── Squaring.lean  ← §6: Examples 6.1, 6.2; witness that the setup is inhabited
│       ├── CofiniteWitness.lean ← a complete `PcfGeometry` with genuine ramification
│       ├── Cusp.lean      ← §4: Examples 4.4, 4.5
│       └── CharP.lean     ← §7: Examples 7.1, 7.4 (the wild counterexample)
├── AXIOMS.md              ← axiom census: everything assumed
├── lakefile.toml, lean-toolchain, lake-manifest.json
└── .lake/                 ← build output, never tracked
```

## The design in one paragraph

The manuscript's §3 depends on a variety only through the set of its primes,
the pushforward of primes along `g`, and the ramification index at each prime.
`Pcf.DivDyn` packages exactly that. The `m`-th iterate `D.iter m` is defined by
`step := stepᵐ` and `ram := ∏_{i<m} ram (stepⁱ ·)`, which builds multiplicativity
of ramification in towers into the definition; Propositions 3.3–3.5 then become
theorems about finite products of natural numbers and forward orbits, and are
proved outright. `Pcf.PcfSetup` adds the data of Theorem 5.1 — a fixed prime
`A`, the restricted system on `A`, the finite sets `Sing` and `A ∩ E`, and the
conclusion of Proposition 4.1 for every iterate. The decisive point of the
paper, that the bounding set `Σ` does **not** depend on the iterate `m`, is
`Pcf.PcfSetup.branch_iter_subset_bound`, and Theorem A follows from it and the
orbit characterization of PCF.

## Statement-to-declaration map

| `pcf.tex` | Lean declaration | Status |
| --- | --- | --- |
| Definition 2.2, 2.3 (`Branch`) | `Pcf.DivDyn.branch` | modelled (char. 0 convention) |
| Definition 2.4 (`PCset`, PCF) | `Pcf.DivDyn.pcSet`, `Pcf.DivDyn.PCF` | modelled |
| Remark 2.5 (normalization) | `Pcf.DivDyn.pcf_of_finite_cover` | proved |
| Chains over `P₀` (§3) | `Pcf.DivDyn.IsChain`, `Pcf.DivDyn.exists_isChain_iff` | proved |
| Lemma 3.2 (padding) | `Pcf.DivDyn.IsChain.extend` | proved |
| multiplicativity in towers | `Pcf.DivDyn.iterRam_add` | proved (from the definition; see AXIOMS A4) |
| Proposition 3.3 | `Pcf.DivDyn.mem_branch_iter_iff` | proved |
| Proposition 3.4 | `Pcf.DivDyn.mem_branch_iter_succ` | proved |
| Proposition 3.5 | `Pcf.DivDyn.pcSet_iter`, `Pcf.DivDyn.pcf_iter_iff` | proved |
| §2, finiteness of `Branch(g)` | `Pcf.PurityData.finite_isPrime_subset_nonEtale` | proved, but *not wired in* — `DivDyn.branch_finite'` is still a field |
| §4, purity: local form ⟹ global form | `Pcf.PurityData.codim_eq_one` | proved |
| Proposition 4.1(1) | `Pcf.IsPrime.not_subset_sUnion`, `Pcf.not_subset_of_two_le_codim` | proved (`Sing(B)` properness assumed) |
| Proposition 4.1(1), finiteness | `Pcf.finite_isPrime_subset` | proved |
| Proposition 4.1(2) | `Pcf.Prop41Data.notMem_branch` | conditional on `standardForm` (= Stacks Tag 0EYG); the passage from the tame form is proved |
| Abhyankar's lemma, Stacks Tag 0EYF | `Abhyankar.etale`, `Abhyankar.ramificationIdx_eq_one` | **proved** |
| Proposition 4.1(2), Step 4 | `Pcf.KummerWitness.eq_one` | proved |
| Proposition 4.1(3) | `Pcf.Prop41Data.branch_subset_bound`, `Pcf.Prop41Data.finite_branch` | proved |
| Proposition 4.1, Step 3 (as a map) | `Pcf.LocalModel.restrictionMap_bijective` | proved |
| Proposition 4.1, Step 4's inference | `Pcf.Ramification.ramificationIdx_eq_one_of_bijective` | proved |
| purity | `Pcf.PurityData.localPurity` | **assumed**; stronger than Stacks 0BMB |
| Abhyankar's structure theorem | `Pcf.Prop41Data.standardForm` | **assumed**; Stacks Tag 0EYG. Tag 0EYF is no longer assumed — it is proved |
| Theorem A via geometry | `Pcf.PcfGeometry.res_pcf` | proved; `sing_finite`/`meets_finite` discharged, `key` restated |
| the join | `Pcf.PcfGeometry.toPcfSetup`, `Pcf.divDynOfGeometry` | proved |
| the join is inhabited | `Pcf.Examples.cofiniteGeometry`, `Pcf.Examples.resDyn_branch` | proved (toy space; see AXIOMS.md) |
| Example 4.4 (cusp) | `Pcf.Examples.Cusp` | normalization, parametrization, Jacobian and `B ∩ Z` proved; `Branch(g) = ∅` not stated (no scheme-level `Branch`) |
| Example 4.5 (quadric cone) | `Pcf.Examples.Cusp` | parametrization and restriction proved; normality/étaleness not formalized |
| Theorem 5.1 = Theorem A | `Pcf.PcfSetup.res_pcf` | proved from the above |
| Corollary 5.2 | `Pcf.PcfSetup.res_pcf_of_iter` | proved |
| Corollary 5.5 | `Pcf.pcf_descent`, `Pcf.PcfSetup.normalization_pcf` | proved |
| Example 6.1, 6.2 | `Pcf.Examples.squaringP1`, `Pcf.Examples.diagonalSquaring` | proved |
| Example 7.4 (wild) | `Pcf.Examples.CharP` | proved |

## Building

```sh
elan toolchain install $(cat lean-toolchain)     # first time only
lake exe cache get                               # Mathlib olean cache
lake build
```

`lake build` builds every module listed above; `lake env lean Pcf/<File>.lean`
checks a single file in a few seconds.
