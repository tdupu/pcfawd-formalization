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
* **Assumed in Lean.** Proposition 4.1 itself — whose proof uses Zariski–Nagata
  purity and Abhyankar's lemma, neither of which exists in Mathlib — together
  with the finiteness statements of Proposition 4.1(1), the finiteness of the
  branch divisor, lying-over, and the scheme-theoretic meaning of "prime",
  "ramification index" and "singular locus". See [AXIOMS.md](AXIOMS.md).

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
│   ├── LocalModel.lean    ← §4 Step 3: the standard tame local model
│   ├── Audit.lean         ← `#print axioms` for every headline result
│   └── Examples/
│       ├── Squaring.lean  ← §6: Examples 6.1, 6.2; witness that the setup is inhabited
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
| Proposition 4.1(1) | `Pcf.PcfSetup.sing_finite`, `Pcf.PcfSetup.meets_finite` | **assumed** |
| Proposition 4.1(2) | `Pcf.PcfSetup.key` | **assumed** |
| Proposition 4.1, Step 3 | `Pcf.LocalModel` (see file) | proved |
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
