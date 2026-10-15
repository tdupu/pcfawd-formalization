# Palomar submission — `PCF all the way down`

This directory is the **selected project** for a [Palomar registry](https://palomar-registry.org/)
submission. It is separate from Tau Ceti: nothing here depends on, or is meant for, Tau Ceti.

**Status: in preparation. Nothing has been submitted.** Submitting requires Taylor's
explicit go-ahead, given at the time and separately from any instruction to prepare.

## Layout

| Path | Role |
| --- | --- |
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Lake project. The proof development is the contained path dependency `../lean`; packages are shared from `../lean/.lake/packages`. |
| `PcfChallenge.lean` | The statement: Mathlib imports only. It restates every `Pcf` definition the compared theorem depends on, and leaves the theorem as `sorry`. |
| `PcfSolution.lean` | The proof: imports the `Pcf` development, which supplies `Pcf.pcfAllTheWayDown_charZero`. |
| `comparator.json` | Compares `Pcf.pcfAllTheWayDown_charZero`; permitted axioms are `propext`, `Quot.sound`, `Classical.choice`. |
| `formalization.yaml` | Palomar metadata (v0.4). Contains `TODO(Taylor)` items. |
| `../LICENSE` | Apache-2.0, at repository root as Palomar requires (matching the Lean file headers). |
| `../.github/workflows/palomar-preflight.yml` | Manually triggered Palomar preflight, pinned to PalomarSubmission `d4e41c1`. |

Submission parameters, for when the time comes:

- repository: **a new public repository `tdupu/pcf_public`**, not this private one (decided by
  Taylor 2026-10-15), at one full commit SHA. It needs `LICENSE` at its root, `lean/`,
  `palomar/`, and the preflight workflow. The paths below assume the same layout;
- project path `palomar`;
- Comparator configuration `palomar/comparator.json`;
- metadata `palomar/formalization.yaml`.

## Checklist

Requirements are from PalomarPolicy `CONTRIBUTING.md` and PalomarSubmission `README.md`,
read 2026-10-15. Palomar changes often, so re-read them before acting.

### Needs Taylor

- [ ] **Create the public repository `tdupu/pcf_public`** and decide what moves into it.
      Palomar accepts only public GitHub repositories, and `tdupu/pcf` stays private. The
      minimum is `LICENSE`, `lean/`, `palomar/`, the workflow, and whatever
      `formalization.yaml` cites: the manuscript and `ai/ai-usage.md`.
- [x] Authors of the formalization: all four (Taylor, 2026-10-15).
- [x] Automation account, review status, arXiv (Taylor, 2026-10-15): the code was built with
      `using-leanpowers` (`tdupu/agent-skills-public`), which builds on `CBirkbeck/mathlib-quality`;
      agents reviewed the statements; there is no arXiv identifier yet, so `latex/paper.tex`
      must ship in `pcf_public`.
- [ ] **One more statement-fidelity review** of the final `PcfChallenge.lean` against the
      manuscript (Taylor asked for this). Record the result in `review.notes`.
- [ ] Decide the submission relationship answer. Palomar records it permanently as a claim
      about the submitter: "I am a responsible author or maintainer", or "I have approval
      from one".
- [ ] Explicit authorization to submit, after reviewing the preflight report and the
      private Palomar review.

### Agent work

- [x] Apache-2.0 `LICENSE` at repository root.
- [ ] Lean toolchain `v4.35.0` (floor `v4.35.0-rc2`) with Mathlib `v4.35.0`. The toolchain
      must equal Mathlib's own `lean-toolchain` exactly. In progress on branch
      `toolchain-v4.35.0`.
- [ ] **Port every `.lean` file in the repository to the Lean module system.** Palomar
      requires a `module` header in every source file, at most 10,000 lines each; on
      2026-10-15, 175 of 177 files in `lean/Pcf` lacked one. This needs `public import`,
      exposed definitions where clients need bodies, then a rebuild.
- [ ] `PcfChallenge.lean`: restate the transitive closure of `Pcf` definitions used by the
      type of `Pcf.pcfAllTheWayDown_charZero`, verbatim and under the same names. Hard
      limit 1,000 lines / 100 KiB; Palomar warns above 300 lines / 32 KiB. The size of that
      closure has not been measured yet; if it is too large, the statement surface has to
      be redesigned.
- [ ] `PcfSolution.lean` and `lake-manifest.json` for this project.
- [ ] A passing local Comparator run. On macOS this uses "fake landrun", which is weaker
      evidence than Palomar's Linux sandbox.
- [ ] A passing preflight run: Actions → "Palomar preflight", which needs the repository to
      be public. Upstream issue PalomarSubmission#154 (open on 2026-10-15) reports that the
      preflight can skip verification steps.
- [ ] Re-derive the `project.description` abstract from the elaborated Challenge, and update
      `../lean/PALOMAR.md` (the claim manifest) to the new pins.

## Background

- `../lean/PALOMAR.md`: the claim manifest. It covers the informal-versus-formal half of a
  submission, with does-not-claim blocks for each entry.
- `../lean/PALOMAR-PROCESS.md`: notes from 2026-09-24 on how Palomar works. Superseded where
  it disagrees with this file.
- Palomar's only trusted Tau Ceti revision (`221bb56`, Lean `v4.31.0-rc2`) was below
  Palomar's own toolchain floor on 2026-10-15. The Challenge here imports Mathlib only, so
  this does not affect us.
