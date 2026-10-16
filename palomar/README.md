# Palomar submission — `PCF all the way down`

This directory is the **selected project** for a [Palomar registry](https://palomar-registry.org/)
submission. It is separate from Tau Ceti: nothing here depends on, or is meant for, Tau Ceti.

**Status: in preparation. Nothing has been submitted.** Submitting requires Taylor's
explicit go-ahead, given at the time and separately from any instruction to prepare.

## Layout

| Path | Role |
| --- | --- |
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Lake project. The proof development is the contained path dependency `../lean`; packages are shared from `../lean/.lake/packages`. |
| `PcfChallenge.lean` | The statement (300 lines, Mathlib imports only): the `Pcf.Palomar` definitions, byte-identical to `../lean/Pcf/Palomar/Statement.lean`, with the three compared theorems as `sorry`. |
| `PcfSolution.lean` | The proof: imports the `Pcf` development, which supplies `Pcf.pcfAllTheWayDown_charZero`. |
| `comparator.json` | Compares `Pcf.Palomar.pcfAllTheWayDown_charZero`, `Pcf.Palomar.existsUnique_isNormalizationLift` and `Pcf.Palomar.exists_pointClosure_restriction`; permitted axioms are `propext`, `Quot.sound`, `Classical.choice`. |
| `formalization.yaml` | Palomar metadata (v0.4). Contains `TODO(Taylor)` items. |
| `../LICENSE` | Apache-2.0, at repository root as Palomar requires (matching the Lean file headers). |
| `../.github/workflows/palomar-preflight.yml` | Manually triggered Palomar preflight, pinned to PalomarSubmission `d4e41c1`. |

Submission parameters, for when the time comes:

- repository: **a new public repository `tdupu/pcfawd-formalization`**, not this private one (decided by
  Taylor 2026-10-15), at one full commit SHA. It needs `LICENSE` at its root, `lean/`,
  `palomar/`, and the preflight workflow. The paths below assume the same layout;
- project path `palomar`;
- Comparator configuration `palomar/comparator.json`;
- metadata `palomar/formalization.yaml`.

## Checklist

Requirements are from PalomarPolicy `CONTRIBUTING.md` and PalomarSubmission `README.md`,
read 2026-10-15. Palomar changes often, so re-read them before acting.

### Needs Taylor

- [x] Public repository `tdupu/pcfawd-formalization` created by Taylor 2026-10-15 (empty; not populated yet).
- [ ] Decide what moves into `tdupu/pcfawd-formalization`, and when.
      Leave out `lean/tauceti/`: its `Suggested.lean` is not a Lean module, which Palomar
      rejects anywhere in a submitted repository.
      Palomar accepts only public GitHub repositories, and `tdupu/pcf` stays private. The
      minimum is `LICENSE`, `lean/`, `palomar/`, the workflow, and the manuscript
      `latex/paper.tex` (cited by `formalization.yaml`). Not public (Taylor, 2026-10-15):
      `ai/ai-usage.md`, `lean/PALOMAR-PROCESS.md`, `lean/tauceti/`.
- [x] Authors of the formalization: all four (Taylor, 2026-10-15).
- [x] Automation account, review status, arXiv (Taylor, 2026-10-15): the code was built with
      `using-leanpowers` (`tdupu/agent-skills-public`), which builds on `CBirkbeck/mathlib-quality`;
      agents reviewed the statements; there is no arXiv identifier yet, so `latex/paper.tex`
      must ship in `pcfawd-formalization`.
- [x] **One more statement-fidelity review** of the final `PcfChallenge.lean` against the
      manuscript (2026-10-15): approved, recorded in `review.notes`.
- [ ] **Reconcile `latex/paper.tex` with the formalization.** Its "Formalization"
      subsubsection still says `thm:general`, `lem:covers` and the passage to the
      normalization are not formalized, and that `prop:loci-compare` and
      `lem:tower-unnormalized` are assumed. The submission proves these and assumes only
      purity and Abhyankar. `paper.tex` is hand-managed and ships in `pcfawd-formalization`.
- [ ] Decide the submission relationship answer. Palomar records it permanently as a claim
      about the submitter: "I am a responsible author or maintainer", or "I have approval
      from one".
- [ ] Explicit authorization to submit, after reviewing the preflight report and the
      private Palomar review.

### Agent work

- [x] Apache-2.0 `LICENSE` at repository root.
- [x] Lean toolchain `v4.35.0` with Mathlib `v4.35.0`, matching Mathlib's `lean-toolchain`
      exactly.
- [x] Every `.lean` file in `lean/Pcf` uses the module system. Exception: `../lean/tauceti/`
      holds a non-module roadmap `Suggested.lean` and must be left out of `pcfawd-formalization`.
- [x] `PcfChallenge.lean` (300 lines), `PcfSolution.lean`, `comparator.json` and
      `lake-manifest.json`. The statement uses Mathlib vocabulary; `../lean/Pcf/Palomar/Bridge.lean`
      proves it equivalent to the development's `Pcf.pcfAllTheWayDown_charZero`.
- [x] Local `lake comparator --paranoid` run accepted the Solution under the default kernel,
      lean4lean, nanoda, con-leche and con-ron. It ran on macOS with no sandbox, which is weaker
      evidence than Palomar's Linux run.
- [x] `project.description` re-derived from the elaborated Challenge.
- [ ] A passing preflight run: Actions → "Palomar preflight", which needs the repository to
      be public. Upstream issue PalomarSubmission#154 (open on 2026-10-15) reports that the
      preflight can skip verification steps.
- [ ] Update `../lean/PALOMAR.md` (the claim manifest) and `../lean/HANDOFF.md` to the
      `v4.35.0` pins and the `Pcf.Palomar` entry.

## Background

- `../lean/PALOMAR.md`: the claim manifest. It covers the informal-versus-formal half of a
  submission, with does-not-claim blocks for each entry.
- `../lean/PALOMAR-PROCESS.md` (private; not copied to `pcfawd-formalization`): notes from 2026-09-24 on
  how Palomar works. Superseded where it disagrees with this file.
- Palomar's only trusted Tau Ceti revision (`221bb56`, Lean `v4.31.0-rc2`) was below
  Palomar's own toolchain floor on 2026-10-15. The Challenge here imports Mathlib only, so
  this does not affect us.
