# Project instructions — lean-CKSD

Before working, read and follow [the shared Lean instructions](../lean-codes/AGENTS.common.md),
then apply the project-specific rules below. Resolve that path relative to this file.
Local rules take precedence over the shared defaults. If the shared file is unavailable,
report that fact rather than proceeding without it.

## Build settings

- Lake root: the directory containing this `AGENTS.md`.
- Build output: `.lake/build-CKSD`; preserve the matching `buildDir` in `lakefile.toml`.
- Ordinary build command: `lake build > /tmp/cksd-build.log 2>&1`.
- Local exception to the shared build topology: `.lake` is a symlink to
  `/export/scratch1/braams/lean-CKSD-lake` on local disk, not to the shared
  `lean-codes-lake`. This project has its own `.lake/packages` because it requires
  Statlib (`https://github.com/stat-lib/statlib`) in addition to Mathlib and TauCeti,
  with Lean, Mathlib, and TauCeti revisions newer than those of the sibling projects.
  The pins in `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` are
  authoritative. The other shared rules for `.lake` apply to this target: never replace,
  delete, or retarget it without being asked, and never write to `lean-codes-lake`
  from this project.
- In this project the library search order is Mathlib → pinned TauCeti → pinned
  Statlib → local project code.

## Project

This project is in the area of Core Knowledge of Statistics and Data Science at the level
of graduate students and beginning researchers. The project follows the style of the
sibling ../lean-CKMA project that is devoted to core knowledge in mathematical analysis.

One component of the lean-CKSD project is to assemble a bibliography. The main working file is
`CKSD-bib.md`. This file is meant for the human reader. The file is divided into topical sections
numbered from 101 on.

PDF files for some of the references are in the directory ../lean-CKMA/References/. The directory
../lean-CKMA/ReferencesSuppl/ may contain PDF files for some books in the same general area that
are not in the bibliography.

There may be additional files, for example `*.json`, for precise bibliographical data.

Files `SYNOPSIS.md` and `SYNOPSIS101.md`–`SYNOPSIS108.md` describe the mathematical content of
Sections 101–108, in the style of the SYNOPSIS files in the sibling CKMA project. `SYNOPSIS.md`
is the index. Numbered entries, cited as `<ddd>.<k>`, are stable identifiers: existing numbers
are kept when a statement is revised, removed numbers are not reused, and a new statement takes
the next free number in its file. These files are meant for the human mathematician reader; they
do not reference any technical Lean concepts. Proofs are outside their scope. The selection is
the recurring core of each section. The index records the scope and size of the series.

Coverage of the SYNOPSIS in Lean Mathlib, TauCeti, and Statlib is documented in files
STRUCTURE.md and STRUCTUREddd.md, following the style of the sibling CKMA project. These STRUCTURE
files support Lean projects. `STRUCTURE.md` is the index and states the classification rule
(covered, partly covered, not covered); `MathlibCoverage.md`, `TauCetiCoverage.md`, and
`StatlibCoverage.md` summarize coverage per library; `GAPS.md` restates
the principal results that none of the libraries proves. `GAPS_EASY.md` outlines
short derivations from library results for some of them.

Following the bibliographical work and the development of the inventories the project continues
with the formalization of content of GAPS.md. The Lean codes for this formalization are developed
in the subdirectory CKDS. The Lean codes created there should all live in a CKSD namespace.
Within that namespace the naming should adhere to Mathlib standards. (I have in mind that at some
point this becomes a TauCeti project, and then the namespace CKSD will be replaced by namespace
TauCeti.) So one task is to go through all of GAPS.md and for the identified gaps, create code
according to Mathlib standards in the CKSD subdirectory. At first any such code may only be
admitted, but in time the `sorry`s should be removed.

You may be asked to edit, revise or expand any of the files in the project directory or to create
new files.
- Keep changes narrowly related to the request.
- Preserve unrelated user changes.
- Do not commit changes unless explicitly requested.

## Documentation consistency

- Describe the present mathematical content and coverage. Do not include
  development histories, review rounds, or accounts of additions, removals,
  renumbering, or changes in inventory counts. Retain source provenance
  and the library revisions needed to interpret coverage claims.
- Treat each numbered SYNOPSIS statement as the mathematical source for
  its restatements in GAPS.md and GAPS_EASY.md. Propagate corrections to
  hypotheses, conventions, and conclusions to every affected restatement
  and STRUCTURE assessment. A Scope or Argument paragraph must not silently
  add a missing hypothesis to a Statement paragraph.
- After changing statements or selections, recount synopsis entries,
  coverage classifications, selected gaps, easy entries, and Scope
  paragraphs. Update the indexes and library summaries, and check local
  Markdown links. New entries take the next free identifier.
- Preserve the explicit distinction between CKSD's direct-declaration
  coverage rule and CKMA's broader use of partly covered. Comparisons need
  a common rule and source baseline before counts can be combined.
