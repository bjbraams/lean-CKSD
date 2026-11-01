# Project instructions — lean-CKSD

Before working, read and follow [the shared Lean instructions](../lean-codes/AGENTS.common.md),
then apply the project-specific rules below. Resolve that path relative to this file.
Local rules take precedence over the shared defaults. If the shared file is unavailable,
report that fact rather than proceeding without it.

## Build settings

- Lake root: the directory containing this `AGENTS.md`.
- Build output: `.lake/build-CKSD`; preserve the matching `buildDir` in `lakefile.toml`.
- Ordinary build command: `lake build > /tmp/cksd-build.log 2>&1`.

## Project

This is a new project in the area of Core Knowledge of Statistics and Data Science at the level
of graduate students and beginning researchers. The project follows the style of the earlier
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
the next free number in its file. The sections were reorganized on 2026-11-01 from the earlier
Sections 101–114; `SYNOPSIS-CONCORDANCE.md` maps every earlier identifier to its current one. These files are meant for the human mathematician reader; they
do not reference any technical Lean concepts. Proofs are outside their scope. The selection is
the recurring core of each section. The index records how far the series has been written.

Following completion of the synopsis series, the next major task is to inventorize
coverage of the SYNOPSIS in Lean Mathlib and TauCeti. This inventory is to be documented in files
STRUCTURE.md and STRUCTUREddd.md, following the style of the sibling CKMA project. These STRUCTURE
files are meant to support future Lean projects. The inventory has been written: `STRUCTURE.md`
is the index and states the classification rule (covered, partly covered, not covered);
`MathlibCoverage.md` and `TauCetiCoverage.md` summarize coverage per library; `GAPS.md` restates
the principal results that neither library proves. `GAPS_EASY.md` outlines
short derivations from library results for some of them.

You may be asked to edit, revise or expand any of the files in the project directory or to create
new files.
- Keep changes narrowly related to the request.
- Preserve unrelated user changes.
- Do not commit changes unless explicitly requested.
