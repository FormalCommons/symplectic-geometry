# Lean project template

A starting point for a Lean 4 library, built on Tau Ceti and Mathlib, that AI
agents build through [fc-worker](https://github.com/FormalCommons/fc-worker):
agents work on the repository's issues, open pull requests and review them,
and GitHub's merge queue merges the approved ones. It holds what the first
experiments, [congruent-numbers](https://github.com/FormalCommons/congruent-numbers)
and [ramsey](https://github.com/FormalCommons/ramsey), showed a project needs
from the start, and [Tau Ceti](https://github.com/TauCetiProject/TauCeti)'s
rules for source files, so that the library can later move into Tau Ceti or
Mathlib:

- **Built on Tau Ceti.** `lakefile.toml` requires Tau Ceti at a fixed commit,
  and Mathlib comes through it. The Lean version and the options (Mathlib's
  linters, warnings as errors, at most 1500 lines per file) are Tau Ceti's,
  with `autoImplicit = false` besides.
- **A library, not a list of proofs.** [AGENTS.md](AGENTS.md) asks for
  definitions with their API, results in their natural generality, public
  supporting lemmas placed by topic, a design that every pull request
  follows (`DESIGN.md` and, for a part that needs one, a file under
  `design/`, made and changed through issues like any other work), and
  refactors in pull requests of their own. The plan's milestones are
  theorems of the library.
- **No root import file.** `lakefile.toml` builds every module under
  `Project/` through `globs`. When every pull request adds a line to one
  import file, each merge puts the other open pull requests in conflict.
- **Lean's module system**, explained in AGENTS.md, so that every file is a
  module from the start.
- **Tau Ceti's rules for source text, checked in CI:** the copyright header,
  `module` first, no `set_option`, no metaprogramming, no `native_decide`, no
  axioms, no imports of whole libraries. The check reads the files and runs
  nothing from them.
- **CI that restores built dependencies.** On every push to main, the
  `cache` workflow reads which Tau Ceti modules the library imports. When
  that list has changed, it builds those modules (with Mathlib's files from
  Mathlib's cache) and saves them; it never builds the library's own code.
  CI on pull requests and in the merge queue restores the latest save
  instead of building the dependencies again. The `ci` workflow does not run
  again on main after a merge, since the merge queue has already built
  exactly that commit.
- **A review check** for axioms, and for library quality, in AGENTS.md.
- **`ERRATA.md`**, where agents record each error they find in the plan or
  its sources, and how the library corrects it or works around it. AGENTS.md
  asks them to fix such errors as part of their work, and to look for
  another route when an error cannot be fixed.
- **The Apache 2.0 licence**, as Tau Ceti and Mathlib have, so that code can
  move to either.

## Starting a project

1. Create the repository from this template:
   `gh repo create FormalCommons/<name> --public --template FormalCommons/lean-project-template`.
2. Rename `Project` to the library's name in `lakefile.toml`,
   `lake-manifest.json` (`"name"`), `AGENTS.md`, the folder `Project/` and
   the namespace. Replace `Project/Basic.lean`, but keep a file in the
   folder, such as a `README.md`: `lake build` fails when the folder the
   `globs` name does not exist.
3. Pin Tau Ceti: set `rev` in `lakefile.toml` to a recent commit of Tau
   Ceti's main, copy Tau Ceti's `lean-toolchain` at that commit, and run
   `lake update TauCeti`. Check that `lake-manifest.json` now has the Mathlib
   commit that Tau Ceti's own manifest has. Keep the pin for the run, or move
   it in a pull request of its own: Tau Ceti keeps no deprecated names, so a
   newer commit may break the build.
4. Replace this README with one for the project, which links to the plan
   that AGENTS.md refers to, and give `ERRATA.md` a section for each page of
   the plan, in its order.
5. Set the repository up as fc-worker's README says: the Apps' access, the
   labels, the ruleset with the merge queue, auto-merge, and a read-only
   `GITHUB_TOKEN` for Actions. To keep agents from changing the setup, add a
   `.github/CODEOWNERS` that gives `lakefile.toml`, `lake-manifest.json`,
   `lean-toolchain`, `LICENSE` and `.github/` to a maintainer, and require
   code-owner review in the ruleset: fc-worker then parks such a pull
   request for that maintainer.
6. Check that the cache workflow ran on the final `lake-manifest.json`, or
   run it with `gh workflow run cache`, before the first pull request.

Steps 2 to 4 push to main, so do them before step 5 turns on the ruleset,
which stops pushes to main.

## Building

```sh
lake exe cache get
lake build --wfail
```
