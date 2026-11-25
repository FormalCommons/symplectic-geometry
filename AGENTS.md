# Instructions for agents

This repository builds a Lean 4 library on top of Tau Ceti and Mathlib. It
covers the subject of the plan that [README.md](README.md) links to: the plan
describes the subject, states its milestones, gives the sources, and may say
how the library should be built. Read the plan's pages for the work you do.

The plan is the atlas, which is private: do not look for it on GitHub. Every
job's container has a read-only copy at `/atlas`, with its pages under
`/atlas/atlas/` and `/atlas/auxiliary/`, and the atlas commit it was copied
from in `/atlas/COMMIT`. This repository is public and the atlas is not, so
never copy text from the atlas into the repository or into its issues, pull
requests and comments. Write statements in Lean and explanations in your own
words, and refer to the atlas by page and milestone name, such as
`atlas/linear-symplectic-geometry.md`, *milestone name*. A milestone's name
is the only prose of the atlas that you may repeat. The names of Mathlib and
Tau Ceti declarations, formulas, and citations of published sources are not
copies, even where the atlas has them too.

The milestones are results that the library must prove, and they measure how
much of the subject it covers. But the library is more than its milestones: it
is meant to be used, by later work here, by other projects, and eventually as
part of Tau Ceti or Mathlib. Write it so that moving it there needs little
more than a new namespace and copyright header.

The design describes how the library is organized: its folders and files,
its core definitions and their API, and which parts build on which. Follow
it. `DESIGN.md`, once it exists, is its overview: the parts, the folders each
owns, which parts build on which, the definitions several parts share, and
the part that proves each milestone. A part can have a detailed design of its
own in `design/<part>.md`, `<part>` being its name in `DESIGN.md`; adding one
does not change `DESIGN.md`. A part's design gives its files, its
definitions with their API, its main results and their names, and what it
uses from other parts.

Designing is work like any other. A part that needs more design than the
overview gives gets an issue of its own, labelled `proposed`, whose pull
request adds or changes the part's file under `design/`. The agent who writes
or splits along `DESIGN.md` creates such issues, and so does an agent whose
building issue finds the design insufficient: then, if the part's design
issue is open, mark it as blocking the issue you work on and stop, so that
your issue waits for it. If the design is wrong, propose a change to it in an
issue, labelled `proposed`, instead of working around it. Keep changes to
`DESIGN.md` itself small, since every part shares it.

## Building

```sh
lake exe cache get          # Mathlib's compiled files; takes a minute
.github/tauceti-cache.sh    # Tau Ceti's, where its build cache has them
lake build --wfail
```

`--wfail` makes every warning an error, as CI does, so a `sorry` fails the
build. Before you push, `lake build --wfail` must succeed.

Run the three commands in this order. The script builds the Tau Ceti modules
that the library imports, and takes them from Tau Ceti's build cache where
that has them. It takes a second once an earlier job that shares the
container's Lake cache has built them; on a server, work jobs share one
cache and reviews another. After a move of Tau Ceti, the first job to run it
compiles the modules that Tau Ceti's cache does not have, which can take 40
minutes, and jobs that start meanwhile wait for it, 45 minutes at most, and
then go on. So start it in a way that lets it run that long, such as in the
background, and start `lake build` only when it has ended. If it is stopped,
run it again: it goes on from where it was. It never fails: if it reports a
problem, go on, and the build compiles what is missing. Where Lake's
artifact cache is not set up (`LAKE_ARTIFACT_CACHE`, `LAKE_CACHE_DIR`), it
does nothing. A branch made before the script was added does not have it;
build without it there.

## Layout and names

- The library is under `SymplecticGeometry/`, in the namespace
  `SymplecticGeometry`. Its folders are Mathlib's top-level areas, such as
  `SymplecticGeometry/Algebra/` or `SymplecticGeometry/Geometry/`, and below
  them, topics. Use one file per topic. When `Foo.lean` gets a sibling
  `FooBar.lean`, make a folder instead: `Foo/Basic.lean` and `Foo/Bar.lean`.
- Name files and declarations after the mathematics, never after a milestone,
  an issue or a pull request. Follow Mathlib's naming conventions; a name
  never claims more than the statement (`_iff` only for an iff).
- A declaration about an existing Lean, Mathlib or Tau Ceti notion, one that
  dot notation on that type would find, goes in that type's namespace, such
  as `Matrix.trace_foo`, so that it can move upstream without a rename.
  Declarations about this library's own definitions go in
  `SymplecticGeometry`.
- No file imports the whole library. `lake build` builds every file under
  `SymplecticGeometry/` by itself (the `globs` in `lakefile.toml`), so a new
  file needs no import anywhere else. Do not add a file that imports the
  others.
- A new file has at most 1000 lines. No file may have more than 1500 (the
  build fails).

## Files

Every file is a module, and starts like this:

```lean
/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import SymplecticGeometry.Algebra.Foo.Basic

/-!
# Title

What the file contains: its main definitions and results.

## References

* [A. Author, *Title of the book*][AuthorYear]
-/

public section

namespace SymplecticGeometry

…

end SymplecticGeometry

end
```

- The header is exactly as above; CI checks it. The module docstring comes
  right after the imports. Mathlib's style linters are on and fail the build,
  among them the limit of 100 characters per line.
- The one other header is that of a file taken from Tau Ceti. When the
  library needs declarations that Tau Ceti's main branch has and the pinned
  version does not, you may copy them, since Tau Ceti's license is this
  library's. The license then requires that their file keeps Tau Ceti's
  notices, so:
  - They go in a file of their own, at the path of Tau Ceti's file with
    `SymplecticGeometry/` in place of `TauCeti/`, under Tau Ceti's names and
    namespaces. A move of Tau Ceti past them then deletes the file. Add no
    declaration of your own to such a file, and copy none into a file with
    the header above. If the library's own file already has that path, the
    copy goes in the sibling `FromTauCeti.lean`: for Tau Ceti's
    `TauCeti/A/B.lean`, the file `SymplecticGeometry/A/B/FromTauCeti.lean`.
    The library's file keeps its path and its header, and the rest of these
    points hold for the sibling.
  - The header is that of Tau Ceti's file as it is: every line before
    `module`, with its copyright line and its `Authors:` line, which may
    name people. CI's check allows any holder and any authors in a header
    of five lines. A few of Tau Ceti's files have a longer one: an
    `Authors:` line that runs on, or a second comment that credits another
    project. Do not shorten it. CI rejects it, so take nothing from such a
    file, and create an issue labelled `proposed` that asks a maintainer to
    change the check.
  - The module docstring names Tau Ceti's file and each commit you copied
    from, says that the file is a part of it, and says each change you made
    to Tau Ceti's code or text. Keep what Tau Ceti's file says of where a
    declaration you take comes from, in its module docstring or in a
    comment ("Adapted from …", "Ported from …", its references). Copy
    every entry of its `## References` section as it is, even one that
    cites a source for the whole file rather than for what you take.
  - Take only what the library needs, and keep Tau Ceti's text as well as
    its code. Apart from the module docstring, change nothing, docstrings
    and comments included, beyond what the pinned version requires and the
    correction of an error in Tau Ceti's text.
  - Only copied declarations take Tau Ceti's header. A proof written anew
    that follows a proof of Tau Ceti, or of Mathlib, in another setting
    stays in a file with the header above, and its module docstring credits
    the declaration it adapts by name.
- A module can import only modules, so every file starts with `module`.
  Import with `public import`, so that files that import yours see the
  declarations your statements use. Import the specific modules you need,
  never all of `Mathlib` or `TauCeti`, and never `Lean`, `Lake` or
  `Mathlib.Lean` modules. Specific `Mathlib.Tactic.*` modules are fine, but
  not `Mathlib.Tactic` itself.
- Only declarations in a `public section`, or marked `public`, are visible
  to other files. Other files see a definition's type, but not its body. Give
  a definition `foo` a lemma `foo_def` that states its body, proved by
  `(rfl)`, and unfold it with that lemma elsewhere. Use `@[expose]` only for a
  definition that other files must compute with, by `rfl` or `decide`.
- Cite sources in the module docstring's `## References`, with the key that
  the plan's `references.bib` gives the source. In a file taken from Tau
  Ceti, the entries copied from Tau Ceti's file stay as they are (see
  *Files*); an entry that the copy adds cites with the `references.bib` key,
  if there is one.

## Rules for the source

- **No gaps.** No `sorry`, `admit`, new `axiom`, `native_decide` or
  `decide +native`. A theorem may depend only on `propext`,
  `Classical.choice` and `Quot.sound`. A `sorry` fails the build; reviewers
  check the axioms with `#print axioms`.
- **No `set_option`**, in any form, including `set_option maxHeartbeats … in`,
  and no `count_heartbeats`. Every declaration must check within Lean's
  default limits.
- **No metaprogramming**: no `meta`, `unsafe`, `elab`, `initialize`,
  `run_cmd`, `#eval`, attributes such as `@[tactic]` or `@[init]`, and no
  `macro` or `macro_rules` that is not `local` (`scoped` ones are ruled out
  too).

CI rejects these by reading the text of every file, comments included. So
keep the words `set_option`, `unsafe`, `native_decide`, `initialize`, `meta`,
`elab`, `macro` and `#eval` out of comments and names too, and do not start a
line of a comment with `axiom`.

## Writing a library

- **Use what exists.** Before you define or prove anything, search Mathlib
  (`.lake/packages/mathlib/Mathlib/`), Tau Ceti
  (`.lake/packages/TauCeti/TauCeti/`) and this library for it, by the
  statement and not only by the name, and use what you find. Never add a
  renamed copy, a wrapper, or a less general version of something that
  exists. Where the plan says that a result exists in a library, do not
  reprove it. The library defers to Tau Ceti at the commit it is on: it
  keeps no definition, lemma or step of a proof that Tau Ceti has there,
  under any name. So after each move of Tau Ceti (*Leave the setup alone*,
  below), issues "Use Tau Ceti `<commit>`: `<directory>`" go through what
  the move brought, remove the library's versions, and move every use to
  Tau Ceti's. Modules under Tau Ceti's `TauCeti/Examples/` do not count as
  what Tau Ceti has: they illustrate its API, and Tau Ceti imports them
  nowhere outside that folder. Library files do not import them, and an
  issue "Use Tau Ceti `<commit>`: `Examples`" moves no library code onto
  them; a fact that only such an example proves is proved here, with its
  topic.
- **Definitions come with their API.** A new definition comes with the API
  that the design gives it, and at least what makes it usable: how to
  build and use it (`foo_def`, `mem_foo_iff`, constructors and eliminators),
  how it behaves under the operations around it, `@[simp]` on lemmas that
  put terms in normal form, and `@[ext]` for a structure. A new predicate
  comes with an example that satisfies it, or a use, in the same pull
  request.
- **State results in their natural generality.** Use the weakest hypotheses
  and typeclasses that make a statement true, as Mathlib would, but no
  generality that nothing needs. Drop hypotheses that the proof does not
  use.
- **Supporting results belong to the library.** A lemma that another proof
  could use is public, named after what it says, and placed with its topic,
  not in the file of the theorem that first needed it. Keep `private` for
  steps of one proof.
- **Milestones are theorems of the library.** A theorem that proves a
  milestone sits where its subject belongs. Its docstring ends with a line
  that names the milestone, such as "Milestone: *Bézout's theorem for plane
  curves*." That line is the only place a docstring mentions the plan. It has
  the plan's hypotheses and conclusion, in the plan's generality or more. If
  the library proves a more general result, the milestone is that result, or
  a corollary of it in the plan's form. If the plan's statement is wrong, see
  the next section.
- **Documentation.** Every definition and every main theorem has a docstring
  that says what it is, mathematically, not how it was proved or which issue
  it came from. Every file has a module docstring.
- **Proofs check quickly and read well.** Prefer an argument to a search, and
  automation (`simp`, `grind`, `omega`, `positivity`, `ring`) to long chains
  of rewrites. Split a proof of more than about 50 lines into lemmas.
- **Refactors.** Improving what exists, by sharing, moving, generalizing or
  renaming it, is welcome, but in a pull request of its own, for an issue of
  its own. If your work needs one, create an issue labelled `proposed` for it
  instead of doing it inside your pull request. A refactor updates every use
  in the same pull request and deletes the old name, with no deprecated
  alias, wrapper or forwarding file. If it changes how the library is
  organized, it updates the design too. A change to a part's design that
  existing code no longer fits is a refactor: one pull request changes
  both.
- **Leave the setup alone.** Do not change `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain`, `LICENSE` or anything under
  `.github/`, nor add a `lakefile.lean`, unless the issue you work on asks
  for it and a person in the project opened it. The one other exception is an
  issue "Move Tau Ceti to `<commit>`", which `github-actions[bot]` opens when
  Tau Ceti's security audit has passed commits that change what the library
  builds on. Whoever works on it changes the first three
  files as the issue says, fixes in the same pull request whatever breaks
  in the library, and creates the issues that remove from the library what
  Tau Ceti now has. A move is never split, and may go over the 2000 lines of
  the next rule; CI checks that it changes the setup only as Tau Ceti does.
- **Keep pull requests focused.** One pull request does one issue, and adds
  at most 2000 lines. If an issue is too big for that, split it into smaller
  issues instead.

## Errors in the plan and its sources

The plan, and the sources it cites, can be wrong: a statement can be false or
miss a hypothesis, a proof can have a gap, a reference can point to the wrong
place. Expect this. An error is something you can show: a counterexample, or
a step that is false or does not follow. A proof you did not find is not an
error. An error that the plan already notes needs no entry; follow its
correction. An error outside your issue gets an issue of its own, labelled
`proposed`. When you find an error in your issue:

1. **Fix it as part of your work, if you can.** Prove the closest correct
   statement, or close the gap in the proof. For each hypothesis you add, or
   change you make to the conclusion, give a counterexample without it: in
   Lean, next to the corrected theorem, if you can.
2. **Record it in `ERRATA.md`, in the same pull request**, in the form the
   file shows, saying in your own words what the plan says (never quote
   the atlas), or quoting a published source. If the file lists
   the error as unresolved, replace its **Unresolved** line with the fix.
3. **If you cannot fix it**, because the statement is false and no
   correction gives the results that build on it what they need, or because
   the plan's proof fails and you know no other, look for another route:
   another proof, or another statement that gives them what they need. The
   plan says which results build on a milestone. If you find a route, take
   it, and record the error and the route as in step 2.
4. **If you find no route**, do not open a pull request that closes the
   issue. Comment on the issue with the error, its evidence, and each route
   you tried and where it failed, so that the next agent tries another. If
   neither `ERRATA.md` nor an open pull request has an entry for the error
   yet, also open a pull request that only adds one, marked **Unresolved**,
   on the branch `fc/issue-<number>-errata`. Unlike other pull requests, end
   its description with `Part of #<number>`, and never write `Closes`,
   `Fixes` or `Resolves` in it or in a commit message, since those close the
   issue when the pull request merges.

Never weaken a milestone, change what it says, or propose closing its issue
because the plan is wrong, without an entry in `ERRATA.md`.

## Reviewing

Besides building, check each main theorem of the pull request with
`#print axioms`, in a scratch file that you do not commit:

```lean
import SymplecticGeometry.Foo

#print axioms SymplecticGeometry.foo_bar
```

Run it with `lake env lean Scratch.lean`. Then check that it is good library
code, by the rules above:

- Nothing in it repeats Mathlib, Tau Ceti or this library. Search for its
  main statements.
- Its statements are as general as they naturally are, its definitions come
  with their API, and its supporting lemmas are public and placed by topic.
- It fits the design (`DESIGN.md`, and the part's file under `design/`): the
  files, the definitions and the names it gives.
- A milestone's statement matches the plan, or is more general. If it is
  weaker or different, the pull request adds an entry to `ERRATA.md`. Check
  that the error is real, and that each change to the statement has a
  counterexample that shows it is needed.
- A change to `lakefile.toml`, `lake-manifest.json` or `lean-toolchain`
  belongs to a move of Tau Ceti or to a maintainer's issue. A move changes
  only the line of Tau Ceti's `rev`, the toolchain and the
  manifest, as CI's setup check enforces, and fixes the library in the same
  pull request.
- A pull request that only adds an unresolved entry to `ERRATA.md`, and is
  `Part of` its issue, need not do the issue. Check the entry's evidence and
  the routes it lists, and that the file has no entry for that error yet.

A pull request that adds or changes the design is reviewed like code. Check
it against what the plan says about building the library and against the
rest of the design. For `DESIGN.md`, check that every milestone has a part
and that the parts can be built in the order given from what exists. For a
part's design, check that it fits the overview, defines nothing that
Mathlib, Tau Ceti or the library already has, states its milestones as the
plan, or `ERRATA.md`, does, and is clear enough to become issues of a few
hundred lines each.

## Triage

An issue that builds a part of the library must agree with the design and
the plan, as `ERRATA.md` corrects it. If it does not, say where, and correct
the issue or close it. An issue that changes the design must say why the
design is wrong or incomplete; check that reason.
