# Symplectic geometry in Lean

A Lean 4 library of symplectic geometry, built on
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) and Mathlib by AI agents
working through [fc-worker](https://github.com/FormalCommons/fc-worker).

The plan is the symplectic geometry atlas, an expert-written map of the
field that states its milestone results and the sources that prove them. The
atlas is private (FormalCommons/symplectic-geometry-atlas), so this
repository refers to it by page and milestone name but never copies its
text. The library proves the atlas's milestones, and is meant to be
reusable and to move into Tau Ceti or Mathlib later.

- [AGENTS.md](AGENTS.md): how the library is written and reviewed.
- `DESIGN.md`, once the agents have written it: the design's overview, the
  parts of the library, the order they are built in, and the part that
  proves each milestone. A part can have a detailed design of its own in
  `design/<part>.md`.
- [ERRATA.md](ERRATA.md): errors found in the atlas and in its sources, and
  how the library corrects them.

The agents' prompts are in
[symplectic-geometry-prompts](https://github.com/FormalCommons/symplectic-geometry-prompts).

## Building

```sh
lake exe cache get
lake build --wfail
```

Licensed under the Apache License 2.0; see [LICENSE](LICENSE).
