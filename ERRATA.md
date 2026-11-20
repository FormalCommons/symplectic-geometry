# Errata

Errors found in the plan and in the sources it cites while formalizing them,
and what the library does about each. `AGENTS.md` says when to add an entry.

There is a section for each page of the plan, in the plan's order, headed
with the page's file name, such as `## 01-local-properties.md`, and
`## Other sources` last, for errors in sources that no page covers. Add a
missing section in its place in that order. Within a section, entries go in
alphabetical order of their titles, with a blank line between them, so that
two pull requests conflict only when their entries land in the same place.

Each entry has this form:

```markdown
### <A short title>

- **Where:** the plan's page and milestone, or the source and its location.
- **Error:** what it says, quoted, and why that is wrong: a counterexample,
  or the step that is false or does not follow.
- **Fix:** what the library proves instead, or the route it takes, naming the
  declarations.
  Or, while there is none, **Unresolved:** the routes tried, and where each
  failed.
- **Issue:** #<number>.
```
