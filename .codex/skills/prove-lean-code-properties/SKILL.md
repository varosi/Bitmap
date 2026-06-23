---
name: prove-lean-code-properties
description: Prove properties about Lean code as a proof engineer. Use when Codex is asked to add correctness lemmas or theorems, prove behavior of implementation code, replace fully proven functional tests, strengthen or generalize existing proofs, reuse project lemmas, Lean core, or Mathlib facts, keep proof code in the relevant library or executable's Lemmas subdirectory when possible, organize proof modules for fast parallel Lake builds, document proof coverage, add readable comments to complex proof logic, or identify implementation code that does not conform to the property being proved.
---

# Prove Lean Code Properties

## Core Contract

Prove real properties about the implementation while preserving behavior, public APIs, and proof coverage. Prefer reusable, fast, documented proofs over narrow proof scripts that duplicate existing work.

Do not use `sorry`, `admit`, `axiom`, committed `implemented_by`, or theorem weakening. Do not remove functional tests unless the property is fully proved and remaining tests still cover examples, fixtures, external compatibility, integration behavior, and performance where relevant.

If a proof attempt reveals weak or non-conforming runtime code, do not contort the theorem to match the bug. Explain the mismatch, propose concrete runtime code changes, and ask the user before changing runtime behavior unless the user already requested implementation fixes.

If a cleaner proof design would break the proof API, ask first. This includes renaming lemmas/theorems, changing theorem statements, removing compatibility wrappers, or consolidating duplicated lemmas in a way that downstream proof code must update.

## Workflow

1. Understand the code and property.
   - Read the implementation, existing theorem statements, and caller expectations.
   - Identify whether the desired property is computational equality, round-trip correctness, safety, bounds preservation, parser/encoder compatibility, or a container invariant.
   - Put new proof code under the relevant library or executable's `Lemmas` subdirectory whenever possible, such as `<LibraryName>/Lemmas/` or `<ExecutableName>/Lemmas/`.
   - Prefer that target's existing `Lemmas` module or a new focused proof module under its `Lemmas` subtree over implementation-adjacent proof code.
   - If a proof must live outside `Lemmas` because it depends on private/local implementation details or must expose a lightweight public API lemma, keep it minimal and explain why.
   - When possible, structure proof work as clean buildable increments: each meaningful lemma, module split, or theorem step should leave the affected target compiling so it can be committed independently.

2. Search before proving.
   - Use `rg` for local theorem names, definitions, and similar proof patterns.
   - Inspect project lemma indexes and imports before adding a new theorem.
   - Search Lean core and Mathlib through local package sources when available, for example `.lake/packages/mathlib/Mathlib`.
   - Use temporary Lean snippets with `#check`, `#print`, and `#print axioms` to confirm existing facts and trust boundaries; remove snippets before committing.

3. Design the theorem.
   - State the most general useful lemma that matches the code structure, not just the one test case at hand.
   - If several existing lemmas differ only by constants, constructors, modes, indices, or codecs, replace the duplication with one stronger lemma and keep old names as compatibility wrappers.
   - Prefer theorem statements that compose with existing invariants and avoid unnecessary unfolding by downstream proofs.
   - Keep public theorem names and theorem statements stable unless the user explicitly accepts a proof API break.
   - If a proof API break would produce cleaner properties, better names, or lower duplication, propose the exact break and ask before making it.
   - If the natural theorem statement exposes implementation behavior that violates the intended specification, pause proof refactoring and propose the smallest runtime change that would make the code conform.

4. Handle non-conforming code.
   - State the intended property, the actual behavior found during proof work, and why the current code blocks or weakens the proof.
   - Propose one or more runtime fixes with expected proof impact and compatibility risk.
   - Ask for approval before editing runtime code when the user only asked for proofs.
   - After approved runtime changes, prove the stronger property against the corrected behavior and keep or adjust tests according to the new proof coverage.

5. Prove efficiently.
   - Prefer directed proof terms: `exact`, `refine`, `apply`, `constructor`, `cases`, `rcases`, `simpa using`.
   - Use `simp only [...]` or small local simp sets in hotspots; avoid broad `simp`, `simp_all`, `aesop`, or large `omega` calls when a short arithmetic lemma or named `have` is faster.
   - Cache expensive intermediate reductions in named `have` facts.
   - Use `show`, `change`, and explicit arguments to reduce elaboration ambiguity.
   - Keep helper definitions opaque with `def` when unfolding them everywhere would slow proofs.
   - Profile slow proof files with `lake env lean --profile -R . path/to/File.lean` when proof time matters.

6. Organize for parallel Lake builds.
   - Split large proof files into coherent modules with narrow imports so Lake can compile independent proofs concurrently.
   - Keep executable code and lightweight API lemmas in small modules; put heavy proof details downstream.
   - Keep substantial proof code in the nearest target's `Lemmas` subtree so implementation modules stay focused on runtime code.
   - Avoid importing a large proof module just to use one small lemma; move shared lemmas to a smaller dependency module when that reduces rebuild fanout.
   - Check that new modules are imported by the project lemma index or library root only where needed.

7. Replace proven tests carefully.
   - First map each candidate test assertion to a named theorem that proves the same property for all relevant inputs.
   - Keep tests that cover external files, parser interoperability, public API wiring, examples, regressions, performance, or theorem assumptions not visible to users.
   - Remove only tests that are strictly redundant with complete theorem coverage.
   - Document the removed test coverage by naming the replacement theorem in the commit summary or nearby test/proof comments when useful.

8. Document proof coverage.
   - Add Lean doc comments `/-- ... -/` for new proof lemmas when they are nontrivial or part of the public proof surface.
   - Comment complex proof blocks briefly, explaining the invariant or transport step, not the syntax.
   - Update README proof coverage notes when adding/removing top-level correctness theorems or changing what a proved round-trip/property means.
   - Keep comments current when proofs are generalized or moved.

9. Validate end to end.
   - Build the smallest affected module first, and repeat this after each incremental proof step when feasible.
   - Run the relevant full target, normally `lake build Bitmap`, `lake test`, or the target requested by the user.
   - Search changed proof code for forbidden escapes: `sorry`, `admit`, `axiom`, and `implemented_by`.
   - Report theorem names added, tests removed, validation commands, and any remaining unproved assumptions.

## Project-Oriented Heuristics

- Prefer reusing local facts from the relevant library or executable's `Lemmas` subtree before proving from first principles.
- Prefer placing new proofs in that target's `Lemmas` subtree; implementation files should contain only the proof code needed for local invariants or public API ergonomics.
- Use Mathlib for standard arithmetic, list/array, bit, and parser-independent facts; avoid custom proofs when a stable library theorem exists.
- Generalize by data shape or invariant, not by making theorem statements hard to apply.
- Preserve old theorem names as wrappers after consolidation so downstream proofs keep compiling.
- Treat performance-sensitive proofs as production code: profile before optimizing, reduce import fanout, and keep proof search bounded.
