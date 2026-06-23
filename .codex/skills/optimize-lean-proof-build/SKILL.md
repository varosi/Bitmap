---
name: optimize-lean-proof-build
description: Optimize Lean proof build time without removing, weakening, or bypassing proved lemmas and theorems. Use when Codex is asked to speed up Lean theorem/proof compilation, profile slow lemmas, reduce build time of proof modules, refactor repeated proof patterns, generalize several lemmas into one reusable lemma, improve Lean/Lake parallelism, or investigate proof elaboration hotspots while preserving theorem coverage and public proof APIs.
---

# Optimize Lean Proof Build

## Core Contract

Improve proof build speed while preserving correctness and coverage.

Do not remove proved lemmas or theorems, weaken theorem statements, hide failures with `sorry`/`admit`/`axiom`, commit `implemented_by` in proof-critical code, or treat a higher `maxHeartbeats` as a real optimization. If a lemma is generalized or replaced internally, keep the old theorem name as a short compatibility wrapper unless the user explicitly approves an API break.

## Workflow

1. Establish the baseline.
   - Record the current branch, dirty files, Lean version, and Lake version.
   - Measure the full target the user cares about, usually `lake build <target>` or `lake test`.
   - Measure hot modules directly, for example `/usr/bin/time -p lake build +Namespace.Module`.
   - Do not compare cold and warm builds as if they were the same experiment. If using `lake clean`, say that the measurement is a cold build.

2. Find proof hotspots before editing.
   - Use `lake env lean --profile -R . -o /tmp/profile.olean -i /tmp/profile.ilean path/to/File.lean` for per-declaration elaboration/type-checking time.
   - Use `#time` only as temporary local instrumentation and remove it before committing unless the project already keeps timing commands.
   - Sort by declarations that are slow, repeated across many files, or imported by many downstream modules.
   - Check import fanout: speeding or isolating a heavily imported proof module often matters more than a standalone theorem.

3. Choose the lowest-risk optimization.
   - Prefer proof-local changes before API changes.
   - Replace broad proof search with directed proof terms: `exact`, `refine`, `apply`, `constructor`, `cases`, `simpa using`.
   - Replace broad `simp` with `simp only [...]` or a smaller local simp set when the goal is stable.
   - Avoid global `[simp]` additions unless they reduce more time than they cost across downstream imports.
   - Name expensive intermediate facts with `have`; reuse them instead of recomputing large reductions.
   - Use `show`, `change`, and explicit arguments to guide elaboration and reduce typeclass/search ambiguity.
   - Prefer `def` over `abbrev` for helper definitions that should not unfold eagerly during proofs.

4. Generalize repeated lemmas safely.
   - When several lemmas differ only by constants, indices, modes, or constructors, prove one stronger lemma over the shared structure.
   - Keep existing theorem names as one-line specializations with their original attributes and namespaces.
   - Avoid over-generalizing if it makes typeclass inference, reduction, or downstream rewrite search slower.
   - Add doc comments for new proof lemmas when the project asks for documentation-visible lemma comments.

5. Improve parallelism and invalidation behavior.
   - Split very large proof files into coherent modules with independent imports so Lake and Lean can compile more work concurrently.
   - Keep computational definitions and public APIs in lightweight modules; put heavy proof details in downstream lemma modules.
   - Avoid making many files import a massive proof module when only a few declarations are needed.
   - For direct profiling or one-file checking, use Lean's `-j <n>` when useful, for example `lake env lean -j 8 --profile -R . path/to/File.lean`.
   - Do not assume a Lake job flag exists; inspect the local `lake --help` before adding build-system parallelism flags.

6. Validate after each meaningful change.
   - Rebuild the smallest affected target first.
   - Then run the user's required full target, normally `lake build` or `lake test`.
   - Search changed proof code for forbidden escapes: `sorry`, `admit`, `axiom`, and `implemented_by`.
   - For top-level theorem refactors, use `#print axioms TheoremName` temporarily when trust boundaries matter, and remove it before committing.
   - Compare before/after timings from the same kind of build and report the commands used.

## Good Practices To Add

- Track module dependency cost, not only single theorem time. A slightly slower isolated lemma can still be a win if it lets many imports avoid a heavy module.
- Preserve attributes such as `[simp]`, `[aesop safe]`, and namespace placement when keeping compatibility wrappers.
- Minimize import lists after moving proofs; unnecessary imports can dominate rebuild time.
- Prefer stable, explicit proof scripts over tactic scripts that are fast only by accident.
- Avoid huge goals passed to automation. Break them into smaller claims and simplify data constructors early.
- Cache expensive normalized expressions in local `have` facts, especially around arrays, byte arrays, dependent indices, and arithmetic casts.
- If proof speed depends on generated or computed data, consider proving small generic transport lemmas instead of unfolding the data repeatedly.
- Keep performance evidence in the final answer: baseline, optimized time, percentage change, target, machine/thread assumptions, and any residual hotspots.

