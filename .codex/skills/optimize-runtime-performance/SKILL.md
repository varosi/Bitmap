---
name: optimize-runtime-performance
description: Optimize runtime performance as a software developer without removing functionality, breaking tests, or weakening proved properties such as lemmas and theorems. Use when Codex is asked to speed up code, reduce CPU cycles, memory use, allocations, latency, throughput cost, benchmark time, Lean runtime heartbeats, or algorithmic complexity, and when performance work must be guided by debug/profiling/benchmark data with each performance test run at least five times for more reliable measurement.
---

# Optimize Runtime Performance

## Core Contract

Optimize measured runtime behavior while preserving functionality, public APIs, tests, and proved properties. Performance wins must be demonstrated with benchmark or performance-test data, not intuition.

Do not remove features, skip test paths, weaken correctness checks, bypass public APIs, remove or weaken lemmas/theorems, hide failures, or optimize only by lowering coverage. Proof scripts may be changed to fit optimized code as long as the proved properties stay intact. Temporary `implemented_by` is allowed only for local performance experiments; final committed code must remove it and prove the optimized implementation. If the fastest change would alter semantics or public behavior, explain the tradeoff and ask before editing.

Each performance test used as evidence must run at least 5 iterations in the same measurement session. If an existing performance test runs fewer than 5 iterations, update it or add a comparable benchmark harness before using it as performance evidence.

## Workflow

1. Define the performance target.
   - Identify the operation, input size, workload shape, and metric: latency, throughput, allocations, memory footprint, CPU time, heartbeats, I/O, or algorithmic complexity.
   - Confirm which correctness contract must remain unchanged: tests, proved lemmas/theorems, public encode/decode behavior, external compatibility, or API output equality.
   - Choose representative inputs, including worst-case or regression inputs when they matter.

2. Establish a baseline.
   - Run the relevant benchmark/performance test with at least 5 runs.
   - Record command, target, input size, average/median if available, variance or min/max if available, machine assumptions, and current branch.
   - Keep cold-build, warm-build, first-run, and steady-state measurements separate.
   - Run the relevant correctness suite before or after the baseline so later regressions are visible.

3. Find hotspots from evidence.
   - Use profiler, debug counters, benchmark logs, tracing, allocation reports, flamegraphs, or domain-specific counters before changing code.
   - For Lean projects, inspect benchmark output and heartbeat counters when available; use `lake test`, targeted executables, `lean --profile`, or explicit counters according to the bottleneck.
   - Locate whether time is spent in algorithms, allocation/copying, data conversion, bounds proofs carried into runtime code, I/O, parsing, encoding, decoding, cache misses, or repeated work.
   - Optimize the hottest path first unless a low-risk structural change clearly unlocks larger wins.

4. Choose the right optimization level.
   - Low level: reduce allocations, copies, boxing, bounds checks, conversions, cache-unfriendly access, unnecessary intermediate arrays/strings, and repeated arithmetic.
   - Mid level: batch work, reuse buffers, precompute tables, avoid repeated parsing/encoding, improve data layout, use specialized loops where the public behavior is unchanged.
   - High level: improve algorithmic complexity, change search strategy, memoize, short-circuit impossible cases, stream instead of materializing, or reduce Lean/runtime heartbeats by avoiding needless computation.
   - Prefer simple, measurable changes over clever code whose correctness or maintenance cost is unclear.

5. Preserve correctness.
   - Keep the same public API behavior unless the user explicitly approves a behavior change.
   - Update or add exact equality checks for optimized paths when possible.
   - Keep proved lemmas and theorems compiling with the same intended statements; update proof bodies as needed for optimized code.
   - If proof obligations expose weak runtime code, propose the runtime fix and ask before changing semantics.
   - Keep external fixture, interoperability, and regression tests when they cover functionality beyond the proved or benchmarked property.

6. Measure after each meaningful change.
   - Re-run the same performance test with at least 5 runs.
   - Compare against the baseline using the same input size, environment, and command.
   - Treat noisy wins as inconclusive; repeat or broaden measurement before claiming success.
   - If a micro-optimization makes one workload faster but worsens another relevant workload, report both and choose according to the user-facing goal.
   - If using temporary `implemented_by` to test an optimized implementation, treat the result as exploratory only until the optimized code is fully proved without `implemented_by`.

7. Validate end to end.
   - Run targeted correctness tests first, then the requested full suite, normally `lake test` or the project’s equivalent.
   - Run proof builds when proof modules can be affected, normally `lake build <library>` or the user-specified target.
   - Search for accidental coverage bypasses, disabled tests, removed assertions, weakened theorem statements, removed lemmas, `implemented_by`, or proof escape hatches.
   - Before final commit, ensure all optimized runtime code is proved directly and no temporary `implemented_by` remains.
   - Report commands, before/after measurements, number of runs, correctness verification, and remaining hotspots.

## Good Practices

- Make benchmarks deterministic enough to compare: fixed seeds, fixed fixtures, fixed input sizes, and no hidden network dependency.
- Avoid benchmarking debug-only code unless debug performance is the actual target.
- Keep benchmark changes separate from runtime changes when that improves reviewability.
- Prefer changing shared hot helpers over duplicating optimized logic in many call sites.
- Keep optimized code readable; add comments where an implementation is shaped by a non-obvious performance invariant.
- Retain simple reference implementations or tests when they help verify optimized code.
- Use feature-level performance gates only when they are stable enough for CI; ratio guards are often more robust than absolute timing gates.
