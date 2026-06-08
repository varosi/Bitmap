# Agent Notes

## Project Documentation

- The main project description is in `README.md` at the repository root.
- If a change affects PNG encoder or decoder feature support — adding or removing a color type, bit depth, filter type, compression mode, chunk, or any item in the "Not supported" list — update the "Supported PNG features" section of `README.md` in the same commit.
- If a change affects proof coverage — adding or removing a top-level correctness theorem, or changing what "PNG encode/decode round-trip is proved" means in scope — update the proofs bullet list at the top of `README.md` in the same commit.

## Testing

- Run `lake test` to execute the project test suite.
- The test driver is `bitmap_tests`, so `lake test` covers the main correctness checks.
- The test suite also includes performance tests that measure the library runtime, including bitmap `putPixel`/`getPixel` performance and PNG encode/decode round-trips.
- When changing performance-sensitive code, pay attention to those performance-test results in addition to pass/fail status.

## Lean Proof Comments

- For newly introduced proof lemmas, add Lean doc comments using `/-- ... -/`.
- Keep each comment to at most a few short lines.
- Each comment should answer two questions:
  - why the lemma exists in the proof
  - what the lemma does at a high level
- Prefer comments that are documentation-visible over ordinary line comments.
