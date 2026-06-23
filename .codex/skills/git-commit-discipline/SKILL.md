---
name: git-commit-discipline
description: Guide Git commits and merges as a software developer with clear, descriptive commit messages, careful staging, non-destructive history handling, and mandatory no-fast-forward merges. Use when Codex is asked to commit, push, merge branches, prepare merge commits, write commit messages, inspect Git changes before committing, or maintain project history with descriptive messages.
---

# Git Commit Discipline

## Core Contract

Create intentional Git history. Every commit must describe what changed and why it belongs together. Merge commits must use no-fast-forward merges and explain what the merged branch contributes.

Never hide unrelated changes in a commit, rewrite published history, squash, rebase, reset hard, or delete branches unless the user explicitly asks. Do not fast-forward merges; use `git merge --no-ff`.

## Before Committing

1. Inspect the worktree.
   - Run `git status --short --branch`.
   - Review staged and unstaged diffs with `git diff` and `git diff --cached`.
   - Identify files changed by the current task versus unrelated user changes.

2. Stage deliberately.
   - Stage only files that belong to the requested change.
   - Keep separate logical changes in separate commits when practical.
   - Do not stage generated files, lockfiles, or metadata churn unless they are required by the change.

3. Verify as appropriate.
   - Run the relevant test/build/lint command for the change when feasible.
   - If verification is skipped or blocked, say exactly why in the final response.

## Commit Messages

Use descriptive messages that let a future developer understand the change without reading the full diff.

Preferred format:

```text
Imperative subject naming the concrete change

Optional body explaining motivation, scope, side effects, or test notes.
```

Good subjects:

- `Add full dynamic PNG encoder proofs`
- `Increase PNG round-trip perf samples`
- `Test CI against latest Lean releases`
- `Document unsupported PNG chunk handling`

Avoid vague subjects:

- `Update`
- `Fix`
- `Changes`
- `WIP`
- `Cleanup`

Use a body when the commit crosses modules, changes behavior, updates generated artifacts, or has important verification context.

## Merge Commits

All merges must be explicit merge commits:

```bash
git merge --no-ff <branch> -m "<subject>" -m "<body>"
```

Do not use a fast-forward merge even when Git can fast-forward. Do not squash unless explicitly requested.

Merge commit subject format:

```text
Merge <branch> into <target>: <short summary>
```

Merge commit body should summarize what is coming from the merged branch. Use a longer body when the branch contains multiple commits or meaningful areas of work:

```text
Merge feature/full_dyn into main: full dynamic PNG encoder

Includes generated dynamic Huffman encoding, decoder round-trip proof coverage,
README support updates, performance-test precision changes, and the package
minor version bump.

Verified with lake test.
```

Before merging:

- Make sure the target branch is current with its remote when the user wants a pushed merge.
- Review `git log --oneline <target>..<branch>` to summarize branch contents.
- Check `git status --short --branch` so local uncommitted changes do not get mixed into the merge.

After merging:

- Run relevant verification on the target branch when feasible.
- Push the target branch only when the user asked to push or the task explicitly requires it.
- Report the merge commit hash, merge message, verification, pushed branch, and final branch status.

## Safety Rules

- Treat uncommitted changes as user-owned until proven otherwise.
- Use non-interactive Git commands.
- If a command would discard or rewrite history, stop and ask unless the user explicitly requested it.
- If a commit fails because hooks or tests fail, inspect and fix the issue instead of bypassing hooks.
- If remote push is rejected, fetch and explain the divergence before choosing a merge/rebase strategy.

