
# Contribution Guidelines

Thank you for your interest in contributing to LiveLeanTriathlon!

Pull requests are subject to a CI check that should enforce the most important parts of these guidelines.
Here is a summary of the main points.

## Submitting Theorems

A contribution should add the following files
(respecting case conventions,
with the `.tex` file in `kebab-case` and the `.lean` files in `UpperCamelCase`):

- `/blueprint/src/theorems/theorem-name.tex`
- `/LiveLeanTriathlon/TheoremName/MainTheorem.lean`

And potentially additional files in:

- `/LiveLeanTriathlon/TheoremName/BackgroundLemmas.lean`
- `/LiveLeanTriathlon/Mathlib/`

The content of these files should be as follows:

- `/blueprint/src/theorems/theorem-name.tex`
  - Should contain the LaTeX blueprint proof of the theorem
    - Each lean definition, lemma, or theorem in the `/LiveLeanTriathlon/TheoremName/` directory is referenced in a `definition`, `lemma`, or `theorem` environment.
    - An exception can be made for lemmas that are needed to provide API, such as definition unfolding lemmas.
  - Each such environment should have a `\lean{}` tag to reference to the corresponding Lean declaration in the `/LiveLeanTriathlon/TheoremName/` directory.
  - These environments should also include a standard TeX `\label{}` tag for cross-referencing
  - And also a `\uses{}` tag listing any other lemmas or definitions used by that declaration, if any of these are among those defined in the `/LiveLeanTriathlon/TheoremName/` directory.
  - The `lemma` and `theorem` environments should also be followed by a `proof` environment containing the natural language proof of the lemma or theorem.
  - Submissions should also edit `/blueprint/src/content.tex` to include the blueprint for the theorem.
- `/LiveLeanTriathlon/TheoremName/MainTheorem.lean` and `/LiveLeanTriathlon/TheoremName/BackgroundLemmas.lean`
  - `MainTheorem.lean` should contain the main `theorem` statement, and should import `BackgroundLemmas.lean`
  - `BackgroundLemmas.lean` should contain any supporting `lemma`s mentioned in the blueprint needed for the main theorem.
  - Although, if the amount of content is not too long, it is also acceptable to combine these into one file.
  - Both files should import any files from mathlib that are needed.
  - If mathlib-suitable lemmas are needed but not present in mathlib, these can be placed in `LiveLeanTriathlon/Mathlib/`.
- `/LiveLeanTriathlon/Mathlib/...` (if needed)
  - Should contain any lemmas that are needed but not present in mathlib.
  - These should be written in a style suitable for eventual submission to mathlib.
  - The directory structure should mirror that of mathlib as much as possible, and the files should import their corresponding mathlib files.
  - Files in this directory should not import files from the `/LiveLeanTriathlon/TheoremName/` directories.
    - If a contributor finds that the most mathlib-friendly organization of lemmas for a theorem requires some lemmas that would otherwise go in the `/LiveLeanTriathlon/TheoremName/` directories to prove lemmas in `/LiveLeanTriathlon/Mathlib/`, then there are a few options:
      - Make the mathlib-suitable lemmas part of the blueprint and `/LiveLeanTriathlon/TheoremName/` directories
      - Inline the proofs of the mathlib-suitable lemmas into the proofs in `/LiveLeanTriathlon/TheoremName/`.
      - Add a new file in `/LiveLeanTriathlon/Mathlib/` to hold all of these lemmas, and then add a `assert_not_exists` command to ensure that these proofs cannot be used by models when completng benchmark tasks.
      - Discuss with the maintainers to find the best solution.

### Additional updates

Once the above files have been added, some additional edits should be made:

- A reference to the `/blueprint/src/theorems/theorem-name.tex` file should be made in `/blueprint/src
/content.tex`
- The main `LiveLeanTriathlon.lean` file should be updated to include any new `.lean` files added
  - This can be done by calling `lake exe mk_all --module`

## Proofs

As a project dedicated to the use of AI tools for formalization,
we are interested in leveraging AI tools to help with the formalization of theorems and lemmas,
and we have been using AI to vet and help complete many of the proofs in the repository.
In cases where it seems more efficient to do so,
we encourage contributors to leave parts of proofs that seem difficult or time-consuming for a human
as `sorry` to be completed by an AI tool.
These proof obligations can be marked with a comment such as `-- TODO(AI)`, for example:


```lean
theorem example_theorem (a b : ℕ) : a + b = b + a := by
  -- TODO(AI): Prove commutativity of addition
  sorry
```

In cases where AI has attempted to complete a proof but has not succeeded,
we encourage contributors to leave an inline comment.

```lean
theorem example_theorem (a b c n : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : 3 ≤ n) :
    a ^ n + b ^ n ≠ c ^ n := by
  -- TODO(Human): AI XXX was unable to complete this proof.
  sorry
```

To make this workflow effective, ideally, a partial proof that covers the main ideas of the proof at
hand and references the background lemmas should be provided.
This helps ensure that the formalization of the statement is correct
and that the background lemmas are indeed the right ones.
If this is not possible, contributors and reviewers should scrutinize the statement carefully to ensure its correctness.

If you formulate a formalization of a theorem or lemma and you later discover that it is incorrect,
we would appreciate it if you would add the incorrect version to the `/Mistakes` directory!
We are interested in learning from mistakes as well as successes.

## PR lifecycle and Label management

Each PR contributing a theorem should have an `awaiting-` label
to indicate what the next step in the PR development is,
and whether it needs contributor, maintainer, or AI attention.
Please use one of the following tags to indicate the status of the PR:

* `non-theorem` = Non-theorem changes (CI, docs, config, tooling, scripts) that don't follow the proof pipeline below and should be reviewed and merged promptly
* `awaiting-human-reference-material` = Waiting for human to provide links to reference material in GitHub PR tracker comments
  * Once this is provided, switch to `awaiting-AI-generate-blueprint`
* `awaiting-AI-generate-blueprint` = Waiting for AI to process reference material / pre-existing blueprint into more elaborate blueprint
  * Once this is done, switch to `awaiting-human-blueprint-review`
* `awaiting-human-blueprint-review` = Waiting for human to review blueprint and correct it
  * Ideally, the blueprint will have lemmas for every step of the formal proof.
  * To make the theorem search go well, it is best to also include here Lean statements of the main theorem and definitions that it or the proof depends on.
  * Once the blueprint is good, switch to `awaiting-AI-generate-formal-statements`
* `awaiting-AI-generate-formal-statements` = Waiting for AI to process blueprint into formalized statements
  * AI should generate formal statements and attempt to prove them, then switch to `awaiting-human-review`
* `awaiting-AI-sorry-attempt` = AI should search for sorries and attempt to prove them
  * AI should search for sorries and attempt to prove them, then switch to `awaiting-human-review`
* `awaiting-human-review` = Waiting for human to review and attempt to prove any remaining sorries (Formerly AI-processed)
  * Human should work on sorries until they are confident all remaining sorries are correct, then switch to `awaiting-maintainer-review`
  * Optionally, make partial progress on sorries and switch back to `awaiting-AI-sorry-attempt`
* `awaiting-maintainer-review` = Proof looks good and maintainer should double-check and merge


## Style Guidelines

Submissions should follow the [style guidelines of mathlib](https://leanprover-community.github.io/contribute/style.html) as closely as possible.

Note that, because we are producing relatively short and self-contained proofs,
we may contribute some theorems or lemmas that are more specialized than what would typically be accepted into mathlib.
