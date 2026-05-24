
# Instructions for GitHub Copilot

This repository contains instructions for GitHub Copilot. These instructions help guide Copilot to generate code that aligns with the project's coding style, conventions, and best practices.

This project is a Lean4 project, so the instructions are tailored to the Lean4 programming language and its ecosystem.

## Instructions for Refactoring Lemmas into Multiple Lemmas

When a proof is long or complex, it may be beneficial to refactor it into multiple lemmas.
When doing so, please follow these guidelines:

- Lean4 uses the syntax `/-- ... -/` for doc comments immediately above the defininiton or theorem it documents.
  Please follow this convention when generating comments.
  Do not separate doc comments from the definitions they document with blank lines or added code.

## Instructions for Golfing Proofs

It is usually better to have shorter proofs, but not at the cost of readability.
When refactoring proofs, please follow these guidelines:

- Avoid using the `;` tactic combinator to combine tactics onto one line.
  Instead, put each tactic on its own line.
- When a rewriting or simplification tactic is used multiple times in a row,
  consider trying to combine them into a single invocation.
- In instances where a one-line `have` statement has been made, and then used once. In such cases, inline the proof of the `have` statement directly into its usage.
- The mathlib style guideline dictate that `simp` should not be used except at the end of a proof block. When refactoring proofs, please replace such calls to `simp` with `simp?`.
