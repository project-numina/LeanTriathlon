# LiveLeanTriathlon

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

This repository contains a benchmark suite of mathematical theorems
formalized in Lean 4.

It has been adapted from the [Lean Project Template repository](https://github.com/pitmonticone/LeanProject).

*Note: This version of the repository has been stripped of the informal and formal proofs to avoid data leakage. Full version is available upon request.*

## Overview

LiveLeanTriathlon is a benchmark
for automated theorem proving and autoformalization in Lean 4.
It consists of a collection of mathematical theorems formalized in Lean 4,
and formalizations of supporting lemmas used in the proofs of these theorems,
along with informal descriptions of these theorems, lemmas, and their proofs
in the form of LaTeX blueprints.
These theorems come from a variety of sources,
including the [1000+ theorems project](https://1000-plus.github.io/),
extensions of projects by individual contributors,
and other mathematical literature. They cover many different mathematical fields.

LiveLeanTriathlon has a few goals:

* To assess the capabilities of automated theorem proving systems
  in Lean 4 on a set of theorems that is more diverse than previous benchmarks
  (which largely focus on competition math) and hopefully more similar to research level mathematics.
* To provide a testbed for autoformalization systems that can take informal descriptions of theorems
  and lemmas and produce formal statements in Lean 4.
* To explore ways of using human-AI collaboration to assist larger scale formalization projects.

Eventually, we hope that LiveLeanTriathlon can help contribute to upstream formalization efforts like
mathlib directly by providing first drafts of formal proofs of important theorems and lemmas
that the community is interested in.

### Repository Layout

The repository is organized as follows (listing the main folders and files):

- ~~`blueprint/src/theorems/`: Contains the LaTeX blueprints for the theorems in the benchmark.~~
- ~~`blueprint/src/content.tex`: The main LaTeX file that includes the individual theorem blueprints as `\input`s.~~
- `LiveLeanTriathlonSorry/<TheoremName>/`: Each theorem has its own directory containing:
  - `All.lean`: The sorried main theorem statement.
  - ~~`MainTheorem.lean`: The main theorem statement and proof.~~
  - ~~`BackgroundLemmas.lean`: Supporting lemmas needed for the main theorem.~~
- `LiveLeanTriathlonSorry/Mathlib/`: Contains any lemmas that are needed but not present in mathlib.

## Licensing

Copyright 2025 Project Numina. All software is licensed under the Apache License,
Version 2.0 (Apache-2.0); you may not use this file except in compliance with
the Apache 2.0 license. You may obtain a copy of the Apache 2.0 license at:
https://www.apache.org/licenses/LICENSE-2.0

The content may be based on third party sources and may in some cases include
third party content. The original source for each theorem is indicated by a
URL within the source file. Third party content may be subject to different
licensing requirements. In particular:

-   Material from Wikipedia articles and MathOverflow is released under the
    Creative Commons Attribution-Share-Alike License 4.0.
-   Material from The Stacks Project is released under the GNU Free
    Documentation License.
-   Material from arXiv is used under the licence applicable to the relevant
    paper, as indicated at the URL within the source file.

Unless required by applicable law or agreed to in writing, all software and
materials distributed here under the Apache 2.0 license are distributed on an
"AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
implied. See the license for the specific language governing permissions and
limitations under the license.

## Acknowledgements

We would like to thank Kim Morrison and Kevin Buzzard for identifying formalization errors in this development.
