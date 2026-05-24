
*Provide a brief description of the subject matter of the main theorem of this LiveLeanTriathlon entry.*

### References:

- *List any reference material for the theorem here (or in comments below)*

### PR lifecycle and Label management

Each PR contributing a theorem should have an `awaiting-` label
to indicate what the next step in the PR development is,
and whether it needs contributor, maintainer, or AI attention.
Please use one of the following tags to indicate the status of the PR:

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
