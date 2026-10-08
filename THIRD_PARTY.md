# Third-party sources and attribution

The submitted project credits Jensen Kohlmeyer and Liam Kruer for their project contributions, with AI assistance as described in [AUTHORS.md](AUTHORS.md). It includes and depends on substantial work by others.

- OpenAI mathematics: analytic and other Lean developments retained in `modular/src/OAI/` and incorporated source modules. The original candidate pins upstream source `openai/math` at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Preserve the original source headers. The upstream Apache 2.0 license texts are in `licenses/openai-math-LICENSE` and `licenses/openai-math-lean-LICENSE`.
- Formal Conjectures and its contributors: the problem statement and supporting definitions are copied into `baseline/formal-conjectures`. Their Apache 2.0 license is retained in `licenses/formal-conjectures-LICENSE`. The exact challenge corrections and provenance are supplied in `challenge-pins/` and `baseline/reconstruction.json`.
- Mathlib and Lean contributors: dependencies are pinned in `baseline/formal-conjectures/lake-manifest.json` and are fetched from their original repositories by the build recipe. Their source notices and licenses remain applicable.
- The classical and recent mathematical references used by the original synthesis are identified in the preserved candidate, including D. Larsen’s subgroup-pruning/subset-product strategy, the prime-number and character-sum literature, Korselt’s criterion, and the OpenAI manuscripts. The current account distinguishes reused results from the submitted transfer and subsequent formalization.

This publication preserves existing notices and does not claim ownership of upstream work. No new license grant for independently authored project material is asserted by this attribution note.
