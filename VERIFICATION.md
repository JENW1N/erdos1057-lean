# Verification evidence and limits

The selected 320-module source snapshot was audited by its source-owning proof task before this publication task extracted it. The recorded audit used Lean 4.35.0-rc2 (compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`), the pinned challenge baseline, `--trust=0`, `-Dweak.google.answer=always_true`, and `-DElab.async=false`.

The recorded output is:

```text
'Bounty.target' depends on axioms: [propext, Classical.choice, Quot.sound]
Bounty.target : True ↔
  Filter.Tendsto (fun x => Real.log (Erdos1057.carmichaelCounting x) / Real.log x) Filter.atTop (nhds 1)
```

This is a parameter-free proof target. The audit checks the exact challenge type and rejects axiom dependencies beyond those three standard axioms. In particular, the recorded closure contains neither `sorryAx` nor the admitted source conjecture. See the [audit entry](verification/modular__canonical__AuditTarget.lean), [output](verification/modular__canonical__audit-target.log), [receipt](verification/modular__canonical__audit-receipt.json), [result](verification/modular__audit-result.json) and [module logs](verification/build-logs/).

The source export is identified by source-lock digest `0f0ee393d8024ecd7b3ebf23889d7bb5bef3833328899cd51ba7cb2fbc213108`. The extraction checked all 320 source hashes and all 993 entries of its original validation manifest against the owner's export. Original object files were checked there but are not committed here. The [original manifest](verification/modular__validation-manifest.json) retains original paths and hashes; it is an evidence record, not a portable launcher.

There are three distinct checks:

1. The source task's completed modular Lean build and exact-target/axiom audit, recorded in the copied evidence.
2. This publication task's byte-identity, packaging, metadata and source-manifest checks. These do not rerun Lean.
3. Independent review and a clean reproduction from the published repository. These remain for reviewers; the portable build instructions have not yet received a successful clean-build receipt.

The original manifest states: “Modular certificate only; assembled source, policy, size, and final wrapper validation are separate.” Its `submission_ready: false` and `source_policy_checked: false` fields are preserved: those separate checks are not certified by the modular receipt, rather than failed modular target checks. No successful Conjectures.io submission, single-file compilation, JSP review, proof acceptance, or prize entitlement is inferred from the modular audit.

The user asked this publication task not to work on the proof. It therefore did not modify proof sources, restart the source task, run Lean, or claim an independent mathematical review. The copied evidence supports the stated modular result, subject to review of the statement correspondence and reproducibility.
