# Machine-Verifiable Law (MVL) — Lean 4 Verification Repository

Lean 4 derivative of the **Foundational Canonical Specification for Machine-Verifiable Law** (Universal Standard Axiom Corporation, October 2026). Under the specification's derivation rule, this repository is a controlled derivative of the canonical semantic root: it carries no authority of its own.

BEGIN WITH PURPOSE. END IN TRUTH.

Pure Lean 4 core: no Mathlib, no external dependencies.

## Build

```bash
# install elan (Lean toolchain manager): https://github.com/leanprover/elan
lake build
```

The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.12.0`). Every push runs `.github/workflows/lean.yml`, which builds the project and checks every proof and golden vector.

## Build status

This repository was written without access to a Lean compiler. **It has not yet been compiled.** The first CI run on GitHub is the first check; if a proof fails, the log names the file and line. As the specification requires, a failed proof must not be reported as successful: until a CI run passes, treat these theorems as *written, not verified*.

## Modules

| File | Contents |
|---|---|
| `Mvl/Verdict.lean` | Three-valued invariant results; `verify : List Truth3 → {ACCEPT, REJECT, UNVERIFIED}` |
| `Mvl/Transition.lean` | Fail-closed transition authorization |
| `Mvl/Obligation.lean` | TRUE / FALSE / UNKNOWN / OBLIGATION; consequential acceptance |
| `Mvl/Refinement.lean` | R³ operator with declared comparison relation; fixed point; diminishing-returns stop; termination |
| `Mvl/Derivation.lean` | Derivative authority, mapping classes, digest admissibility, proof status, reproducibility, supersession |
| `Mvl/GoldenVectors.lean` | 29 concrete cases checked by `decide` |

## Theorems and the specification

| Theorem | Specification statement |
|---|---|
| `reject_of_false`, `contradiction_rejects` | ∃ i : I_i(S) = false ⇒ Verify = REJECT |
| `unknown_not_accept`, `unverified_of_unknown` | UNVERIFIED ≠ ACCEPT; unknown never implies acceptance |
| `accept_of_all_tt`, `accept_no_false`, `accept_no_unknown` | ACCEPT exactly when every mandatory invariant is established true |
| `reject_ne_unverified`, `unverified_ne_accept` | REJECT ≢ UNVERIFIED |
| `not_accept_not_authorized`, `authorized_iff_accept` | Verify ≠ ACCEPT ⇒ transition not authorized by MVL |
| `unknown_condition_blocks`, `violated_condition_blocks`, `integrity_unknown_blocks` | Fail closed; integrity unknown ⇒ Verify ≠ ACCEPT |
| `obligation_not_truth`, `unknown_not_truth`, `obligation_not_fact` | OBLIGATION ≠ Truth; obligations are not recorded as facts |
| `open_obligation_blocks` | Consequential acceptance requires every mandatory obligation |
| `fixed_of_eq`, `iterate_fixed` | R³(C*) ≡_can C* under a declared comparison relation |
| `no_material_change_stops`, `material_change_continues` | Δ(C_n, C_{n+1}) = ∅ ⇒ stop refinement |
| `reaches_fixed_point`, `closure_within_defect_count` | Refinement terminates when each step strictly reduces material defects |
| `meaning_change_invalid` | Removing a defect by changing meaning is not a valid R³ refinement |
| `*_not_authoritative` | No derivative becomes authoritative by being executable or immutable |
| `unresolved_not_equivalence`, `approximation_not_equivalence` | An unresolved mapping is not an established equivalence |
| `more_authority_rejected` | No derivative may contain more authority than its source |
| `fabricated_digest_rejected` | A digest is represented only when actually computed |
| `failed_not_proven`, `unformalized_not_proven` | A failed proof is not a successful proof |
| `reproducible` | J₁ ≡ J₂ ⇒ Verify(J₁) = Verify(J₂) |
| `supersession_preserves_history` | Supersession does not erase historical provenance |

## Scope and known edge case

These proofs cover the model as formalized here. A proof of a formalized proposition is not proof of an unstated proposition outside this formalization. `reproducible` holds because verification is modelled as a pure function; it says nothing about an implementation that depends on hidden state. The R³ termination theorem holds under its stated assumption that each refinement strictly reduces the material-defect count.

**Vacuous acceptance:** `verify []` returns ACCEPT, because with no mandatory invariants every mandatory condition is trivially satisfied. A declared verification domain must therefore list its mandatory invariants explicitly; an empty list means nothing was checked, not that the state is verified.

Choose and add a license before publishing.
