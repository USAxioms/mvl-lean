/-!
# Derivation, provenance, reproducibility, and integrity rules

One canonical semantic root → many controlled representations (Lean 4,
JSONL, Code Ocean, blockchain). No derivative carries more authority
than its source; an unresolved mapping is never an established
equivalence; a digest is represented only when actually computed; a
failed proof is never a successful proof.
-/
namespace Mvl

inductive Representation where
  | canonical
  | lean
  | jsonl
  | codeOcean
  | blockchain
  deriving DecidableEq, Repr

/-- Only the canonical semantic specification carries normative authority. -/
def isAuthoritative : Representation → Bool
  | .canonical => true
  | _ => false

/-- Immutability does not confer authority: a blockchain record is a
provenance function, not the source of meaning. -/
theorem blockchain_not_authoritative : isAuthoritative .blockchain = false := rfl
theorem lean_not_authoritative : isAuthoritative .lean = false := rfl
theorem jsonl_not_authoritative : isAuthoritative .jsonl = false := rfl
theorem codeOcean_not_authoritative : isAuthoritative .codeOcean = false := rfl

/-- Classification of a derivative's semantic relationship to the source. -/
inductive Mapping where
  | exact
  | structurePreserving
  | projection
  | approximation
  | unresolved
  deriving DecidableEq, Repr

def establishesEquivalence : Mapping → Bool
  | .exact => true
  | _ => false

theorem unresolved_not_equivalence : establishesEquivalence .unresolved = false := rfl
theorem approximation_not_equivalence : establishesEquivalence .approximation = false := rfl

/-- Integrity rule 1: a derivative's authority may not exceed its source's. -/
def derivativeOk (sourceRank derivativeRank : Nat) : Bool := decide (derivativeRank ≤ sourceRank)

theorem more_authority_rejected (s d : Nat) (h : s < d) : derivativeOk s d = false := by
  unfold derivativeOk
  exact decide_eq_false (Nat.not_le.mpr h)

/-- A provenance digest is admissible only if it was actually computed. -/
structure Digest where
  value    : Option String
  computed : Bool
  deriving DecidableEq, Repr

def digestAdmissible (d : Digest) : Bool :=
  match d.value with
  | none => true
  | some _ => d.computed

theorem fabricated_digest_rejected (v : String) : digestAdmissible ⟨some v, false⟩ = false := rfl
theorem absent_digest_honest : digestAdmissible ⟨none, false⟩ = true := rfl

/-- Proof status: a failed proof is never reported as successful. -/
inductive ProofStatus where
  | proven
  | failed
  | notFormalized
  deriving DecidableEq, Repr

def reportAsProven : ProofStatus → Bool
  | .proven => true
  | _ => false

theorem failed_not_proven : reportAsProven .failed = false := rfl
theorem unformalized_not_proven : reportAsProven .notFormalized = false := rfl

/-- Reproducibility: verification modelled as a function of
(inputs, rules, versions, execution conditions) gives equal verdicts on
equal inputs. -/
theorem reproducible {J V : Type} (verifyFn : J → V) (j₁ j₂ : J) (h : j₁ = j₂) :
    verifyFn j₁ = verifyFn j₂ := by
  rw [h]

/-- Supersession keeps history: appending a version never removes a prior one. -/
theorem supersession_preserves_history {α : Type} (history : List α) (old new : α)
    (h : old ∈ history) : old ∈ history ++ [new] :=
  List.mem_append_left _ h

end Mvl
