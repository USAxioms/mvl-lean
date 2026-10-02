import Mvl.Verdict

/-!
# Unknown and obligation states

Canonical status distinguishes TRUE, FALSE, UNKNOWN, and OBLIGATION.
Neither OBLIGATION nor UNKNOWN is truth. A consequential acceptance
requires every mandatory obligation to be satisfied.
-/
namespace Mvl

inductive Status where
  | true_
  | false_
  | unknown
  | obligation
  deriving DecidableEq, Repr

def isTruth : Status → Bool
  | .true_ => true
  | _ => false

theorem obligation_not_truth : isTruth .obligation = false := rfl
theorem unknown_not_truth : isTruth .unknown = false := rfl

/-- Consequential acceptance: ACCEPT and no open mandatory obligations. -/
def acceptConsequential (v : Verdict) (openObligations : Nat) : Bool :=
  (match v with
   | .accept => true
   | _ => false) && decide (openObligations = 0)

theorem open_obligation_blocks (v : Verdict) (n : Nat) (h : n ≠ 0) :
    acceptConsequential v n = false := by
  unfold acceptConsequential
  rw [decide_eq_false h]
  simp

/-- A ledger entry either is an established fact or an obligation; an
obligation is never silently recorded as a fact. -/
structure LedgerEntry where
  claim  : String
  status : Status
  deriving DecidableEq, Repr

def isEstablishedFact (e : LedgerEntry) : Bool := isTruth e.status

theorem obligation_not_fact (c : String) : isEstablishedFact ⟨c, .obligation⟩ = false := rfl

end Mvl
