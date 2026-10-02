import Mvl.Verdict
import Mvl.Transition
import Mvl.Obligation
import Mvl.Refinement
import Mvl.Derivation

/-!
# Golden vectors

Concrete cases checked by the Lean kernel with `decide`.
-/
namespace Mvl

-- all mandatory invariants true: ACCEPT
example : verify [.tt, .tt, .tt] = .accept := by decide
-- one affirmatively false: REJECT
example : verify [.tt, .ff, .tt] = .reject := by decide
-- false dominates unknown: REJECT
example : verify [.tt, .ff, .unknown] = .reject := by decide
-- unknown without false: UNVERIFIED, never ACCEPT
example : verify [.tt, .tt, .unknown] = .unverified := by decide
example : verify [.unknown] ≠ .accept := by decide
-- empty mandatory set is vacuously accepted (the declared domain must list its invariants)
example : verify [] = .accept := by decide
-- REJECT and UNVERIFIED are distinct
example : Verdict.reject ≠ Verdict.unverified := by decide

-- transitions: only ACCEPT authorizes
example : authorized (verify [.tt, .tt]) = true := by decide
example : authorized (verify [.tt, .unknown]) = false := by decide
example : authorized (verify [.ff]) = false := by decide

-- obligations
example : acceptConsequential .accept 0 = true := by decide
example : acceptConsequential .accept 2 = false := by decide
example : acceptConsequential .unverified 0 = false := by decide
example : isEstablishedFact ⟨"auditor sign-off", .obligation⟩ = false := by decide
example : isEstablishedFact ⟨"balance reconciled", .true_⟩ = true := by decide

-- R³: refinement reaches the fixed point and stops on no material change
example : iterate (fun (n : Nat) => n - 1) 5 5 = 0 := by decide
example : shouldStop [] = true := by decide
example : shouldStop ["contradiction in definition 3"] = false := by decide
example : validRefinement true false = false := by decide
example : validRefinement true true = true := by decide

-- derivation and integrity
example : isAuthoritative .canonical = true := by decide
example : isAuthoritative .blockchain = false := by decide
example : establishesEquivalence .exact = true := by decide
example : establishesEquivalence .projection = false := by decide
example : derivativeOk 1 2 = false := by decide
example : derivativeOk 2 2 = true := by decide
example : digestAdmissible ⟨some "e3b0c442", false⟩ = false := by decide
example : digestAdmissible ⟨some "e3b0c442", true⟩ = true := by decide
example : reportAsProven .failed = false := by decide

end Mvl
