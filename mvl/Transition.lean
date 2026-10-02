import Mvl.Verdict

/-!
# State-transition semantics

A transition S_t → S_{t+1} is admissible only when its verification
returns ACCEPT. Under fail-closed semantics, any other verdict means the
consequential transition is not authorized by MVL.
-/
namespace Mvl

/-- Whether a verdict authorizes a consequential transition. -/
def authorized : Verdict → Bool
  | .accept => true
  | .reject => false
  | .unverified => false

/-- Verify ≠ ACCEPT ⇒ the consequential transition is not authorized. -/
theorem not_accept_not_authorized (v : Verdict) (h : v ≠ .accept) : authorized v = false := by
  cases v with
  | accept => exact absurd rfl h
  | reject => rfl
  | unverified => rfl

theorem authorized_iff_accept (v : Verdict) : authorized v = true ↔ v = .accept := by
  cases v <;> decide

/-- A transition with an unknown mandatory condition is never authorized. -/
theorem unknown_condition_blocks (rs : List Truth3) (h : Truth3.unknown ∈ rs) :
    authorized (verify rs) = false :=
  not_accept_not_authorized _ (unknown_not_accept rs h)

/-- A transition with an affirmatively violated condition is never authorized. -/
theorem violated_condition_blocks (rs : List Truth3) (h : Truth3.ff ∈ rs) :
    authorized (verify rs) = false := by
  rw [reject_of_false rs h] <;> rfl

/-- An integrity condition that cannot be established blocks acceptance:
it enters verification as `unknown`. -/
theorem integrity_unknown_blocks (rs : List Truth3) :
    authorized (verify (Truth3.unknown :: rs)) = false :=
  unknown_condition_blocks _ (List.mem_cons_self _ _)

end Mvl
