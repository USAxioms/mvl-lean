/-!
# Verification semantics

Each mandatory invariant evaluates to `tt`, `ff`, or `unknown`.
Verify returns ACCEPT, REJECT, or UNVERIFIED:
* any `ff`            ⇒ REJECT
* else any `unknown`  ⇒ UNVERIFIED
* else                ⇒ ACCEPT
UNVERIFIED ≠ ACCEPT, and REJECT ≢ UNVERIFIED.
-/
namespace Mvl

/-- Result of evaluating one invariant: true, false, or unknown. -/
inductive Truth3 where
  | tt
  | ff
  | unknown
  deriving DecidableEq, Repr

/-- Verification verdict. -/
inductive Verdict where
  | accept
  | reject
  | unverified
  deriving DecidableEq, Repr

def hasFalse : List Truth3 → Bool
  | [] => false
  | .ff :: _ => true
  | .tt :: xs => hasFalse xs
  | .unknown :: xs => hasFalse xs

def hasUnknown : List Truth3 → Bool
  | [] => false
  | .unknown :: _ => true
  | .tt :: xs => hasUnknown xs
  | .ff :: xs => hasUnknown xs

/-- Verify(S, L) over the mandatory invariant results. -/
def verify (rs : List Truth3) : Verdict :=
  match hasFalse rs, hasUnknown rs with
  | true, _ => .reject
  | false, true => .unverified
  | false, false => .accept

theorem hasFalse_of_mem (rs : List Truth3) (h : Truth3.ff ∈ rs) : hasFalse rs = true := by
  induction rs with
  | nil => cases h
  | cons x xs ih =>
    cases x with
    | ff => rfl
    | tt =>
      cases h with
      | tail _ h' => exact ih h'
    | unknown =>
      cases h with
      | tail _ h' => exact ih h'

theorem hasUnknown_of_mem (rs : List Truth3) (h : Truth3.unknown ∈ rs) : hasUnknown rs = true := by
  induction rs with
  | nil => cases h
  | cons x xs ih =>
    cases x with
    | unknown => rfl
    | tt =>
      cases h with
      | tail _ h' => exact ih h'
    | ff =>
      cases h with
      | tail _ h' => exact ih h'

theorem hasFalse_of_all_tt : ∀ rs : List Truth3, (∀ r ∈ rs, r = .tt) → hasFalse rs = false
  | [], _ => rfl
  | x :: xs, h => by
    have hx : x = .tt := h x (List.mem_cons_self x xs)
    subst hx
    exact hasFalse_of_all_tt xs (fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem hasUnknown_of_all_tt : ∀ rs : List Truth3, (∀ r ∈ rs, r = .tt) → hasUnknown rs = false
  | [], _ => rfl
  | x :: xs, h => by
    have hx : x = .tt := h x (List.mem_cons_self x xs)
    subst hx
    exact hasUnknown_of_all_tt xs (fun r hr => h r (List.mem_cons_of_mem _ hr))

/-- An affirmatively false mandatory invariant forces REJECT. -/
theorem reject_of_false (rs : List Truth3) (h : Truth3.ff ∈ rs) : verify rs = .reject := by
  unfold verify
  rw [hasFalse_of_mem rs h] <;> rfl

/-- Fail closed: an unknown mandatory invariant never yields ACCEPT. -/
theorem unknown_not_accept (rs : List Truth3) (h : Truth3.unknown ∈ rs) : verify rs ≠ .accept := by
  unfold verify
  rw [hasUnknown_of_mem rs h]
  cases hasFalse rs <;> decide

/-- With no false invariant, an unknown one yields exactly UNVERIFIED. -/
theorem unverified_of_unknown (rs : List Truth3) (hf : hasFalse rs = false)
    (h : Truth3.unknown ∈ rs) : verify rs = .unverified := by
  unfold verify
  rw [hf, hasUnknown_of_mem rs h] <;> rfl

/-- Every mandatory invariant established true yields ACCEPT. -/
theorem accept_of_all_tt (rs : List Truth3) (h : ∀ r ∈ rs, r = .tt) : verify rs = .accept := by
  unfold verify
  rw [hasFalse_of_all_tt rs h, hasUnknown_of_all_tt rs h] <;> rfl

/-- ACCEPT implies no mandatory invariant is false. -/
theorem accept_no_false (rs : List Truth3) (h : verify rs = .accept) : Truth3.ff ∉ rs := by
  intro hm
  rw [reject_of_false rs hm] at h
  cases h

/-- ACCEPT implies no mandatory invariant is unknown. -/
theorem accept_no_unknown (rs : List Truth3) (h : verify rs = .accept) : Truth3.unknown ∉ rs :=
  fun hm => unknown_not_accept rs hm h

/-- REJECT and UNVERIFIED are distinct verdicts. -/
theorem reject_ne_unverified : Verdict.reject ≠ Verdict.unverified := by decide

/-- UNVERIFIED is not ACCEPT. -/
theorem unverified_ne_accept : Verdict.unverified ≠ Verdict.accept := by decide

/-- Contradiction: one invariant true and another false on the same state is REJECT. -/
theorem contradiction_rejects (rs : List Truth3) (_ht : Truth3.tt ∈ rs) (hf : Truth3.ff ∈ rs) :
    verify rs = .reject :=
  reject_of_false rs hf

end Mvl
