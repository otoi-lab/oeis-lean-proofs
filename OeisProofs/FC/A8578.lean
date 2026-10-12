import OeisProofs.Gerasimova

/-!
# A008578: the statement of formal-conjectures, with a proof

The definitions and the statement below are the same as in
`FormalConjectures/OEIS/8578.lean` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
-/

namespace OeisA8578

open ArithmeticFunction

/-- The predicate for the sequence: $n = 1$ or $n$ is prime. -/
def A (n : ℕ) : Prop := n = 1 ∨ n.Prime

theorem conjecture (k : ℕ) : A k ↔ k * cardFactors k < sigma 1 k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [A, Nat.not_prime_zero]
  · exact OeisProofs.Gerasimova.gerasimova hk

end OeisA8578
