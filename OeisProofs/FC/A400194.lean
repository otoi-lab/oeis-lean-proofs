import OeisProofs.DenseList

/-!
# A400194: the statement of formal-conjectures, with a proof

The definitions and the statement below are the same as in
`FormalConjectures/OEIS/400194.lean` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
-/

namespace OeisA400194

/-- The divisors of $n$ in increasing order. -/
def divisorList (n : ℕ) : List ℕ := (List.range' 1 n).filter (· ∣ n)

/-- The 2-dense sublists of divisors of $n$. -/
def denseSublists (n : ℕ) : List (List ℕ) :=
  (divisorList n).splitBy fun d d' => d' ≤ 2 * d

/-- The maximum number of terms in a 2-dense sublist of divisors of $n$. -/
def a (n : ℕ) : ℕ := ((denseSublists n).map List.length).foldr max 0

/-- The maximum number of odd terms in a 2-dense sublist of divisors of $n$ (A400195). -/
def b (n : ℕ) : ℕ := ((denseSublists n).map (List.countP fun d => d % 2 = 1)).foldr max 0

theorem conjecture (n : ℕ) (hn : 0 < n) : a n = (padicValNat 2 n + 1) * b n :=
  OeisProofs.DenseList.maxLength_eq hn

end OeisA400194
