import OeisProofs.DenseList

/-!
# A384222: the statements of formal-conjectures, with proofs

The definitions and the statements below are the same as in
`FormalConjectures/OEIS/384222.lean` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
-/

namespace OeisA384222

/-- The divisors of $n$ in increasing order. -/
def divisorList (n : ℕ) : List ℕ := (List.range' 1 n).filter (· ∣ n)

/-- The 2-dense sublists of divisors of $n$. -/
def denseSublists (n : ℕ) : List (List ℕ) :=
  (divisorList n).splitBy fun d d' => d' ≤ 2 * d

/-- Row $n$ of the triangle: the lengths of the 2-dense sublists of divisors of $n$. -/
def row (n : ℕ) : List ℕ := (denseSublists n).map List.length

/-- Row $n$ of A384225: the numbers of odd terms in the 2-dense sublists of divisors of $n$. -/
def oddRow (n : ℕ) : List ℕ := (denseSublists n).map (List.countP fun d => d % 2 = 1)

theorem conjecture_1 (n : ℕ) (hn : 0 < n) :
    (∀ k ∈ row n, 0 < k) ∧ (row n).sum = n.divisors.card ∧ (row n).reverse = row n := by
  refine ⟨?_, OeisProofs.DenseList.lengths_sum hn, OeisProofs.DenseList.lengths_reverse hn⟩
  intro k hk
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem_splitBy hg)

theorem conjecture_formula (n : ℕ) (hn : 0 < n) :
    row n = (oddRow n).map ((padicValNat 2 n + 1) * ·) := by
  rw [row, oddRow, List.map_map]
  exact List.map_congr_left fun g hg => OeisProofs.DenseList.length_eq hn hg

end OeisA384222
