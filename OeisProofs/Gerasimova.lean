import Mathlib

/-!
# Gerasimova's conjecture (OEIS A008578)

A008578 lists `1` and the primes. Irina Gerasimova conjectured (2013) that these are exactly
the positive integers `k` with `σ(k) > k * Ω(k)`, where `σ` is the sum of divisors and `Ω`
counts prime factors with multiplicity.

Proof outline. `σ` is submultiplicative, and `σ(k) < k * P` for the largest prime factor `P`
of `k`. If `P + 2 ≤ Ω(k)` this already gives `σ(k) ≤ k * Ω(k)`. Otherwise write `k = P * m`
and use induction on `m`.
-/

namespace OeisProofs.Gerasimova

open ArithmeticFunction

/-- The sum of divisors is submultiplicative. -/
theorem sigma_one_mul_le (a b : ℕ) : sigma 1 (a * b) ≤ sigma 1 a * sigma 1 b := by
  rw [sigma_one_apply, sigma_one_apply, sigma_one_apply, Nat.divisors_mul, Finset.mul_def,
    Finset.sum_mul_sum, ← Finset.sum_product']
  exact Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _

theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (i := 1) hp
  rw [pow_one] at this
  rw [this, Finset.sum_range_succ, Finset.sum_range_one]
  ring

/-- `σ(p^a) * (p - 1) < p^a * p` for a prime `p`. -/
theorem sigma_prime_pow_mul_lt {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigma 1 (p ^ a) * (p - 1) < p ^ a * p := by
  rw [sigma_one_apply_prime_pow hp]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  have key : ∀ a : ℕ, (∑ k ∈ Finset.range (a + 1), (q + 1) ^ k) * q + 1 = (q + 1) ^ (a + 1) := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Finset.sum_range_succ, add_mul, add_right_comm, ih]
      ring
  have := key a
  rw [← pow_succ]
  omega

/-- A product of integers `≥ 2` is at most its maximum times the product of the predecessors. -/
theorem prod_le_sup_mul_prod_sub_one (s : Finset ℕ) :
    s.Nonempty → (∀ x ∈ s, 2 ≤ x) → ∏ x ∈ s, x ≤ s.sup id * ∏ x ∈ s, (x - 1) := by
  induction s using Finset.induction_on_max with
  | empty => intro h; simp at h
  | insert a s hlt ih =>
    intro _ h2
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ha2 : 2 ≤ a := h2 a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hsup : (insert a s).sup id = a := by
      rw [Finset.sup_insert]
      exact sup_eq_left.mpr (Finset.sup_le fun x hx => (hlt x hx).le)
    rw [hsup]
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp only [Finset.prod_empty, mul_one]
      exact Nat.le_mul_of_pos_right a (by omega)
    · have ih' := ih hne fun x hx => h2 x (Finset.mem_insert_of_mem hx)
      have hM : s.sup id ≤ a - 1 := by
        apply Finset.sup_le
        intro x hx
        have := hlt x hx
        simp only [id]
        omega
      calc a * ∏ x ∈ s, x ≤ a * (s.sup id * ∏ x ∈ s, (x - 1)) := Nat.mul_le_mul_left a ih'
        _ ≤ a * ((a - 1) * ∏ x ∈ s, (x - 1)) :=
          Nat.mul_le_mul_left a (Nat.mul_le_mul_right _ hM)

/-- `σ(k) < k * P` whenever `P` bounds every prime factor of `k ≥ 2`. -/
theorem sigma_lt_mul_of_primeFactors_le {k P : ℕ} (hk : 2 ≤ k)
    (hP : ∀ p ∈ k.primeFactors, p ≤ P) : sigma 1 k < k * P := by
  have hk0 : k ≠ 0 := by omega
  set S := k.primeFactors
  have hne : S.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  have hσ : sigma 1 k = ∏ p ∈ S, sigma 1 (p ^ k.factorization p) := by
    rw [IsMultiplicative.multiplicative_factorization _ isMultiplicative_sigma hk0, Finsupp.prod,
      Nat.support_factorization]
  have hkprod : k = ∏ p ∈ S, p ^ k.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hk0]
    rw [Finsupp.prod, Nat.support_factorization]
  have hApos : 0 < ∏ p ∈ S, (p - 1) :=
    Finset.prod_pos fun p hp => by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  have h1 : sigma 1 k * ∏ p ∈ S, (p - 1) < k * ∏ p ∈ S, p := by
    rw [hσ, ← Finset.prod_mul_distrib]
    conv_rhs => rw [hkprod, ← Finset.prod_mul_distrib]
    apply Finset.prod_lt_prod_of_nonempty _ _ hne
    · intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      have : 0 < sigma 1 (p ^ k.factorization p) := by
        rw [sigma_one_apply_prime_pow hp']
        exact Finset.sum_pos (fun _ _ => pow_pos hp'.pos _) (by simp)
      have := hp'.two_le
      exact Nat.mul_pos ‹_› (by omega)
    · intro p hp
      exact sigma_prime_pow_mul_lt (Nat.prime_of_mem_primeFactors hp) _
  have h2 : ∏ p ∈ S, p ≤ P * ∏ p ∈ S, (p - 1) :=
    (prod_le_sup_mul_prod_sub_one S hne fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le).trans
      (Nat.mul_le_mul_right _ (Finset.sup_le hP))
  have : sigma 1 k * ∏ p ∈ S, (p - 1) < k * P * ∏ p ∈ S, (p - 1) := by
    calc _ < k * ∏ p ∈ S, p := h1
      _ ≤ k * (P * ∏ p ∈ S, (p - 1)) := Nat.mul_le_mul_left k h2
      _ = _ := by ring
  exact Nat.lt_of_mul_lt_mul_right this

theorem two_le_cardFactors {k : ℕ} (hk : 2 ≤ k) (hkp : ¬ k.Prime) : 2 ≤ cardFactors k := by
  have h0 : cardFactors k ≠ 0 := by
    rw [cardFactors_apply, ne_eq, List.length_eq_zero_iff, Nat.primeFactorsList_eq_nil]
    omega
  have h1 : cardFactors k ≠ 1 := fun h => hkp (cardFactors_eq_one_iff_prime.mp h)
  omega

/-- The main inequality: `σ(k) ≤ k * Ω(k)` for every composite `k`. -/
theorem sigma_le_mul_cardFactors :
    ∀ k : ℕ, 2 ≤ k → ¬ k.Prime → sigma 1 k ≤ k * cardFactors k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk hkp
  have hk0 : k ≠ 0 := by omega
  have hne : k.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨P, hPmem, hPmax'⟩ := Finset.exists_max_image k.primeFactors id hne
  have hPmax : ∀ p ∈ k.primeFactors, p ≤ P := fun p hp => hPmax' p hp
  have hPp : P.Prime := Nat.prime_of_mem_primeFactors hPmem
  have hP2 := hPp.two_le
  set t := cardFactors k with ht
  have ht2 : 2 ≤ t := two_le_cardFactors hk hkp
  by_cases hsmall : P + 2 ≤ t
  · have := sigma_lt_mul_of_primeFactors_le hk hPmax
    have : k * P ≤ k * t := Nat.mul_le_mul_left k (by omega)
    omega
  obtain ⟨m, rfl⟩ : P ∣ k := Nat.dvd_of_mem_primeFactors hPmem
  have hm0 : m ≠ 0 := by rintro rfl; simp at hk0
  have hcard : t = cardFactors m + 1 := by
    rw [ht, cardFactors_mul hPp.ne_zero hm0, cardFactors_apply_prime hPp, add_comm]
  have hσ : sigma 1 (P * m) ≤ (P + 1) * sigma 1 m := by
    simpa [sigma_one_prime hPp] using sigma_one_mul_le P m
  by_cases ht3 : t = 2
  · have hmp : m.Prime := cardFactors_eq_one_iff_prime.mp (by omega)
    have hmP : m ≤ P := hPmax m (Nat.mem_primeFactors.mpr ⟨hmp, dvd_mul_left m P, hk0⟩)
    have hm2 := hmp.two_le
    rw [sigma_one_prime hmp] at hσ
    rw [ht3]
    by_cases hP3 : 3 ≤ P
    · nlinarith
    · obtain rfl : P = 2 := by omega
      obtain rfl : m = 2 := by omega
      decide
  · have hm2 : 2 ≤ m := by
      by_contra h
      obtain rfl : m = 1 := by omega
      simp [cardFactors_one] at hcard
      omega
    have hmp : ¬ m.Prime := fun h => by rw [cardFactors_apply_prime h] at hcard; omega
    have hlt : m < P * m := by nlinarith
    have ihm := ih m hlt hm2 hmp
    have hle : t ≤ P + 1 := by omega
    calc sigma 1 (P * m) ≤ (P + 1) * sigma 1 m := hσ
      _ ≤ (P + 1) * (m * cardFactors m) := Nat.mul_le_mul_left _ ihm
      _ ≤ P * m * t := by rw [hcard]; nlinarith

/-- Gerasimova's conjecture (OEIS A008578): a positive integer `k` is `1` or a prime
if and only if `σ(k) > k * Ω(k)`. -/
theorem gerasimova {k : ℕ} (hk : 0 < k) : (k = 1 ∨ k.Prime) ↔ k * cardFactors k < sigma 1 k := by
  constructor
  · rintro (rfl | hp)
    · simp [cardFactors_one]
    · rw [cardFactors_apply_prime hp, sigma_one_prime hp]
      omega
  · intro h
    by_contra hc
    have h1 : k ≠ 1 := fun h => hc (Or.inl h)
    have h2 : ¬ k.Prime := fun h => hc (Or.inr h)
    have := sigma_le_mul_cardFactors k (by omega) h2
    omega

/-! Sanity check against the first terms of A008578. -/

#guard (List.range 200).filter (fun k => 0 < k ∧ k * cardFactors k < sigma 1 k) =
  (List.range 200).filter (fun k => k = 1 ∨ k.Prime)

end OeisProofs.Gerasimova
