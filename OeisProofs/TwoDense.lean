import Mathlib

/-!
# 2-dense sublists of divisors (OEIS A400194, A400195, A384222)

Write the divisors of `n` in increasing order and cut the list after every divisor `e`
whose successor exceeds `2 * e`. The pieces are the *2-dense sublists* of divisors of `n`.

`SameBlock n d d'` says that `d` and `d'` lie in the same piece: no divisor `e` of `n`
between them (with `min d d' ≤ e < max d d'`) is followed by a gap, i.e. every such `e`
has a divisor of `n` in `(e, 2 * e]`.
-/

namespace OeisProofs.TwoDense

/-- `d` and `d'` lie in the same 2-dense sublist of the divisors of `n`. -/
def SameBlock (n d d' : ℕ) : Prop :=
  ∀ e ∈ n.divisors, min d d' ≤ e → e < max d d' → ∃ f ∈ n.divisors, e < f ∧ f ≤ 2 * e

instance (n d d' : ℕ) : Decidable (SameBlock n d d') := by
  unfold SameBlock; infer_instance

/-- The 2-dense sublist of divisors of `n` that contains `d`. -/
def block (n d : ℕ) : Finset ℕ := n.divisors.filter (SameBlock n d)

/-- A400194: the maximum number of terms in a 2-dense sublist of divisors of `n`. -/
def maxBlock (n : ℕ) : ℕ := n.divisors.sup fun d => (block n d).card

/-- A400195: the maximum number of odd terms in a 2-dense sublist of divisors of `n`. -/
def maxOddBlock (n : ℕ) : ℕ := n.divisors.sup fun d => ((block n d).filter Odd).card

variable {n : ℕ}

theorem sameBlock_comm {a b : ℕ} : SameBlock n a b ↔ SameBlock n b a := by
  simp only [SameBlock, min_comm, max_comm]

theorem sameBlock_refl (a : ℕ) : SameBlock n a a := by
  intro e _ h1 h2
  simp only [min_self, max_self] at h1 h2
  omega

theorem sameBlock_trans {a b c : ℕ} (h1 : SameBlock n a b) (h2 : SameBlock n b c) :
    SameBlock n a c := by
  intro e he hlo hhi
  by_cases h : min a b ≤ e ∧ e < max a b
  · exact h1 e he h.1 h.2
  · apply h2 e he
    · simp only [Nat.min_def, Nat.max_def] at *
      split_ifs at * <;> omega
    · simp only [Nat.min_def, Nat.max_def] at *
      split_ifs at * <;> omega

theorem sameBlock_of_le_two_mul {a b : ℕ} (hb : b ∈ n.divisors) (hab : a ≤ b)
    (hba : b ≤ 2 * a) : SameBlock n a b := by
  intro e _ hlo hhi
  rw [min_eq_left hab] at hlo
  rw [max_eq_right hab] at hhi
  exact ⟨b, hb, hhi, by omega⟩

/-- `o` and `o * 2 ^ i` lie in the same block whenever `o * 2 ^ i ∣ n`. -/
theorem sameBlock_mul_two_pow (hn : n ≠ 0) {o : ℕ} :
    ∀ i, o * 2 ^ i ∣ n → SameBlock n o (o * 2 ^ i)
  | 0, _ => by simpa using sameBlock_refl o
  | i + 1, h => by
    have hx : o * 2 ^ (i + 1) = 2 * (o * 2 ^ i) := by ring
    have h' : o * 2 ^ i ∣ n := (Dvd.intro 2 (by rw [hx]; ring)).trans h
    refine sameBlock_trans (sameBlock_mul_two_pow hn i h') ?_
    rw [hx] at h ⊢
    exact sameBlock_of_le_two_mul (Nat.mem_divisors.mpr ⟨h, hn⟩) (by omega) le_rfl

/-- The key lemma (the conjectured formula of A384222): every 2-dense sublist of divisors of
`n` has `A001511(n) = ν₂(n) + 1` times as many terms as odd terms. -/
theorem card_block (hn : n ≠ 0) (d : ℕ) :
    (block n d).card = (padicValNat 2 n + 1) * ((block n d).filter Odd).card := by
  set v := padicValNat 2 n
  set B := block n d
  rw [mul_comm, ← Finset.card_range (v + 1), ← Finset.card_product]
  symm
  apply Finset.card_nbij' (fun p => p.1 * 2 ^ p.2)
    (fun b => (b / 2 ^ padicValNat 2 b, padicValNat 2 b))
  · rintro ⟨o, j⟩ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range, B, block] at h ⊢
    obtain ⟨⟨⟨ho, hdo⟩, hodd⟩, hj⟩ := h
    have hon : o ∣ n := (Nat.mem_divisors.mp ho).1
    have h2 : 2 ^ j ∣ n := (padicValNat_dvd_iff_le (p := 2) hn).mpr (by omega)
    have hdiv : o * 2 ^ j ∣ n := by
      rw [mul_comm]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)) h2 hon
    exact ⟨Nat.mem_divisors.mpr ⟨hdiv, hn⟩, sameBlock_trans hdo (sameBlock_mul_two_pow hn j hdiv)⟩
  · intro b h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range, B, block] at h ⊢
    obtain ⟨hb, hdb⟩ := h
    have hbn : b ∣ n := (Nat.mem_divisors.mp hb).1
    have hb0 : b ≠ 0 := ne_zero_of_dvd_ne_zero hn hbn
    set w := padicValNat 2 b
    have hpow : 2 ^ w ∣ b := pow_padicValNat_dvd
    have hodd : Odd (b / 2 ^ w) := by
      rw [Nat.odd_iff]
      by_contra hc
      have h2 : 2 ∣ b / 2 ^ w := Nat.dvd_of_mod_eq_zero (by omega)
      apply pow_succ_padicValNat_not_dvd (p := 2) hb0
      have hb : b = b / 2 ^ w * 2 ^ w := (Nat.div_mul_cancel hpow).symm
      conv_rhs => rw [hb]
      rw [pow_succ, mul_comm (b / 2 ^ w)]
      exact Nat.mul_dvd_mul_left _ h2
    have hq : b / 2 ^ w ∣ n := (Nat.div_dvd_of_dvd hpow).trans hbn
    refine ⟨⟨⟨Nat.mem_divisors.mpr ⟨hq, hn⟩, ?_⟩, hodd⟩, ?_⟩
    · have := sameBlock_mul_two_pow hn (o := b / 2 ^ w) w (by rwa [Nat.div_mul_cancel hpow])
      rw [Nat.div_mul_cancel hpow] at this
      exact sameBlock_trans hdb (sameBlock_comm.mp this)
    · have : w ≤ v := (padicValNat_dvd_iff_le (p := 2) hn).mp (hpow.trans hbn)
      omega
  · rintro ⟨o, j⟩ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter] at h
    have hodd : Odd o := h.1.2
    have ho0 : o ≠ 0 := by rintro rfl; simp at hodd
    have hv : padicValNat 2 (o * 2 ^ j) = j := by
      rw [padicValNat.mul ho0 (by positivity), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)), zero_add]
    show (o * 2 ^ j / 2 ^ padicValNat 2 (o * 2 ^ j), padicValNat 2 (o * 2 ^ j)) = (o, j)
    rw [hv, Nat.mul_div_cancel o (by positivity)]
  · intro b _
    show b / 2 ^ padicValNat 2 b * 2 ^ padicValNat 2 b = b
    exact Nat.div_mul_cancel pow_padicValNat_dvd

/-- The conjecture of A400194 and A400195: `A400194(n) = A001511(n) * A400195(n)`. -/
theorem maxBlock_eq (hn : n ≠ 0) : maxBlock n = (padicValNat 2 n + 1) * maxOddBlock n := by
  unfold maxBlock maxOddBlock
  rw [Finset.sup_congr rfl fun d _ => card_block hn d]
  apply le_antisymm
  · exact Finset.sup_le fun d hd => Nat.mul_le_mul_left _ (Finset.le_sup (f := fun d =>
      ((block n d).filter Odd).card) hd)
  · obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_sup n.divisors
      (Finset.nonempty_of_ne_empty (by simp [hn])) fun d => ((block n d).filter Odd).card
    rw [he]
    exact Finset.le_sup (f := fun d => (padicValNat 2 n + 1) * ((block n d).filter Odd).card) hd

/-! ### Symmetry (Conjecture 1 of A384222)

The map `d ↦ n / d` reverses the order of the divisors and preserves the ratio of
consecutive divisors, so it maps 2-dense sublists onto 2-dense sublists. Hence the lengths
of the sublists, read from left to right, form a palindrome. -/

/-- `SameBlock` in terms of consecutive divisors: every pair of consecutive divisors between
`a` and `b` has ratio at most `2`. -/
def Gapfree (n a b : ℕ) : Prop :=
  ∀ x ∈ n.divisors, ∀ y ∈ n.divisors, min a b ≤ x → y ≤ max a b → x < y →
    (∀ z ∈ n.divisors, ¬ (x < z ∧ z < y)) → y ≤ 2 * x

theorem sameBlock_iff_gapfree {a b : ℕ} (ha : a ∈ n.divisors) (hb : b ∈ n.divisors) :
    SameBlock n a b ↔ Gapfree n a b := by
  constructor
  · intro h x hx y hy hlo hhi hxy hcons
    obtain ⟨f, hf, hxf, hf2⟩ := h x hx hlo (lt_of_lt_of_le hxy hhi)
    have : y ≤ f := by
      by_contra hc
      exact hcons f hf ⟨hxf, by omega⟩
    omega
  · intro h e he hlo hhi
    have hmax : max a b ∈ n.divisors := by
      rcases le_total a b with hab | hab
      · rwa [max_eq_right hab]
      · rwa [max_eq_left hab]
    set T := n.divisors.filter (e < ·)
    have hT : T.Nonempty := ⟨max a b, Finset.mem_filter.mpr ⟨hmax, hhi⟩⟩
    have hyT := Finset.min'_mem T hT
    simp only [T, Finset.mem_filter] at hyT
    refine ⟨T.min' hT, hyT.1, hyT.2, ?_⟩
    apply h e he (T.min' hT) hyT.1 hlo
      (Finset.min'_le T _ (Finset.mem_filter.mpr ⟨hmax, hhi⟩)) hyT.2
    rintro z hz ⟨hez, hzy⟩
    exact absurd (Finset.min'_le T z (Finset.mem_filter.mpr ⟨hz, hez⟩)) (not_le.mpr hzy)

theorem div_mul_self_of_mem {x : ℕ} (hx : x ∈ n.divisors) : n / x * x = n :=
  Nat.div_mul_cancel (Nat.mem_divisors.mp hx).1

theorem div_mem_divisors {x : ℕ} (hx : x ∈ n.divisors) : n / x ∈ n.divisors :=
  Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hx).1, (Nat.mem_divisors.mp hx).2⟩

theorem pos_of_mem_divisors' {x : ℕ} (hx : x ∈ n.divisors) : 0 < x :=
  Nat.pos_of_mem_divisors hx

/-- For divisors, `x < y ↔ n / y < n / x`. -/
theorem div_lt_div_iff_of_mem {x y : ℕ} (hx : x ∈ n.divisors) (hy : y ∈ n.divisors) :
    n / y < n / x ↔ x < y := by
  have h1 := div_mul_self_of_mem hx
  have h2 := div_mul_self_of_mem hy
  have := pos_of_mem_divisors' hx
  have := pos_of_mem_divisors' hy
  have := pos_of_mem_divisors' (div_mem_divisors hx)
  have := pos_of_mem_divisors' (div_mem_divisors hy)
  constructor
  · intro h
    by_contra hc
    nlinarith
  · intro h
    by_contra hc
    nlinarith

theorem div_div_of_mem {x : ℕ} (hx : x ∈ n.divisors) : n / (n / x) = x :=
  Nat.div_div_self (Nat.mem_divisors.mp hx).1 (Nat.mem_divisors.mp hx).2

theorem le_div_comm {u v : ℕ} (hu : u ∈ n.divisors) (hv : v ∈ n.divisors) :
    u ≤ n / v ↔ v ≤ n / u := by
  rw [Nat.le_div_iff_mul_le (pos_of_mem_divisors' hv),
    Nat.le_div_iff_mul_le (pos_of_mem_divisors' hu), mul_comm]

theorem div_le_comm {u v : ℕ} (hu : u ∈ n.divisors) (hv : v ∈ n.divisors) :
    n / v ≤ u ↔ n / u ≤ v := by
  have h1 := div_mul_self_of_mem hu
  have h2 := div_mul_self_of_mem hv
  have := pos_of_mem_divisors' hu
  have := pos_of_mem_divisors' hv
  constructor
  · intro h
    by_contra hc
    nlinarith
  · intro h
    by_contra hc
    nlinarith

theorem gapfree_div {a b : ℕ} (ha : a ∈ n.divisors) (hb : b ∈ n.divisors) (h : Gapfree n a b) :
    Gapfree n (n / a) (n / b) := by
  intro x hx y hy hlo hhi hxy hcons
  have hx' := div_mem_divisors hx
  have hy' := div_mem_divisors hy
  have hlt : n / y < n / x := (div_lt_div_iff_of_mem hx hy).mpr hxy
  have key := h (n / y) hy' (n / x) hx' ?_ ?_ hlt ?_
  · -- `n / x ≤ 2 * (n / y)` gives `y ≤ 2 * x`
    have h1 := div_mul_self_of_mem hx
    have h2 := div_mul_self_of_mem hy
    have := pos_of_mem_divisors' hx
    have := pos_of_mem_divisors' hy
    have := pos_of_mem_divisors' hx'
    by_contra hc
    nlinarith
  · -- `min a b ≤ n / y`
    rw [min_le_iff]
    rcases le_max_iff.mp hhi with h' | h'
    · exact Or.inl ((le_div_comm hy ha).mp h')
    · exact Or.inr ((le_div_comm hy hb).mp h')
  · -- `n / x ≤ max a b`
    rw [le_max_iff]
    rcases min_le_iff.mp hlo with h' | h'
    · exact Or.inl ((div_le_comm hx ha).mp h')
    · exact Or.inr ((div_le_comm hx hb).mp h')
  · -- no divisor strictly between `n / y` and `n / x`
    rintro z hz ⟨h1, h2⟩
    have hz' := div_mem_divisors hz
    apply hcons (n / z) hz'
    constructor
    · have := (div_lt_div_iff_of_mem hz hx').mpr h2
      rwa [div_div_of_mem hx] at this
    · have := (div_lt_div_iff_of_mem hy' hz).mpr h1
      rwa [div_div_of_mem hy] at this

theorem sameBlock_div {a b : ℕ} (ha : a ∈ n.divisors) (hb : b ∈ n.divisors)
    (h : SameBlock n a b) : SameBlock n (n / a) (n / b) :=
  (sameBlock_iff_gapfree (div_mem_divisors ha) (div_mem_divisors hb)).mpr
    (gapfree_div ha hb ((sameBlock_iff_gapfree ha hb).mp h))

/-- Conjecture 1 of A384222: `d ↦ n / d` maps the 2-dense sublist of `d` onto the 2-dense
sublist of `n / d`. -/
theorem block_div {d : ℕ} (hd : d ∈ n.divisors) :
    block n (n / d) = (block n d).image (n / ·) := by
  ext e
  simp only [block, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨he, hde⟩
    refine ⟨n / e, ⟨div_mem_divisors he, ?_⟩, div_div_of_mem he⟩
    have := sameBlock_div (div_mem_divisors hd) he hde
    rwa [div_div_of_mem hd] at this
  · rintro ⟨b, ⟨hb, hdb⟩, rfl⟩
    exact ⟨div_mem_divisors hb, sameBlock_div hd hb hdb⟩

/-- The sublists of `d` and `n / d` have the same length. -/
theorem card_block_div {d : ℕ} (hd : d ∈ n.divisors) :
    (block n (n / d)).card = (block n d).card := by
  rw [block_div hd]
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  simp only [Finset.coe_filter, block, Set.mem_ofPred_eq] at hx hy
  have := div_div_of_mem hx.1
  rw [← this, ← div_div_of_mem hy.1]
  exact congrArg (n / ·) hxy

/-! Sanity checks: the definitions reproduce the data of A400194 and A400195. -/

#guard (List.range 100).map (fun i => maxBlock (i + 1)) = [1,2,1,3,1,4,1,4,1,2,1,6,1,2,2,5,1,6,1,6,1,2,1,8,1,2,1,6,1,8,1,6,1,2,2,9,1,2,1,8,1,8,1,3,4,2,1,10,1,2,1,3,1,8,1,8,1,2,1,12,1,2,2,7,1,8,1,3,1,4,1,12,1,2,2,3,2,4,1,10,1,2,1,12,1,2,1,8,1,12,2,3,1,2,1,12,1,2,2,9]

#guard (List.range 105).map (fun i => maxOddBlock (i + 1)) = [1,1,1,1,1,2,1,1,1,1,1,2,1,1,2,1,1,3,1,2,1,1,1,2,1,1,1,2,1,4,1,1,1,1,2,3,1,1,1,2,1,4,1,1,4,1,1,2,1,1,1,1,1,4,1,2,1,1,1,4,1,1,2,1,1,4,1,1,1,2,1,3,1,1,2,1,2,2,1,2,1,1,1,4,1,1,1,2,1,6,2,1,1,1,1,2,1,1,2,3,1,2,1,2,3]

end OeisProofs.TwoDense
