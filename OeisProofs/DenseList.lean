import Mathlib

/-!
# 2-dense sublists as lists (OEIS A384222, A400194, A400195)

The divisors of `n` in increasing order are split with `List.splitBy` between consecutive
divisors `d < d'` with `d' > 2 * d`. This file proves the facts about these lists that the
OEIS conjectures need.
-/

namespace OeisProofs.DenseList

/-- The divisors of `n` in increasing order. -/
def divisorList (n : ℕ) : List ℕ := (List.range' 1 n).filter (· ∣ n)

/-- The 2-dense sublists of divisors of `n`. -/
def denseSublists (n : ℕ) : List (List ℕ) :=
  (divisorList n).splitBy fun d d' => d' ≤ 2 * d

variable {n : ℕ}

theorem mem_divisorList (hn : 0 < n) {d : ℕ} : d ∈ divisorList n ↔ d ∣ n := by
  simp only [divisorList, List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    have := Nat.pos_of_dvd_of_pos h hn
    have := Nat.le_of_dvd hn h
    exact ⟨⟨by omega, by omega⟩, h⟩

theorem divisorList_pairwise (n : ℕ) : (divisorList n).Pairwise (· < ·) :=
  (List.pairwise_lt_range' 1).filter _

theorem divisorList_nodup (n : ℕ) : (divisorList n).Nodup :=
  (divisorList_pairwise n).imp ne_of_lt

theorem pos_of_mem_divisorList {d : ℕ} (h : d ∈ divisorList n) : 0 < d := by
  simp only [divisorList, List.mem_filter, List.mem_range'_1] at h
  omega

/-! ### Elementary facts about strictly increasing lists -/

theorem head_le_of_pairwise {g : List ℕ} (hg : g.Pairwise (· < ·)) (hne : g ≠ []) {y : ℕ}
    (hy : y ∈ g) : g.head hne ≤ y := by
  obtain ⟨h, t⟩ := g
  · exact absurd rfl hne
  · simp only [List.head_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_rfl
    · exact (List.rel_of_pairwise_cons hg hy).le

theorem le_getLast_of_pairwise {g : List ℕ} (hg : g.Pairwise (· < ·)) (hne : g ≠ []) {y : ℕ}
    (hy : y ∈ g) : y ≤ g.getLast hne := by
  have hsplit := List.dropLast_append_getLast hne
  rw [← hsplit] at hg hy
  rcases List.mem_append.mp hy with hy | hy
  · exact ((List.pairwise_append.mp hg).2.2 y hy _ (List.mem_singleton_self _)).le
  · rw [List.mem_singleton.mp hy]

/-- Two elements `x ≤ y ≤ 2 * x` of a strictly increasing list lie in the same group of
`splitBy`. -/
theorem mem_iff_mem_of_le_two_mul {L : List ℕ} (hL : L.Pairwise (· < ·)) {g : List ℕ}
    (hg : g ∈ L.splitBy fun d d' => d' ≤ 2 * d) {x y : ℕ} (hx : x ∈ L) (hy : y ∈ L)
    (hxy : x ≤ y) (hyx : y ≤ 2 * x) : x ∈ g ↔ y ∈ g := by
  set G := L.splitBy fun d d' => d' ≤ 2 * d
  have hflat : G.flatten = L := List.flatten_splitBy _ _
  have hP := List.pairwise_flatten.mp (hflat ▸ hL)
  have hchain := List.isChain_getLast_head_splitBy (fun d d' => decide (d' ≤ 2 * d)) L
  rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hchain
  have hne : ∀ m ∈ G, m ≠ [] := fun m hm => List.ne_nil_of_mem_splitBy hm
  obtain ⟨A, B, hAB⟩ := List.append_of_mem hg
  have hpw := hP.2
  rw [hAB, List.pairwise_append, List.pairwise_cons] at hpw
  -- every element of `L` lies in `A`, in `g` or in `B`
  have hloc : ∀ z ∈ L, (∃ m ∈ A, z ∈ m) ∨ z ∈ g ∨ (∃ m ∈ B, z ∈ m) := by
    intro z hz
    rw [← hflat, List.mem_flatten] at hz
    obtain ⟨m, hm, hzm⟩ := hz
    rw [hAB, List.mem_append, List.mem_cons] at hm
    rcases hm with hm | rfl | hm
    · exact Or.inl ⟨m, hm, hzm⟩
    · exact Or.inr (Or.inl hzm)
    · exact Or.inr (Or.inr ⟨m, hm, hzm⟩)
  have hgP : g.Pairwise (· < ·) := hP.1 g hg
  constructor
  · intro hxg
    by_contra hyg
    rcases hloc y hy with ⟨m, hm, hym⟩ | hyg' | ⟨m, hm, hym⟩
    · have := hpw.2.2 m hm g (List.mem_cons_self) y hym x hxg
      omega
    · exact hyg hyg'
    · obtain ⟨g', B', rfl⟩ : ∃ g' B', B = g' :: B' := by
        cases B with
        | nil => simp at hm
        | cons g' B' => exact ⟨g', B', rfl⟩
      obtain ⟨ha, hb, hr⟩ := hchain (l₁ := A) (l₂ := B') hAB
      simp only [decide_eq_false_iff_not, not_le] at hr
      have h1 := le_getLast_of_pairwise hgP ha hxg
      have hg'm : g' ∈ G := by rw [hAB]; simp
      have h2 : g'.head hb ≤ y := by
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact head_le_of_pairwise (hP.1 _ hg'm) hb hym
        · exact ((List.pairwise_cons.mp hpw.2.1.2).1 m hm' _ (List.head_mem hb) y hym).le
      omega
  · intro hyg
    by_contra hxg
    rcases hloc x hx with ⟨m, hm, hxm⟩ | hxg' | ⟨m, hm, hxm⟩
    · obtain ⟨A', g'', rfl⟩ : ∃ A' g'', A = A' ++ [g''] := by
        rcases List.eq_nil_or_concat A with rfl | ⟨A', g'', rfl⟩
        · simp at hm
        · exact ⟨A', g'', by simp⟩
      obtain ⟨ha, hb, hr⟩ := hchain (a := g'') (b := g) (l₁ := A') (l₂ := B) (hAB.trans (by simp))
      simp only [decide_eq_false_iff_not, not_le] at hr
      have hg''m : g'' ∈ G := by rw [hAB]; simp
      have h1 : x ≤ g''.getLast ha := by
        rcases List.mem_append.mp hm with hm' | hm'
        · have hpwA := hpw.1
          rw [List.pairwise_append] at hpwA
          exact (hpwA.2.2 m hm' g'' (List.mem_singleton_self _) x hxm _
            (List.getLast_mem ha)).le
        · rw [List.mem_singleton.mp hm'] at hxm
          exact le_getLast_of_pairwise (hP.1 _ hg''m) ha hxm
      have h2 := head_le_of_pairwise hgP hb hyg
      omega
    · exact hxg hxg'
    · have := hpw.2.1.1 m hm y hyg x hxm
      omega

/-! ### Groups are unions of sets `{o, 2o, …, 2^v o}` -/

theorem mem_divisorList_of_mem {g : List ℕ} (hg : g ∈ denseSublists n) {x : ℕ}
    (hx : x ∈ g) : x ∈ divisorList n := by
  rw [← List.flatten_splitBy (fun d d' => decide (d' ≤ 2 * d)) (divisorList n)]
  exact List.mem_flatten.mpr ⟨g, hg, hx⟩

theorem dvd_of_mem (hn : 0 < n) {g : List ℕ} (hg : g ∈ denseSublists n) {x : ℕ} (hx : x ∈ g) :
    x ∣ n :=
  (mem_divisorList hn).mp (mem_divisorList_of_mem hg hx)

theorem mem_iff_mem (hn : 0 < n) {g : List ℕ} (hg : g ∈ denseSublists n) {x y : ℕ}
    (hx : x ∣ n) (hy : y ∣ n) (hxy : x ≤ y) (hyx : y ≤ 2 * x) : x ∈ g ↔ y ∈ g :=
  mem_iff_mem_of_le_two_mul (divisorList_pairwise n) hg ((mem_divisorList hn).mpr hx)
    ((mem_divisorList hn).mpr hy) hxy hyx

theorem mul_two_pow_mem (hn : 0 < n) {g : List ℕ} (hg : g ∈ denseSublists n) {o : ℕ}
    (ho : o ∈ g) : ∀ j, o * 2 ^ j ∣ n → o * 2 ^ j ∈ g
  | 0, _ => by simpa using ho
  | j + 1, h => by
    have hx : o * 2 ^ (j + 1) = 2 * (o * 2 ^ j) := by ring
    have h' : o * 2 ^ j ∣ n := (Dvd.intro 2 (by ring)).trans h
    have ih := mul_two_pow_mem hn hg ho j h'
    rw [hx] at h ⊢
    exact (mem_iff_mem hn hg h' h (by omega) le_rfl).mp ih

theorem mem_of_mul_two_pow_mem (hn : 0 < n) {g : List ℕ} (hg : g ∈ denseSublists n) {o : ℕ} :
    ∀ j, o * 2 ^ j ∈ g → o ∈ g
  | 0, h => by simpa using h
  | j + 1, h => by
    have hx : o * 2 ^ (j + 1) = 2 * (o * 2 ^ j) := by ring
    have hd := dvd_of_mem hn hg h
    have h' : o * 2 ^ j ∣ n := (Dvd.intro 2 (by ring)).trans hd
    apply mem_of_mul_two_pow_mem hn hg j
    rw [hx] at h hd
    exact (mem_iff_mem hn hg h' hd (by omega) le_rfl).mpr h

theorem nodup_of_mem {g : List ℕ} (hg : g ∈ denseSublists n) : g.Nodup := by
  have := List.sublist_flatten_of_mem hg
  rw [denseSublists, List.flatten_splitBy] at this
  exact (divisorList_nodup n).sublist this

/-- Every 2-dense sublist has `ν₂(n) + 1` times as many terms as odd terms. -/
theorem length_eq (hn : 0 < n) {g : List ℕ} (hg : g ∈ denseSublists n) :
    g.length = (padicValNat 2 n + 1) * g.countP (fun d => d % 2 = 1) := by
  have hnd := nodup_of_mem hg
  have hn0 : n ≠ 0 := hn.ne'
  rw [← List.toFinset_card_of_nodup hnd, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (hnd.filter _), List.toFinset_filter]
  set v := padicValNat 2 n
  rw [mul_comm, ← Finset.card_range (v + 1), ← Finset.card_product]
  symm
  apply Finset.card_nbij' (fun p => p.1 * 2 ^ p.2)
    (fun b => (b / 2 ^ padicValNat 2 b, padicValNat 2 b))
  · rintro ⟨o, j⟩ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      List.mem_toFinset, Finset.mem_range, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨ho, hodd⟩, hj⟩ := h
    have hon : o ∣ n := dvd_of_mem hn hg ho
    have h2 : 2 ^ j ∣ n := (padicValNat_dvd_iff_le (p := 2) hn0).mpr (by omega)
    have hdiv : o * 2 ^ j ∣ n := by
      rw [mul_comm]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd))) h2 hon
    exact mul_two_pow_mem hn hg ho j hdiv
  · intro b h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      List.mem_toFinset, Finset.mem_range, decide_eq_true_eq] at h ⊢
    have hbn : b ∣ n := dvd_of_mem hn hg h
    have hb0 : b ≠ 0 := ne_zero_of_dvd_ne_zero hn0 hbn
    set w := padicValNat 2 b
    have hpow : 2 ^ w ∣ b := pow_padicValNat_dvd
    have hodd : b / 2 ^ w % 2 = 1 := by
      by_contra hc
      have h2 : 2 ∣ b / 2 ^ w := Nat.dvd_of_mod_eq_zero (by omega)
      apply pow_succ_padicValNat_not_dvd (p := 2) hb0
      have hb : b = b / 2 ^ w * 2 ^ w := (Nat.div_mul_cancel hpow).symm
      conv_rhs => rw [hb]
      rw [pow_succ, mul_comm (b / 2 ^ w)]
      exact Nat.mul_dvd_mul_left _ h2
    refine ⟨⟨mem_of_mul_two_pow_mem hn hg w (by rwa [Nat.div_mul_cancel hpow]), hodd⟩, ?_⟩
    have : w ≤ v := (padicValNat_dvd_iff_le (p := 2) hn0).mp (hpow.trans hbn)
    omega
  · rintro ⟨o, j⟩ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      decide_eq_true_eq] at h
    have hodd : o % 2 = 1 := h.1.2
    have ho0 : o ≠ 0 := by rintro rfl; simp at hodd
    have hv : padicValNat 2 (o * 2 ^ j) = j := by
      rw [padicValNat.mul ho0 (by positivity), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.mpr hodd), zero_add]
    show (o * 2 ^ j / 2 ^ padicValNat 2 (o * 2 ^ j), padicValNat 2 (o * 2 ^ j)) = (o, j)
    rw [hv, Nat.mul_div_cancel o (by positivity)]
  · intro b _
    show b / 2 ^ padicValNat 2 b * 2 ^ padicValNat 2 b = b
    exact Nat.div_mul_cancel pow_padicValNat_dvd

theorem foldr_max_map_mul (c : ℕ) (l : List ℕ) :
    (l.map (c * ·)).foldr max 0 = c * l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_max_mul_left]

/-- `A400194(n) = A001511(n) * A400195(n)`. -/
theorem maxLength_eq (hn : 0 < n) :
    ((denseSublists n).map List.length).foldr max 0 =
      (padicValNat 2 n + 1) *
        ((denseSublists n).map (List.countP fun d => d % 2 = 1)).foldr max 0 := by
  rw [← foldr_max_map_mul, List.map_map]
  congr 1
  exact List.map_congr_left fun g hg => length_eq hn hg

/-! ### Symmetry under `d ↦ n / d` -/

theorem div_lt_div_of_dvd {a b : ℕ} (hn : 0 < n) (ha : a ∣ n) (hb : b ∣ n) (hab : a < b) :
    n / b < n / a := by
  have h1 := Nat.div_mul_cancel ha
  have h2 := Nat.div_mul_cancel hb
  have := Nat.pos_of_dvd_of_pos ha hn
  have := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd ha) hn
  have := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hb) hn
  by_contra hc
  nlinarith

theorem le_two_mul_iff_of_dvd {a b : ℕ} (hn : 0 < n) (ha : a ∣ n) (hb : b ∣ n) :
    b ≤ 2 * a ↔ n / a ≤ 2 * (n / b) := by
  have h1 := Nat.div_mul_cancel ha
  have h2 := Nat.div_mul_cancel hb
  have := Nat.pos_of_dvd_of_pos ha hn
  have := Nat.pos_of_dvd_of_pos hb hn
  have := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd ha) hn
  have := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hb) hn
  constructor
  · intro h
    by_contra hc
    nlinarith
  · intro h
    by_contra hc
    nlinarith

theorem divisorList_reverse_map (hn : 0 < n) :
    (divisorList n).reverse.map (n / ·) = divisorList n := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) _ (divisorList_pairwise n)
  · intro x
    simp only [List.mem_map, List.mem_reverse, mem_divisorList hn]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact Nat.div_dvd_of_dvd hd
    · intro hx
      exact ⟨n / x, Nat.div_dvd_of_dvd hx, Nat.div_div_self hx hn.ne'⟩
  · rw [List.pairwise_map, List.pairwise_reverse]
    exact (divisorList_pairwise n).imp_of_mem fun ha hb hab =>
      div_lt_div_of_dvd hn ((mem_divisorList hn).mp ha) ((mem_divisorList hn).mp hb) hab

/-- `d ↦ n / d` maps the list of 2-dense sublists onto itself in reverse order. -/
theorem denseSublists_eq_reverse (hn : 0 < n) :
    denseSublists n = ((denseSublists n).map fun g => g.reverse.map (n / ·)).reverse := by
  have hdvd : ∀ g ∈ denseSublists n, ∀ x ∈ g, x ∣ n := fun g hg x hx => dvd_of_mem hn hg hx
  have hne : ∀ g ∈ denseSublists n, g ≠ [] := fun g hg => List.ne_nil_of_mem_splitBy hg
  conv_lhs => rw [denseSublists, ← divisorList_reverse_map hn]
  apply List.splitBy_eq_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.flatten_reverse, List.map_map]
    have : (List.reverse ∘ fun g : List ℕ => g.reverse.map (n / ·)) = List.map (n / ·) := by
      funext g
      simp [List.map_reverse]
    rw [this, ← List.map_flatten, denseSublists, List.flatten_splitBy, List.map_reverse]
  · simp only [List.mem_reverse, List.mem_map, not_exists, not_and]
    intro g hg h
    exact hne g hg (by simpa using h)
  · intro m hm
    simp only [List.mem_reverse, List.mem_map] at hm
    obtain ⟨g, hg, rfl⟩ := hm
    rw [List.isChain_map, List.isChain_reverse]
    have hc := List.isChain_of_mem_splitBy hg
    rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hc ⊢
    intro a b l₁ l₂ hab
    have h := hc hab
    have ha : a ∈ g := by rw [hab]; simp
    have hb : b ∈ g := by rw [hab]; simp
    simp only [decide_eq_true_eq] at h ⊢
    exact (le_two_mul_iff_of_dvd hn (hdvd g hg a ha) (hdvd g hg b hb)).mp h
  · rw [List.isChain_reverse, List.isChain_map]
    have hc := List.isChain_getLast_head_splitBy (fun d d' => decide (d' ≤ 2 * d)) (divisorList n)
    rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hc ⊢
    intro g₁ g₂ l₁ l₂ hab
    obtain ⟨h₁, h₂, h⟩ := hc hab
    have hg₁ : g₁ ∈ denseSublists n := by rw [hab]; simp
    have hg₂ : g₂ ∈ denseSublists n := by rw [hab]; simp
    refine ⟨by simpa using h₂, by simpa using h₁, ?_⟩
    simp only [List.getLast_map, List.getLast_reverse, List.head_map, List.head_reverse,
      decide_eq_false_iff_not] at h ⊢
    rwa [← le_two_mul_iff_of_dvd hn (hdvd g₁ hg₁ _ (List.getLast_mem h₁))
      (hdvd g₂ hg₂ _ (List.head_mem h₂))]

/-- The row of lengths of the 2-dense sublists is a palindrome. -/
theorem lengths_reverse (hn : 0 < n) :
    ((denseSublists n).map List.length).reverse = (denseSublists n).map List.length := by
  conv_rhs => rw [denseSublists_eq_reverse hn]
  simp [List.map_reverse, List.map_map, Function.comp_def]

/-- The lengths of the 2-dense sublists add up to the number of divisors. -/
theorem lengths_sum (hn : 0 < n) :
    ((denseSublists n).map List.length).sum = n.divisors.card := by
  rw [← List.length_flatten, denseSublists, List.flatten_splitBy,
    ← List.toFinset_card_of_nodup (divisorList_nodup n)]
  congr 1
  ext d
  simp [mem_divisorList hn, hn.ne']

end OeisProofs.DenseList
