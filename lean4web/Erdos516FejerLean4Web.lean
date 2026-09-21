import Mathlib

/-!
# Erdős 516: standalone Lean4Web proof

This mathlib-only file mirrors the Formal Conjectures Fejér-gap target.  It is
self-contained so it can be opened directly in Lean4Web with Lean v4.35.0-rc2.
-/

namespace Erdos516Target

/-- Fejér gaps: strict increase and summability of reciprocal exponents. -/
def HasFejerGaps (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ Summable (fun k => (n k : ℝ)⁻¹)

/-- The minimum/maximum modulus logarithm ratio from the registered target. -/
noncomputable def ratio (r : ℝ) (f : ℂ → ℂ) : ℝ :=
  (⨅ z : {z : ℂ // ‖z‖ = r}, ‖f z‖).log /
    (⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖).log

end Erdos516Target

namespace Erdos516Proof

/- ## Parameters -/

/-- The paper uses indices `j ≥ 16`; definitions below are total on naturals. -/
def b (j : ℕ) : ℕ := Nat.log 2 j
def N (j : ℕ) : ℕ := 2 ^ (j ^ 2)
def denom (j : ℕ) : ℕ := j * b j ^ 2
def ceilDiv (a d : ℕ) : ℕ := (a + d - 1) / d
def q (j : ℕ) : ℕ := ceilDiv (8 * N j) (denom j)
def m (j : ℕ) : ℕ := 2 * q j
noncomputable def delta (j : ℕ) : ℝ := 1 / ((j : ℝ) * (b j : ℝ))
noncomputable def A (j : ℕ) : ℝ := (N j : ℝ) * delta j

theorem ceilDiv_le {a d c : ℕ} (hd : 0 < d) (h : a ≤ c * d) :
    ceilDiv a d ≤ c := by
  apply Nat.le_of_lt_succ
  rw [ceilDiv, Nat.div_lt_iff_lt_mul hd]
  rw [Nat.succ_mul]
  omega

theorem le_ceilDiv_mul (a : ℕ) {d : ℕ} (hd : 0 < d) : a ≤ ceilDiv a d * d := by
  have hmod := Nat.mod_lt (a + d - 1) hd
  have heq := Nat.mod_add_div (a + d - 1) d
  unfold ceilDiv
  rw [Nat.mul_comm d] at heq
  omega

theorem ceilDiv_mul_le (a d : ℕ) : ceilDiv a d * d ≤ a + d := by
  have h := Nat.div_mul_le_self (a + d - 1) d
  unfold ceilDiv
  omega

theorem b_ge_four {j : ℕ} (hj : 16 ≤ j) : 4 ≤ b j := by
  apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
  norm_num
  exact hj

theorem b_pos {j : ℕ} (hj : 16 ≤ j) : 0 < b j := lt_of_lt_of_le (by norm_num) (b_ge_four hj)

theorem b_le (j : ℕ) : b j ≤ j := Nat.log_le_self 2 j

theorem b_mono : Monotone b := Nat.log_monotone

theorem denom_ge {j : ℕ} (hj : 16 ≤ j) : 256 ≤ denom j := by
  have hb := b_ge_four hj
  have hb2 : 16 ≤ b j ^ 2 := by nlinarith
  have h := Nat.mul_le_mul hj hb2
  simpa [denom] using h

theorem denom_pos {j : ℕ} (hj : 16 ≤ j) : 0 < denom j := lt_of_lt_of_le (by norm_num) (denom_ge hj)

theorem N_pos (j : ℕ) : 0 < N j := by unfold N; positivity

theorem N_ge_sixteen {j : ℕ} (hj : 16 ≤ j) : 16 ≤ N j := by
  have he : 4 ≤ j ^ 2 := by nlinarith
  exact (show 2 ^ 4 ≤ 2 ^ (j ^ 2) from Nat.pow_le_pow_right (by norm_num) he)

theorem four_dvd_N {j : ℕ} (hj : 16 ≤ j) : 4 ∣ N j := by
  have he : 2 ≤ j ^ 2 := by nlinarith
  exact (show 2 ^ 2 ∣ 2 ^ (j ^ 2) from pow_dvd_pow 2 he)

theorem N_even {j : ℕ} (hj : 16 ≤ j) : Even (N j) := by
  exact even_iff_two_dvd.mpr (dvd_trans (by norm_num : 2 ∣ 4) (four_dvd_N hj))

theorem m_even (j : ℕ) : Even (m j) := ⟨q j, by simp [m, two_mul]⟩

theorem q_pos {j : ℕ} (hj : 16 ≤ j) : 0 < q j := by
  have h := le_ceilDiv_mul (8 * N j) (denom_pos hj)
  have hp := N_pos j
  change 8 * N j ≤ q j * denom j at h
  nlinarith

theorem m_pos {j : ℕ} (hj : 16 ≤ j) : 0 < m j := by
  unfold m
  exact Nat.mul_pos (by norm_num) (q_pos hj)

theorem q_le_quarter {j : ℕ} (hj : 16 ≤ j) : q j ≤ N j / 4 := by
  apply ceilDiv_le (denom_pos hj)
  have hd : 32 ≤ denom j := le_trans (by norm_num) (denom_ge hj)
  have hmul := Nat.mul_le_mul_left (N j / 4) hd
  have hdiv := Nat.div_mul_cancel (four_dvd_N hj)
  nlinarith

theorem twice_m_le_N {j : ℕ} (hj : 16 ≤ j) : 2 * m j ≤ N j := by
  have h := q_le_quarter hj
  have hd := Nat.div_mul_le_self (N j) 4
  unfold m
  omega

theorem m_le_half {j : ℕ} (hj : 16 ≤ j) : m j ≤ N j / 2 := by
  have h := twice_m_le_N hj
  omega

theorem N_succ_ge_twice (j : ℕ) : 2 * N j ≤ N (j + 1) := by
  have he : j ^ 2 + 1 ≤ (j + 1) ^ 2 := by
    calc
      j ^ 2 + 1 ≤ j ^ 2 + 2 * j + 1 := by omega
      _ = (j + 1) ^ 2 := by ring
  have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) he
  simpa [N, pow_succ, Nat.mul_comm] using h

theorem blocks_separated {j : ℕ} (hj : 16 ≤ j) : N j + m j < N (j + 1) := by
  have h1 := twice_m_le_N hj
  have h2 := N_succ_ge_twice j
  have h3 := N_pos j
  omega

theorem delta_pos {j : ℕ} (hj : 16 ≤ j) : 0 < delta j := by
  have hb : (0 : ℝ) < b j := by exact_mod_cast b_pos hj
  have hJ : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  unfold delta
  positivity

theorem delta_antitone {i j : ℕ} (hi : 16 ≤ i) (hij : i ≤ j) : delta j ≤ delta i := by
  have hbi : (0 : ℝ) < b i := by exact_mod_cast b_pos hi
  have hiR : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hb : (b i : ℝ) ≤ b j := by exact_mod_cast b_mono hij
  unfold delta
  apply one_div_le_one_div_of_le (mul_pos hiR hbi)
  exact mul_le_mul hijR hb hbi.le (by positivity)

theorem A_pos {j : ℕ} (hj : 16 ≤ j) : 0 < A j := by
  exact mul_pos (by exact_mod_cast N_pos j) (delta_pos hj)

theorem N_strictMono : StrictMono N := by
  apply strictMono_nat_of_lt_succ
  intro j
  have h := N_succ_ge_twice j
  have hp := N_pos j
  omega

theorem pow_four_le_N {j : ℕ} (hj : 16 ≤ j) : j ^ 4 ≤ N j := by
  calc
    j ^ 4 ≤ (2 ^ j) ^ 4 := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) 4
    _ = 2 ^ (j * 4) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (j ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem sq_le_A {j : ℕ} (hj : 16 ≤ j) : (j : ℝ) ^ 2 ≤ A j := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hbR : (0 : ℝ) < b j := by exact_mod_cast b_pos hj
  have hb : (b j : ℝ) ≤ j := by exact_mod_cast b_le j
  have hpow : (j : ℝ) ^ 4 ≤ N j := by exact_mod_cast pow_four_le_N hj
  unfold A delta
  rw [mul_one_div, le_div_iff₀ (mul_pos hjR hbR)]
  calc
    (j : ℝ) ^ 2 * ((j : ℝ) * b j) ≤ (j : ℝ) ^ 2 * ((j : ℝ) * j) := by gcongr
    _ = (j : ℝ) ^ 4 := by ring
    _ ≤ N j := hpow

/- ## Dyadic -/

open Filter Finset
open scoped Topology


noncomputable def weight (j : ℕ) : ℝ := 1 / ((j : ℝ) * (b j : ℝ) ^ 2)

theorem weight_nonneg (j : ℕ) : 0 ≤ weight j := by unfold weight; positivity
theorem delta_nonneg (j : ℕ) : 0 ≤ delta j := by unfold delta; positivity

theorem weight_antitone {i j : ℕ} (hi : 16 ≤ i) (hij : i ≤ j) : weight j ≤ weight i := by
  have hbi : (0 : ℝ) < b i := by exact_mod_cast b_pos hi
  have hiR : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hb : (b i : ℝ) ≤ b j := by exact_mod_cast b_mono hij
  unfold weight
  apply one_div_le_one_div_of_le (mul_pos hiR (sq_pos_of_pos hbi))
  exact mul_le_mul hijR (pow_le_pow_left₀ hbi.le hb 2) (sq_nonneg _) (by positivity)

theorem condensed_weight (k : ℕ) : (2 : ℝ) ^ k * weight (2 ^ k) = 1 / (k : ℝ) ^ 2 := by
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  simp only [weight, b, Nat.log_pow (by norm_num : 1 < 2), Nat.cast_pow, Nat.cast_ofNat]
  rw [one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ hp, one_mul, one_div]

theorem condensed_delta (k : ℕ) : (2 : ℝ) ^ k * delta (2 ^ k) = 1 / (k : ℝ) := by
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  simp only [delta, b, Nat.log_pow (by norm_num : 1 < 2), Nat.cast_pow, Nat.cast_ofNat]
  rw [one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ hp, one_mul, one_div]

theorem summable_weight : Summable weight := by
  apply (summable_condensed_iff_of_eventually_nonneg
    (Eventually.of_forall weight_nonneg) ?_).1
  · simpa only [condensed_weight] using
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  · filter_upwards [eventually_ge_atTop 16] with k hk
    exact weight_antitone hk (Nat.le_succ k)

theorem not_summable_delta : ¬ Summable delta := by
  intro h
  have hc := (summable_condensed_iff_of_eventually_nonneg
    (Eventually.of_forall delta_nonneg)
    (show ∀ᶠ k in atTop, delta (k + 1) ≤ delta k from by
      filter_upwards [eventually_ge_atTop 16] with k hk
      exact delta_antitone hk (Nat.le_succ k))).2 h
  have hh : Summable (fun k : ℕ => 1 / (k : ℝ)) := by
    simpa only [condensed_delta] using hc
  exact Real.not_summable_one_div_natCast hh

/-- `s k` is the left endpoint of block `j = k + 16`. -/
noncomputable def s (k : ℕ) : ℝ := ∑ i ∈ range k, delta (i + 16)

@[simp] theorem s_zero : s 0 = 0 := by simp [s]

theorem s_succ (k : ℕ) : s (k + 1) = s k + delta (k + 16) := by
  simp [s, sum_range_succ]

theorem s_strictMono : StrictMono s := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [s_succ]
  exact lt_add_of_pos_right _ (delta_pos (by omega))

theorem s_nonneg (k : ℕ) : 0 ≤ s k := by
  simpa using s_strictMono.monotone (Nat.zero_le k)

theorem s_tendsto_atTop : Tendsto s atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k => delta_nonneg (k + 16))).1
  intro h
  exact not_summable_delta ((summable_nat_add_iff 16).1 h)

/- ## Gaps -/

open Finset


theorem reciprocal_block_bound {j : ℕ} (hj : 16 ≤ j) :
    ((m j : ℝ) + 1) / N j ≤ 16 * weight j + 3 / N j := by
  have hN : (0 : ℝ) < N j := by exact_mod_cast N_pos j
  have hd : (0 : ℝ) < denom j := by exact_mod_cast denom_pos hj
  have hq : (q j : ℝ) * denom j ≤ 8 * (N j : ℝ) + denom j := by
    exact_mod_cast ceilDiv_mul_le (8 * N j) (denom j)
  have hm : (m j : ℝ) = 2 * q j := by simp [m]
  have hw : weight j = 1 / (denom j : ℝ) := by simp [weight, denom]
  rw [hw, hm]
  apply (div_le_iff₀ hN).2
  apply (mul_le_mul_iff_left₀ hd).mp
  field_simp
  nlinarith

theorem sum_reciprocal_block_le {j : ℕ} (hj : 16 ≤ j) :
    (∑ l : Fin (m j + 1), (1 / (N j + l.val : ℝ))) ≤
      16 * weight j + 3 / N j := by
  apply le_trans _ (reciprocal_block_bound hj)
  calc
    (∑ l : Fin (m j + 1), 1 / (N j + l.val : ℝ)) ≤
        ∑ _l : Fin (m j + 1), 1 / (N j : ℝ) := by
      apply sum_le_sum
      intro l _
      apply one_div_le_one_div_of_le (by exact_mod_cast N_pos j)
      exact le_add_of_nonneg_right (by positivity)
    _ = ((m j : ℝ) + 1) / N j := by simp [div_eq_mul_inv]

theorem summable_reciprocal_N : Summable (fun j : ℕ => 1 / (N j : ℝ)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    (summable_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num))
  intro j
  have hj : j ≤ j ^ 2 := by
    rcases j with _ | j
    · simp
    · nlinarith [Nat.zero_le j]
  have hN : (2 : ℝ) ^ j ≤ N j := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hj
  calc
    1 / (N j : ℝ) ≤ 1 / (2 : ℝ) ^ j := one_div_le_one_div_of_le (by positivity) hN
    _ = (1 / 2 : ℝ) ^ j := by rw [one_div_pow]

theorem summable_reciprocal_block_sums :
    Summable (fun k : ℕ => ∑ l : Fin (m (k + 16) + 1),
      1 / (N (k + 16) + l.val : ℝ)) := by
  have hmajor : Summable (fun j : ℕ => 16 * weight j + 3 / (N j : ℝ)) := by
    simpa only [mul_one_div] using
      (summable_weight.mul_left 16).add (summable_reciprocal_N.mul_left 3)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    ((summable_nat_add_iff 16).2 hmajor)
  intro k
  exact sum_reciprocal_block_le (by omega)

/- ## Terminal -/

open Filter Set


theorem limsup_le_of_eventually_le_nonneg {α : Type*} {l : Filter α}
    {u : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᶠ x in l, u x ≤ c) : limsup u l ≤ c := by
  rw [Filter.limsup_eq]
  by_cases hb : BddBelow {a : ℝ | ∀ᶠ x in l, u x ≤ a}
  · exact csInf_le hb h
  · rw [Real.sInf_of_not_bddBelow hb]
    exact hc

theorem limsup_ne_one_of_eventually_le_half {α : Type*} {l : Filter α}
    {u : α → ℝ} (h : ∀ᶠ x in l, u x ≤ (1 / 2 : ℝ)) :
    limsup u l ≠ 1 := by
  have hle : limsup u l ≤ (1 / 2 : ℝ) :=
    limsup_le_of_eventually_le_nonneg (by norm_num) h
  exact ne_of_lt (lt_of_le_of_lt hle (by norm_num))

/-- The paper's final majorant, with real arithmetic in the polynomial term. -/
noncomputable def ratioMajorant (n : ℕ) : ℝ :=
  5 / 2 ^ (2 * n - 4) + Real.log ((n : ℝ) + 4) / ((n : ℝ) - 1) ^ 2

theorem ratioMajorant_le_half {n : ℕ} (hn : 18 ≤ n) : ratioMajorant n ≤ 1 / 2 := by
  have hnR : (18 : ℝ) ≤ n := by exact_mod_cast hn
  have he : 5 ≤ 2 * n - 4 := by omega
  have hp : (32 : ℝ) ≤ 2 ^ (2 * n - 4) := by
    calc
      (32 : ℝ) = 2 ^ (5 : ℕ) := by norm_num
      _ ≤ 2 ^ (2 * n - 4) := pow_le_pow_right₀ (by norm_num) he
  have hfirst : (5 : ℝ) / 2 ^ (2 * n - 4) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hlog : Real.log ((n : ℝ) + 4) ≤ (n : ℝ) + 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n + 4 by positivity)
    linarith
  have hpoly : (n : ℝ) + 3 ≤ ((n : ℝ) - 1) ^ 2 / 4 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n - 18 by linarith)
      (show (0 : ℝ) ≤ n + 12 by positivity)]
  have hsecond : Real.log ((n : ℝ) + 4) / ((n : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos (show (0 : ℝ) < n - 1 by linarith))).2
    linarith
  unfold ratioMajorant
  linarith

/- ## Enumeration -/

open Set


abbrev Index := Σ k : ℕ, Fin (m (k + 16) + 1)

def exponent (x : Index) : ℕ := N (x.1 + 16) + x.2.val

theorem exponent_lt_of_block_lt {x y : Index} (h : x.1 < y.1) : exponent x < exponent y := by
  have hblock := blocks_separated (show 16 ≤ x.1 + 16 by omega)
  have hN := N_strictMono.monotone (show x.1 + 16 + 1 ≤ y.1 + 16 by omega)
  have hx := x.2.isLt
  unfold exponent
  omega

theorem exponent_injective : Function.Injective exponent := by
  rintro ⟨k, l⟩ ⟨k', l'⟩ h
  have hk : k = k' := by
    rcases lt_trichotomy k k' with hlt | heq | hgt
    · exact False.elim ((ne_of_lt (exponent_lt_of_block_lt hlt)) h)
    · exact heq
    · exact False.elim ((ne_of_lt (exponent_lt_of_block_lt hgt)) h.symm)
  subst k'
  have hl : l = l' := by
    apply Fin.ext
    change N (k + 16) + l.val = N (k + 16) + l'.val at h
    omega
  subst l'
  rfl

def support : Set ℕ := range exponent

theorem support_infinite : support.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => N (k + 16)) :=
    N_strictMono.injective.comp (fun _ _ h => by omega)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨k, rfl⟩
  exact ⟨⟨k, ⟨0, by omega⟩⟩, by simp [exponent]⟩

noncomputable def exponents : ℕ → ℕ := Nat.nth (fun n => n ∈ support)

theorem exponents_strictMono : StrictMono exponents := Nat.nth_strictMono support_infinite

theorem exponents_mem (k : ℕ) : exponents k ∈ support :=
  Nat.nth_mem_of_infinite support_infinite k

noncomputable def indexOf (k : ℕ) : Index := Classical.choose (exponents_mem k)

theorem exponent_indexOf (k : ℕ) : exponent (indexOf k) = exponents k :=
  Classical.choose_spec (exponents_mem k)

theorem indexOf_injective : Function.Injective indexOf := by
  intro i j hij
  apply exponents_strictMono.injective
  simpa only [Function.comp_def, exponent_indexOf] using congrArg exponent hij

theorem indexOf_surjective : Function.Surjective indexOf := by
  intro x
  have hr : range exponents = support := Nat.range_nth_of_infinite support_infinite
  have hx : exponent x ∈ range exponents := by rw [hr]; exact ⟨x, rfl⟩
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, exponent_injective ?_⟩
  rw [exponent_indexOf, hk]

noncomputable def enumeration : ℕ ≃ Index :=
  Equiv.ofBijective indexOf ⟨indexOf_injective, indexOf_surjective⟩

theorem summable_reciprocal_exponent : Summable (fun x : Index => (exponent x : ℝ)⁻¹) := by
  apply (summable_sigma_of_nonneg (fun x => by positivity)).2
  constructor
  · intro k
    exact (hasSum_fintype _).summable
  · simpa only [exponent, tsum_fintype, one_div, Nat.cast_add] using summable_reciprocal_block_sums

theorem exponents_hasFejerGaps : Erdos516Target.HasFejerGaps exponents := by
  refine ⟨exponents_strictMono, ?_⟩
  have h := summable_reciprocal_exponent.comp_injective indexOf_injective
  simpa only [Function.comp_def, exponent_indexOf] using h

/- ## Blocks -/

open Finset


/-- Left-endpoint height, corresponding to the paper's `H_(j-1)`. -/
noncomputable def H (k : ℕ) : ℝ :=
  ∑ i ∈ range k, ((N (i + 16) : ℝ) + q (i + 16)) * delta (i + 16)

noncomputable def t (k : ℕ) : ℝ := s k + delta (k + 16) / 2
noncomputable def R (k : ℕ) : ℝ := Real.exp (t k)
noncomputable def c (k : ℕ) : ℝ :=
  Real.exp (H k - (N (k + 16) : ℝ) * s k) /
    (1 + Real.exp (-delta (k + 16) / 2)) ^ m (k + 16)

noncomputable def block (k : ℕ) (z : ℂ) : ℂ :=
  (c k : ℂ) * z ^ N (k + 16) * (1 - z / (R k : ℂ)) ^ m (k + 16)

noncomputable def coefficient (x : Index) : ℂ :=
  (c x.1 : ℂ) * (-1) ^ x.2.val * (Nat.choose (m (x.1 + 16)) x.2.val : ℂ) /
    (R x.1 : ℂ) ^ x.2.val

noncomputable def coefficients (k : ℕ) : ℂ := coefficient (indexOf k)

/-- Defining a tsum does not assert convergence; convergence is proved separately. -/
noncomputable def f (z : ℂ) : ℂ := ∑' k : ℕ, block k z

theorem R_pos (k : ℕ) : 0 < R k := Real.exp_pos _
theorem c_pos (k : ℕ) : 0 < c k := by unfold c; positivity

theorem coefficient_ne_zero (x : Index) : coefficient x ≠ 0 := by
  have hc : (c x.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (c_pos x.1).ne'
  have hR : (R x.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (R_pos x.1).ne'
  have hbin : (Nat.choose (m (x.1 + 16)) x.2.val : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : x.2.val ≤ m (x.1 + 16))).ne'
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ (by norm_num))) hbin)
    (pow_ne_zero _ hR)

theorem coefficients_ne_zero (k : ℕ) : coefficients k ≠ 0 := coefficient_ne_zero _

@[simp] theorem H_zero : H 0 = 0 := by simp only [H, range_zero, sum_empty]
theorem H_succ (k : ℕ) :
    H (k + 1) = H k + ((N (k + 16) : ℝ) + q (k + 16)) * delta (k + 16) := by
  simp only [H, sum_range_succ]

theorem H_nonneg (k : ℕ) : 0 ≤ H k := by
  unfold H
  apply sum_nonneg
  intro i _
  exact mul_nonneg (by positivity) (delta_nonneg _)

theorem block_at_zero (k : ℕ) : block k 0 = 0 := by
  simp only [block, zero_pow (N_pos (k + 16)).ne', mul_zero, zero_mul]

theorem differentiable_block (k : ℕ) : Differentiable ℂ (block k) := by
  unfold block
  exact ((differentiable_const _).mul (differentiable_id.pow _)).mul
    (((differentiable_const _).sub (differentiable_id.div_const _)).pow _)

/- ## Growth -/

theorem b_succ_le {j : ℕ} (hj : 16 ≤ j) : b (j + 1) ≤ b j + 1 := by
  calc
    b (j + 1) ≤ b (j * 2) := b_mono (by omega)
    _ = b j + 1 := Nat.log_mul_base (by norm_num) (by omega)

theorem delta_denominator_succ_le {j : ℕ} (hj : 16 ≤ j) :
    ((j + 1 : ℕ) : ℝ) * b (j + 1) ≤ 2 * (j : ℝ) * b j := by
  have hjR : (16 : ℝ) ≤ j := by exact_mod_cast hj
  have hbR : (4 : ℝ) ≤ b j := by exact_mod_cast b_ge_four hj
  have hbs : (b (j + 1) : ℝ) ≤ b j + 1 := by exact_mod_cast b_succ_le hj
  have hprod : ((j : ℝ) + 1) * ((b j : ℝ) + 1) ≤ 2 * j * b j := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ j - 2 by linarith)
      (show (0 : ℝ) ≤ b j - 2 by linarith)]
  push_cast
  exact (mul_le_mul_of_nonneg_left hbs (by positivity)).trans hprod

theorem delta_le_twice_succ {j : ℕ} (hj : 16 ≤ j) : delta j ≤ 2 * delta (j + 1) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hb0 : (0 : ℝ) < b j := by exact_mod_cast b_pos hj
  have hbs0 : (0 : ℝ) < b (j + 1) := by exact_mod_cast b_pos (by omega : 16 ≤ j + 1)
  have h := delta_denominator_succ_le hj
  unfold delta
  rw [mul_one_div, div_le_div_iff₀ (mul_pos hj0 hb0) (by positivity)]
  simpa only [one_mul, mul_assoc] using h

theorem N_succ_eq (j : ℕ) : N (j + 1) = N j * 2 ^ (2 * j + 1) := by
  unfold N
  rw [show (j + 1) ^ 2 = j ^ 2 + (2 * j + 1) by ring, pow_add]

theorem A_succ_growth {j : ℕ} (hj : 16 ≤ j) : (2 : ℝ) ^ (2 * j) * A j ≤ A (j + 1) := by
  have hN : (N (j + 1) : ℝ) = (N j : ℝ) * (2 : ℝ) ^ (2 * j + 1) := by
    exact_mod_cast N_succ_eq j
  have hδ := delta_le_twice_succ hj
  unfold A
  calc
    (2 : ℝ) ^ (2 * j) * ((N j : ℝ) * delta j) ≤
        (2 : ℝ) ^ (2 * j) * ((N j : ℝ) * (2 * delta (j + 1))) := by gcongr
    _ = (N (j + 1) : ℝ) * delta (j + 1) := by rw [hN, pow_succ]; ring

theorem four_mul_A_le_succ {j : ℕ} (hj : 16 ≤ j) : 4 * A j ≤ A (j + 1) := by
  have he : 2 ≤ 2 * j := by omega
  have hp : (4 : ℝ) ≤ 2 ^ (2 * j) := by
    have hp := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) he
    norm_num at hp
    exact hp
  exact (mul_le_mul_of_nonneg_right hp (A_pos hj).le).trans (A_succ_growth hj)

theorem height_step_le {j : ℕ} (hj : 16 ≤ j) :
    ((N j : ℝ) + q j) * delta j ≤ 3 / 2 * A j := by
  have hq : (q j : ℝ) ≤ (N j : ℝ) / 2 := by
    have h := twice_m_le_N hj
    unfold m at h
    have hNat : 4 * q j ≤ N j := by omega
    have hR : 4 * (q j : ℝ) ≤ N j := by exact_mod_cast hNat
    have hq0 : (0 : ℝ) ≤ q j := by positivity
    linarith
  have h := mul_le_mul_of_nonneg_right hq (delta_pos hj).le
  unfold A
  nlinarith

theorem height_bounds (k : ℕ) :
    A (k + 16) ≤ H (k + 1) ∧ H (k + 1) ≤ 2 * A (k + 16) := by
  induction k with
  | zero =>
    rw [H_succ, H_zero]
    have hδ := delta_pos (show 16 ≤ 0 + 16 by omega)
    have hs := height_step_le (show 16 ≤ 0 + 16 by omega)
    have hq : (0 : ℝ) ≤ q (0 + 16) * delta (0 + 16) := mul_nonneg (by positivity) hδ.le
    have hA := A_pos (show 16 ≤ 0 + 16 by omega)
    constructor
    · dsimp [A]; nlinarith
    · nlinarith
  | succ k ih =>
    rw [H_succ (k + 1)]
    have hg : 4 * A (k + 16) ≤ A (k + 1 + 16) := by
      simpa only [Nat.add_right_comm k 1 16] using four_mul_A_le_succ (show 16 ≤ k + 16 by omega)
    have hs := height_step_le (show 16 ≤ k + 1 + 16 by omega)
    have hH := H_nonneg (k + 1)
    have hq : (0 : ℝ) ≤ q (k + 1 + 16) * delta (k + 1 + 16) :=
      mul_nonneg (by positivity) (delta_pos (by omega)).le
    constructor
    · dsimp [A] at *; nlinarith
    · nlinarith [ih.2]

theorem height_previous_le (k : ℕ) : H k ≤ A (k + 16) / 2 := by
  cases k with
  | zero =>
    rw [H_zero]
    exact div_nonneg (A_pos (by omega)).le (by norm_num)
  | succ k =>
    have hh := (height_bounds k).2
    have hg : 4 * A (k + 16) ≤ A (k + 1 + 16) := by
      simpa only [Nat.add_right_comm k 1 16] using four_mul_A_le_succ (show 16 ≤ k + 16 by omega)
    change H (k + 1) ≤ A (k + 1 + 16) / 2
    linarith

/- ## BlockAlgebra -/

open Finset


noncomputable def majorant (k : ℕ) (r : ℝ) : ℝ :=
  c k * r ^ N (k + 16) * (1 + r / R k) ^ m (k + 16)

noncomputable def realBlock (k : ℕ) (r : ℝ) : ℝ :=
  c k * r ^ N (k + 16) * (1 - r / R k) ^ m (k + 16)

theorem binomial_fin {K : Type*} [CommSemiring K] (w : K) (d : ℕ) :
    (∑ l : Fin (d + 1), w ^ l.val * (Nat.choose d l.val : K)) = (1 + w) ^ d := by
  rw [Fin.sum_univ_eq_sum_range (fun l => w ^ l * (Nat.choose d l : K))]
  simpa only [one_pow, mul_one, add_comm] using (add_pow w 1 d).symm

theorem block_expansion (k : ℕ) (z : ℂ) :
    (∑ l : Fin (m (k + 16) + 1), coefficient ⟨k, l⟩ * z ^ exponent ⟨k, l⟩) =
      block k z := by
  calc
    _ = ∑ l : Fin (m (k + 16) + 1),
        ((c k : ℂ) * z ^ N (k + 16)) *
          ((-z / (R k : ℂ)) ^ l.val * (Nat.choose (m (k + 16)) l.val : ℂ)) := by
      apply sum_congr rfl
      intro l _
      simp only [coefficient, exponent, pow_add, div_pow]
      rw [neg_pow z]
      ring
    _ = (c k : ℂ) * z ^ N (k + 16) * (1 + -z / (R k : ℂ)) ^ m (k + 16) := by
      rw [← mul_sum, binomial_fin]
    _ = block k z := by simp only [block, neg_div, sub_eq_add_neg]

theorem majorant_nonneg (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ majorant k r := by
  unfold majorant
  exact mul_nonneg (mul_nonneg (c_pos k).le (pow_nonneg hr _))
    (pow_nonneg (add_nonneg (by norm_num) (div_nonneg hr (R_pos k).le)) _)

theorem ofReal_realBlock (k : ℕ) (r : ℝ) : (realBlock k r : ℂ) = block k (r : ℂ) := by
  simp only [realBlock, block, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div]

theorem realBlock_nonneg (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ realBlock k r := by
  unfold realBlock
  exact mul_nonneg (mul_nonneg (c_pos k).le (pow_nonneg hr _))
    ((m_even (k + 16)).pow_nonneg _)

theorem block_neg_real (k : ℕ) (r : ℝ) : block k (-(r : ℂ)) = (majorant k r : ℂ) := by
  simp only [block, (N_even (show 16 ≤ k + 16 by omega)).neg_pow,
    neg_div, sub_neg_eq_add, majorant, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_div]

theorem norm_block_le (k : ℕ) (z : ℂ) : ‖block k z‖ ≤ majorant k ‖z‖ := by
  have hR : ‖(R k : ℂ)‖ = R k := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (R_pos k)]
  have hc : ‖(c k : ℂ)‖ = c k := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (c_pos k)]
  have hsub : ‖1 - z / (R k : ℂ)‖ ≤ 1 + ‖z‖ / R k := by
    simpa only [norm_one, norm_div, hR] using norm_sub_le (1 : ℂ) (z / (R k : ℂ))
  simp only [block, norm_mul, norm_pow, hc, majorant]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsub _)
    (mul_nonneg (c_pos k).le (pow_nonneg (norm_nonneg z) _))

theorem sum_norm_monomials (k : ℕ) (z : ℂ) :
    (∑ l : Fin (m (k + 16) + 1), ‖coefficient ⟨k, l⟩ * z ^ exponent ⟨k, l⟩‖) =
      majorant k ‖z‖ := by
  have hR : ‖(R k : ℂ)‖ = R k := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (R_pos k)]
  have hc : ‖(c k : ℂ)‖ = c k := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (c_pos k)]
  calc
    _ = ∑ l : Fin (m (k + 16) + 1),
        (c k * ‖z‖ ^ N (k + 16)) *
          ((‖z‖ / R k) ^ l.val * (Nat.choose (m (k + 16)) l.val : ℝ)) := by
      apply sum_congr rfl
      intro l _
      simp only [coefficient, exponent, norm_mul, norm_div, norm_pow, norm_neg, norm_one,
        one_pow, mul_one, hc, hR, Complex.norm_natCast, pow_add, div_pow]
      ring
    _ = majorant k ‖z‖ := by rw [← mul_sum, binomial_fin]; rfl

/- ## Envelope -/

noncomputable def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

theorem softplus_mono : Monotone softplus := by
  intro x y h
  apply Real.log_le_log (by positivity)
  exact add_le_add_right (Real.exp_le_exp.mpr h) _

theorem softplus_increment_le {x y : ℝ} (h : x ≤ y) : softplus y - softplus x ≤ y - x := by
  have he : 1 ≤ Real.exp (y - x) := Real.one_le_exp_iff.mpr (sub_nonneg.mpr h)
  have hid : Real.exp (y - x) * Real.exp x = Real.exp y := by
    rw [← Real.exp_add, sub_add_cancel]
  have hmul : 1 + Real.exp y ≤ Real.exp (y - x) * (1 + Real.exp x) := by
    rw [mul_add, mul_one, hid]
    linarith
  have hl := Real.log_le_log (by positivity : 0 < 1 + Real.exp y) hmul
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp] at hl
  unfold softplus
  linarith

theorem softplus_reflect (x : ℝ) : softplus x - softplus (-x) = x := by
  have hid : 1 + Real.exp x = Real.exp x * (1 + Real.exp (-x)) := by
    rw [mul_add, mul_one, ← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero]
    ring
  unfold softplus
  rw [hid, Real.log_mul (by positivity) (by positivity), Real.log_exp]
  ring

/-- The logarithmic envelope, normalized at the left endpoint. -/
noncomputable def F (k : ℕ) (u : ℝ) : ℝ :=
  H k + (N (k + 16) : ℝ) * (u - s k) +
    (m (k + 16) : ℝ) * (softplus (u - t k) - softplus (-delta (k + 16) / 2))

theorem F_left (k : ℕ) : F k (s k) = H k := by
  have ht : s k - t k = -delta (k + 16) / 2 := by unfold t; ring
  simp only [F, ht, sub_self, mul_zero, add_zero]

theorem F_right (k : ℕ) : F k (s (k + 1)) = H (k + 1) := by
  have ht : s (k + 1) - t k = delta (k + 16) / 2 := by rw [s_succ]; unfold t; ring
  have hs : s (k + 1) - s k = delta (k + 16) := by rw [s_succ]; ring
  have hr : softplus (delta (k + 16) / 2) - softplus (-delta (k + 16) / 2) =
      delta (k + 16) / 2 := by
    simpa only [neg_div] using softplus_reflect (delta (k + 16) / 2)
  rw [F, ht, hs, hr, H_succ]
  simp only [m, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem F_increment {k : ℕ} {u v : ℝ} (h : u ≤ v) :
    (N (k + 16) : ℝ) * (v - u) ≤ F k v - F k u ∧
      F k v - F k u ≤ ((N (k + 16) : ℝ) + m (k + 16)) * (v - u) := by
  have hm : (0 : ℝ) ≤ m (k + 16) := by positivity
  have hsp : 0 ≤ softplus (v - t k) - softplus (u - t k) :=
    sub_nonneg.mpr (softplus_mono (sub_le_sub_right h _))
  have hsp' : softplus (v - t k) - softplus (u - t k) ≤ v - u := by
    have h' := softplus_increment_le (sub_le_sub_right h (t k))
    convert h' using 1; ring
  have hl := mul_nonneg hm hsp
  have hu := mul_le_mul_of_nonneg_left hsp' hm
  unfold F
  constructor <;> nlinarith

theorem F_mono (k : ℕ) : Monotone (F k) := by
  intro u v huv
  have h := (F_increment (k := k) huv).1
  have hn : (0 : ℝ) ≤ (N (k + 16) : ℝ) * (v - u) := by positivity
  linarith

theorem log_c (k : ℕ) : Real.log (c k) = H k - (N (k + 16) : ℝ) * s k -
    (m (k + 16) : ℝ) * softplus (-delta (k + 16) / 2) := by
  rw [c, Real.log_div (by positivity) (by positivity), Real.log_exp, Real.log_pow]
  rfl

theorem majorant_exp_pos (k : ℕ) (u : ℝ) : 0 < majorant k (Real.exp u) := by
  unfold majorant
  have hc := c_pos k
  have hR := R_pos k
  positivity

theorem log_majorant_exp (k : ℕ) (u : ℝ) :
    Real.log (majorant k (Real.exp u)) = F k u := by
  have hbase : 0 < 1 + Real.exp u / R k := by have := R_pos k; positivity
  have hdiv : Real.exp u / R k = Real.exp (u - t k) := by rw [R, Real.exp_sub]
  rw [majorant, Real.log_mul (by have := c_pos k; positivity) (by positivity),
    Real.log_mul (c_pos k).ne' (by positivity), Real.log_pow, Real.log_exp,
    Real.log_pow, log_c, hdiv]
  unfold F softplus
  ring

theorem majorant_exp_eq (k : ℕ) (u : ℝ) : majorant k (Real.exp u) = Real.exp (F k u) := by
  rw [← log_majorant_exp, Real.exp_log (majorant_exp_pos k u)]

theorem F_future (k : ℕ) {u : ℝ} (hu : u ≤ s k) :
    F (k + 1) u ≤ -A (k + 17) / 2 := by
  have hs : u ≤ s (k + 1) := hu.trans (s_strictMono.monotone (Nat.le_succ k))
  have hi := (F_increment (k := k + 1) hs).1
  rw [F_left, s_succ] at hi
  have hd := delta_antitone (show 16 ≤ k + 16 by omega) (show k + 16 ≤ k + 17 by omega)
  have hN : (0 : ℝ) ≤ N (k + 17) := by positivity
  have hd' := mul_le_mul_of_nonneg_left hd hN
  have hu' := mul_le_mul_of_nonneg_left hu hN
  have hH := height_previous_le (k + 1)
  have hind : k + 1 + 16 = k + 17 := by omega
  rw [hind] at hi hH
  unfold A at hH ⊢
  nlinarith

/- ## Suppression -/

theorem abs_one_sub_exp_le (x : ℝ) :
    |1 - Real.exp x| ≤ |x| * (1 + Real.exp x) := by
  by_cases hx : 0 ≤ x
  · have he : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
    rw [mul_add, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    rw [abs_of_nonpos (by linarith : 1 - Real.exp x ≤ 0), abs_of_nonneg hx]
    nlinarith
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have he : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx'
    have h := Real.add_one_le_exp x
    have hm := mul_nonneg (neg_nonneg.mpr hx') (Real.exp_pos x).le
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - Real.exp x), abs_of_nonpos hx']
    nlinarith

theorem delta_suppression {j : ℕ} (hj : 16 ≤ j) :
    3 * delta j ≤ Real.exp (-(b j : ℝ) / 2) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hb0 : (0 : ℝ) < b j := by exact_mod_cast b_pos hj
  have hpow : 2 ^ b j ≤ j := Nat.pow_log_le_self 2 (by omega)
  have hb3 : 3 ≤ b j := le_trans (by norm_num) (b_ge_four hj)
  have hprod : 3 * (2 : ℝ) ^ b j ≤ (j : ℝ) * b j := by
    exact_mod_cast (show 3 * 2 ^ b j ≤ j * b j from by
      nlinarith [Nat.mul_le_mul hpow hb3])
  have hsmall : 3 * delta j ≤ 1 / (2 : ℝ) ^ b j := by
    unfold delta
    rw [mul_one_div, div_le_div_iff₀ (mul_pos hj0 hb0) (by positivity)]
    simpa only [one_mul] using hprod
  have heq : 1 / (2 : ℝ) ^ b j = Real.exp (-(b j : ℝ) * Real.log 2) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    simp only [one_div]
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  apply hsmall.trans
  rw [heq]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem multiplicity_suppression {j : ℕ} (hj : 16 ≤ j) :
    16 * A j ≤ (m j : ℝ) * b j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hb0 : (0 : ℝ) < b j := by exact_mod_cast b_pos hj
  have hq : 8 * (N j : ℝ) ≤ (q j : ℝ) * ((j : ℝ) * (b j : ℝ) ^ 2) := by
    have hn := le_ceilDiv_mul (8 * N j) (denom_pos hj)
    change 8 * N j ≤ q j * denom j at hn
    exact_mod_cast hn
  unfold A delta
  rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ (mul_pos hj0 hb0)]
  simp only [m, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

theorem realBlock_exp_factor_bound (k : ℕ) (u : ℝ) :
    realBlock k (Real.exp u) ≤ majorant k (Real.exp u) * |u - t k| ^ m (k + 16) := by
  have hdiv : Real.exp u / R k = Real.exp (u - t k) := by rw [R, Real.exp_sub]
  have hs := abs_one_sub_exp_le (u - t k)
  have hcN : 0 ≤ c k * (Real.exp u) ^ N (k + 16) :=
    mul_nonneg (c_pos k).le (pow_nonneg (Real.exp_pos u).le _)
  have hpow := pow_le_pow_left₀ (abs_nonneg (1 - Real.exp (u - t k))) hs (m (k + 16))
  have heven : (1 - Real.exp (u - t k)) ^ m (k + 16) =
      |1 - Real.exp (u - t k)| ^ m (k + 16) :=
    ((m_even (k + 16)).pow_abs _).symm
  unfold realBlock majorant
  rw [hdiv, heven]
  calc
    _ ≤ (c k * Real.exp u ^ N (k + 16)) *
        (|u - t k| * (1 + Real.exp (u - t k))) ^ m (k + 16) :=
      mul_le_mul_of_nonneg_left hpow hcN
    _ = _ := by rw [mul_pow]; ring

theorem near_block_le_one {k : ℕ} {u : ℝ}
    (hnear : |u - t k| ≤ 3 * delta (k + 16))
    (hF : F k u ≤ 4 * A (k + 16)) : realBlock k (Real.exp u) ≤ 1 := by
  have hδ := hnear.trans (delta_suppression (show 16 ≤ k + 16 by omega))
  have hp := pow_le_pow_left₀ (abs_nonneg (u - t k)) hδ (m (k + 16))
  have hm := multiplicity_suppression (show 16 ≤ k + 16 by omega)
  have hA := A_pos (show 16 ≤ k + 16 by omega)
  calc
    realBlock k (Real.exp u) ≤ Real.exp (F k u) * |u - t k| ^ m (k + 16) := by
      simpa only [majorant_exp_eq] using realBlock_exp_factor_bound k u
    _ ≤ Real.exp (F k u) * Real.exp (-(b (k + 16) : ℝ) / 2) ^ m (k + 16) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = Real.exp (F k u - (m (k + 16) : ℝ) * b (k + 16) / 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)

/- ## Intervals -/

theorem degree_upper (k : ℕ) : (N (k + 16) : ℝ) + m (k + 16) ≤ 3 / 2 * N (k + 16) := by
  have hn := twice_m_le_N (show 16 ≤ k + 16 by omega)
  have hr : 2 * (m (k + 16) : ℝ) ≤ N (k + 16) := by exact_mod_cast hn
  linarith

theorem F_increment_upper {k : ℕ} {u v : ℝ} (h : u ≤ v) :
    F k v - F k u ≤ 3 / 2 * (N (k + 16) : ℝ) * (v - u) :=
  (F_increment h).2.trans
    (mul_le_mul_of_nonneg_right (degree_upper k) (sub_nonneg.mpr h))

theorem near_current {k : ℕ} {u : ℝ} (hlo : s k ≤ u) (hhi : u ≤ s (k + 1)) :
    realBlock k (Real.exp u) ≤ 1 := by
  apply near_block_le_one
  · rw [abs_le]
    have hs := s_succ k
    have hd := delta_pos (show 16 ≤ k + 16 by omega)
    unfold t
    constructor <;> linarith
  · have hf := F_mono k hhi
    rw [F_right] at hf
    have hh := (height_bounds k).2
    have hA := A_pos (show 16 ≤ k + 16 by omega)
    linarith

theorem near_previous {k : ℕ} {u : ℝ}
    (hlo : s (k + 1) ≤ u) (hhi : u ≤ s (k + 2)) : realBlock k (Real.exp u) ≤ 1 := by
  have hδ := delta_antitone (show 16 ≤ k + 16 by omega) (show k + 16 ≤ k + 17 by omega)
  have hδ0 := delta_pos (show 16 ≤ k + 16 by omega)
  have hs1 := s_succ k
  have hs2 : s (k + 2) = s (k + 1) + delta (k + 17) := by
    simpa only [show k + 1 + 16 = k + 17 by omega, show k + 1 + 1 = k + 2 by omega]
      using s_succ (k + 1)
  apply near_block_le_one
  · rw [abs_le]
    unfold t
    constructor <;> linarith
  · have hi := F_increment_upper (k := k)
      (show s (k + 1) ≤ s (k + 2) from s_strictMono.monotone (by omega))
    rw [F_right, hs2] at hi
    have hm := F_mono k hhi
    rw [hs2] at hm
    have hh := (height_bounds k).2
    have hn : (0 : ℝ) ≤ N (k + 16) := by exact_mod_cast (N_pos (k + 16)).le
    have hd := mul_le_mul_of_nonneg_left hδ hn
    unfold A at hh ⊢
    nlinarith

theorem near_next {k : ℕ} {u : ℝ} (hlo : s k ≤ u) (hhi : u ≤ s (k + 1)) :
    realBlock (k + 1) (Real.exp u) ≤ 1 := by
  have hd := delta_le_twice_succ (show 16 ≤ k + 16 by omega)
  have hd0 := delta_pos (show 16 ≤ k + 17 by omega)
  have hs := s_succ k
  have hind : k + 16 + 1 = k + 17 := by omega
  have hind' : k + 1 + 16 = k + 17 := by omega
  rw [hind] at hd
  apply near_block_le_one
  · rw [abs_le]
    unfold t
    rw [hind']
    constructor <;> linarith
  · have hf := F_mono (k + 1) hhi
    rw [F_left] at hf
    have hh := height_previous_le (k + 1)
    have hA := A_pos (show 16 ≤ k + 1 + 16 by omega)
    linarith

theorem F_crossing (k : ℕ) {u : ℝ} (hu : s (k + 1) ≤ u) : F k u ≤ F (k + 1) u := by
  have hleft := (F_increment (k := k) hu).2
  have hright := (F_increment (k := k + 1) hu).1
  rw [F_right] at hleft
  rw [F_left] at hright
  have hn : (N (k + 16) : ℝ) + m (k + 16) ≤ N (k + 1 + 16) := by
    exact_mod_cast (show N (k + 16) + m (k + 16) ≤ N (k + 1 + 16) from by
      simpa only [Nat.add_right_comm k 1 16] using
        (blocks_separated (show 16 ≤ k + 16 by omega)).le)
  have hm := mul_le_mul_of_nonneg_right hn (sub_nonneg.mpr hu)
  linarith

theorem F_le_later {i j : ℕ} {u : ℝ} (hij : i ≤ j) (hu : s j ≤ u) : F i u ≤ F j u := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; rfl
    · have hij' : i ≤ j := by omega
      exact (ih hij' ((s_strictMono.monotone (by omega : j ≤ j + 1)).trans hu)).trans
        (F_crossing j hu)

theorem F_old_bound {p i : ℕ} {u : ℝ} (hi : i ≤ p)
    (hlo : s (p + 2) ≤ u) (hhi : u ≤ s (p + 3)) : F i u ≤ 5 * A (p + 16) := by
  have horder := F_le_later hi ((s_strictMono.monotone (by omega : p ≤ p + 2)).trans hlo)
  have hmono := F_mono p hhi
  have hincr := F_increment_upper (k := p)
    (s_strictMono.monotone (show p + 1 ≤ p + 3 by omega))
  rw [F_right] at hincr
  have hs : s (p + 3) - s (p + 1) = delta (p + 17) + delta (p + 18) := by
    have h1 := s_succ (p + 1)
    have h2 := s_succ (p + 2)
    have e1 : p + 1 + 1 = p + 2 := by omega
    have e2 : p + 2 + 1 = p + 3 := by omega
    have e3 : p + 1 + 16 = p + 17 := by omega
    have e4 : p + 2 + 16 = p + 18 := by omega
    rw [e1, e3] at h1
    rw [e2, e4] at h2
    linarith
  rw [hs] at hincr
  have h1 := delta_antitone (show 16 ≤ p + 16 by omega) (show p + 16 ≤ p + 17 by omega)
  have h2 := delta_antitone (show 16 ≤ p + 16 by omega) (show p + 16 ≤ p + 18 by omega)
  have hN : (0 : ℝ) ≤ N (p + 16) := by exact_mod_cast (N_pos (p + 16)).le
  have hm := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hN
  have hh := (height_bounds p).2
  unfold A at hh ⊢
  nlinarith

theorem exists_interval {u : ℝ} {k₀ : ℕ} (hu : s k₀ ≤ u) :
    ∃ k, k₀ ≤ k ∧ s k ≤ u ∧ u ≤ s (k + 1) := by
  classical
  have hex : ∃ n, u < s n := (s_tendsto_atTop.eventually_gt_atTop u).exists
  have hn := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro he
    rw [he, s_zero] at hn
    have h0 := s_nonneg k₀
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hlo : s k ≤ u := by
    apply le_of_not_gt
    exact Nat.find_min hex (by omega : k < Nat.find hex)
  have hhi : u < s (k + 1) := by simpa only [hk] using hn
  have hge : k₀ ≤ k := by
    by_contra h
    have hk₀ : k + 1 ≤ k₀ := by omega
    have h := s_strictMono.monotone hk₀
    linarith
  exact ⟨k, hge, hlo, hhi.le⟩

/- ## Series -/

open Filter Finset Metric
open scoped Topology


theorem majorant_mono (k : ℕ) {r v : ℝ} (hr : 0 ≤ r) (hrv : r ≤ v) :
    majorant k r ≤ majorant k v := by
  have hR := (R_pos k).le
  have hc := (c_pos k).le
  have hb : 0 ≤ 1 + r / R k := add_nonneg (by norm_num) (div_nonneg hr hR)
  have hp := pow_le_pow_left₀ hb
    (add_le_add (le_refl (1 : ℝ)) (div_le_div_of_nonneg_right hrv hR)) (m (k + 16))
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrv _) hc) hp
    (pow_nonneg hb _) (mul_nonneg hc (pow_nonneg (hr.trans hrv) _))

theorem summable_majorant_exp (u : ℝ) : Summable (fun k : ℕ => majorant k (Real.exp u)) := by
  apply (summable_nat_add_iff 1).1
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat
  filter_upwards [s_tendsto_atTop.eventually_ge_atTop u] with k hk
  rw [Real.norm_eq_abs, abs_of_pos (majorant_exp_pos (k + 1) u), majorant_exp_eq]
  apply Real.exp_le_exp.mpr
  have hF := F_future k hk
  have hA := sq_le_A (show 16 ≤ k + 17 by omega)
  push_cast at hA
  have hkR : (0 : ℝ) ≤ k := by positivity
  nlinarith [sq_nonneg (k : ℝ)]

theorem summable_majorant {r : ℝ} (hr : 0 ≤ r) : Summable (fun k : ℕ => majorant k r) := by
  apply (summable_majorant_exp (Real.log (r + 1))).of_nonneg_of_le
    (fun k => majorant_nonneg k hr)
  intro k
  rw [Real.exp_log (by linarith : 0 < r + 1)]
  exact majorant_mono k hr (by linarith)

theorem summable_blocks (z : ℂ) : Summable (fun k : ℕ => block k z) :=
  (summable_majorant (norm_nonneg z)).of_norm_bounded (fun k => norm_block_le k z)

theorem summable_norm_monomials (z : ℂ) :
    Summable (fun x : Index => ‖coefficient x * z ^ exponent x‖) := by
  apply (summable_sigma_of_nonneg (fun x => norm_nonneg _)).2
  constructor
  · intro k
    exact (hasSum_fintype _).summable
  · simpa only [tsum_fintype, sum_norm_monomials] using summable_majorant (norm_nonneg z)

theorem hasSum_monomials (z : ℂ) :
    HasSum (fun x : Index => coefficient x * z ^ exponent x) (f z) := by
  have hmono := (summable_norm_monomials z).of_norm
  have hblocks := hmono.hasSum.sigma (fun k =>
    (show HasSum (fun l : Fin (m (k + 16) + 1) =>
      coefficient ⟨k, l⟩ * z ^ exponent ⟨k, l⟩) (block k z) from by
      simpa only [block_expansion] using hasSum_fintype
        (fun l : Fin (m (k + 16) + 1) => coefficient ⟨k, l⟩ * z ^ exponent ⟨k, l⟩)))
  have heq : f z = ∑' x : Index, coefficient x * z ^ exponent x := hblocks.tsum_eq
  rw [heq]
  exact hmono.hasSum

theorem hasSum_coefficients (z : ℂ) :
    HasSum (fun k => coefficients k * z ^ exponents k) (f z) := by
  have h := enumeration.hasSum_iff.mpr (hasSum_monomials z)
  change HasSum (fun k => coefficient (indexOf k) * z ^ exponent (indexOf k)) (f z) at h
  simpa only [exponent_indexOf, coefficients] using h

theorem differentiable_f : Differentiable ℂ f := by
  intro z
  let rad : ℝ := ‖z‖ + 1
  have hrad : 0 < rad := by dsimp [rad]; positivity
  have hdiff : DifferentiableOn ℂ f (ball 0 rad) := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      (summable_majorant hrad.le) (fun k => (differentiable_block k).differentiableOn) isOpen_ball
    intro k w hw
    apply (norm_block_le k w).trans
    apply majorant_mono k (norm_nonneg w)
    exact (mem_ball_zero_iff.mp hw).le
  apply hdiff.differentiableAt
  apply isOpen_ball.mem_nhds
  rw [mem_ball_zero_iff]
  dsimp [rad]
  linarith

/- ## RadiusBounds -/

open Finset


theorem norm_block_real (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ‖block k (r : ℂ)‖ = realBlock k r := by
  rw [← ofReal_realBlock, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (realBlock_nonneg k hr)]

theorem realBlock_le_majorant (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : realBlock k r ≤ majorant k r := by
  have h := norm_block_le k (r : ℂ)
  rw [norm_block_real k hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at h
  exact h

theorem summable_realBlock {r : ℝ} (hr : 0 ≤ r) : Summable (fun k => realBlock k r) :=
  (summable_majorant hr).of_nonneg_of_le (fun k => realBlock_nonneg k hr)
    (fun k => realBlock_le_majorant k hr)

theorem norm_f_real {r : ℝ} (hr : 0 ≤ r) : ‖f (r : ℂ)‖ = ∑' k, realBlock k r := by
  unfold f
  simp_rw [← ofReal_realBlock]
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (fun k => realBlock_nonneg k hr))]

theorem norm_f_neg_real {r : ℝ} (hr : 0 ≤ r) : ‖f (-(r : ℂ))‖ = ∑' k, majorant k r := by
  unfold f
  simp_rw [block_neg_real]
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (fun k => majorant_nonneg k hr))]

theorem norm_f_le (z : ℂ) : ‖f z‖ ≤ ∑' k, majorant k ‖z‖ := by
  apply (norm_tsum_le_tsum_norm
    ((summable_majorant (norm_nonneg z)).of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_block_le k z))).trans
  exact ((summable_majorant (norm_nonneg z)).of_nonneg_of_le
    (fun k => norm_nonneg _) (fun k => norm_block_le k z)).tsum_le_tsum
      (fun k => norm_block_le k z) (summable_majorant (norm_nonneg z))

theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  rw [Real.exp_neg]
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  simpa only [one_div] using (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).mpr h

theorem future_block_bound (p k : ℕ) {u : ℝ} (hu : u ≤ s (p + 3)) :
    realBlock (k + (p + 4)) (Real.exp u) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  have hs : u ≤ s (k + (p + 3)) := hu.trans (s_strictMono.monotone (by omega))
  have hf := F_future (k + (p + 3)) hs
  have hA := sq_le_A (show 16 ≤ k + (p + 3) + 17 by omega)
  have hind : k + (p + 3) + 1 = k + (p + 4) := by omega
  rw [hind] at hf
  have hF : F (k + (p + 4)) u ≤ -((k : ℝ) + 1) := by
    push_cast at hA
    have hp0 : (0 : ℝ) ≤ p := by positivity
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith [sq_nonneg ((k : ℝ) + p)]
  calc
    _ ≤ majorant (k + (p + 4)) (Real.exp u) := realBlock_le_majorant _ (Real.exp_pos u).le
    _ = Real.exp (F (k + (p + 4)) u) := majorant_exp_eq _ _
    _ ≤ Real.exp (-((k : ℝ) + 1)) := Real.exp_le_exp.mpr hF
    _ = Real.exp (-1) ^ (k + 1) := by rw [← Real.exp_nat_mul]; push_cast; congr 1; ring
    _ ≤ (1 / 2 : ℝ) ^ (k + 1) := pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le_half _

theorem half_geometric_hasSum : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) 1 := by
  have h := (hasSum_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)).mul_right (1 / 2)
  have he : ((1 - (1 / 2 : ℝ))⁻¹) * (1 / 2) = 1 := by norm_num
  simpa only [pow_succ, he] using h

theorem tsum_le_one_of_half_bound {a : ℕ → ℝ} (ha : Summable a)
    (hb : ∀ k, a k ≤ (1 / 2 : ℝ) ^ (k + 1)) : (∑' k, a k) ≤ 1 := by
  exact (ha.tsum_le_tsum hb half_geometric_hasSum.summable).trans_eq half_geometric_hasSum.tsum_eq

theorem future_sum_le_one (p : ℕ) {u : ℝ} (hu : u ≤ s (p + 3)) :
    (∑' k : ℕ, realBlock (k + (p + 4)) (Real.exp u)) ≤ 1 := by
  have hs : Summable (fun k : ℕ => realBlock (k + (p + 4)) (Real.exp u)) :=
    (summable_nat_add_iff (f := fun k : ℕ => realBlock k (Real.exp u)) (p + 4)).2
      (summable_realBlock (Real.exp_pos u).le)
  exact tsum_le_one_of_half_bound hs (fun k => future_block_bound p k hu)

theorem positive_axis_bound (p : ℕ) {u : ℝ}
    (hlo : s (p + 2) ≤ u) (hhi : u ≤ s (p + 3)) :
    ‖f (Real.exp u : ℂ)‖ ≤ ((p : ℝ) + 5) * Real.exp (5 * A (p + 16)) := by
  have hsum := summable_realBlock (Real.exp_pos u).le
  have hold : (∑ i ∈ range (p + 1), realBlock i (Real.exp u)) ≤
      ((p : ℝ) + 1) * Real.exp (5 * A (p + 16)) := by
    calc
      _ ≤ ∑ _i ∈ range (p + 1), Real.exp (5 * A (p + 16)) := by
        apply sum_le_sum
        intro i hi
        have hi' : i ≤ p := by have := mem_range.mp hi; omega
        apply (realBlock_le_majorant i (Real.exp_pos u).le).trans
        rw [majorant_exp_eq]
        exact Real.exp_le_exp.mpr (F_old_bound hi' hlo hhi)
      _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hnear1 : realBlock (p + 1) (Real.exp u) ≤ 1 := by
    exact near_previous hlo hhi
  have hnear2 : realBlock (p + 2) (Real.exp u) ≤ 1 := near_current hlo hhi
  have hnear3 : realBlock (p + 3) (Real.exp u) ≤ 1 := by
    exact near_next hlo hhi
  have htail := future_sum_le_one p hhi
  have hsplit := hsum.sum_add_tsum_nat_add (p + 4)
  have hprefix : (∑ i ∈ range (p + 4), realBlock i (Real.exp u)) =
      (∑ i ∈ range (p + 1), realBlock i (Real.exp u)) +
        realBlock (p + 1) (Real.exp u) + realBlock (p + 2) (Real.exp u) + realBlock (p + 3) (Real.exp u) := by
    rw [show p + 4 = (p + 1 + 1 + 1) + 1 by omega, sum_range_succ, sum_range_succ, sum_range_succ]
  rw [hprefix] at hsplit
  rw [norm_f_real (Real.exp_pos u).le]
  have he : 1 ≤ Real.exp (5 * A (p + 16)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) (A_pos (by omega)).le)
  nlinarith

theorem negative_axis_lower (p : ℕ) {u : ℝ} (hlo : s (p + 2) ≤ u) :
    Real.exp (A (p + 17)) ≤ ‖f (-(Real.exp u : ℂ))‖ := by
  have hf := F_mono (p + 2) hlo
  rw [F_left] at hf
  have hh : A (p + 17) ≤ H (p + 2) := by
    simpa only [show p + 1 + 16 = p + 17 by omega, show p + 1 + 1 = p + 2 by omega]
      using (height_bounds (p + 1)).1
  rw [norm_f_neg_real (Real.exp_pos u).le]
  calc
    Real.exp (A (p + 17)) ≤ Real.exp (F (p + 2) u) := Real.exp_le_exp.mpr (hh.trans hf)
    _ = majorant (p + 2) (Real.exp u) := (majorant_exp_eq _ _).symm
    _ ≤ ∑' k, majorant k (Real.exp u) :=
      (summable_majorant (Real.exp_pos u).le).le_tsum (p + 2) (fun k _ => majorant_nonneg k (Real.exp_pos u).le)

/- ## Ratio -/

open Set


/-- A direct bridge from pointwise estimates to FC's infimum/supremum ratio.
The numerator may be negative, and the infimum may be zero. -/
theorem ratio_le_of_circle_bounds {f : ℂ → ℂ} {r M U B : ℝ}
    (hr : 0 ≤ r) (hB : 0 < B) (hU : 0 ≤ U)
    (hcircle : ∀ z : ℂ, ‖z‖ = r → ‖f z‖ ≤ M)
    (hnegative : Real.exp B ≤ ‖f (-(r : ℂ))‖)
    (hpositive : ‖f (r : ℂ)‖ ≤ Real.exp U) :
    Erdos516Target.ratio r f ≤ U / B := by
  let C := {z : ℂ // ‖z‖ = r}
  let zpos : C := ⟨(r : ℂ), by simpa using hr⟩
  let zneg : C := ⟨-(r : ℂ), by simpa using hr⟩
  let L : ℝ := ⨅ z : C, ‖f z‖
  let S : ℝ := ⨆ z : C, ‖f z‖
  have hlower : BddBelow (range (fun z : C => ‖f z‖)) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩
  have hupper : BddAbove (range (fun z : C => ‖f z‖)) :=
    ⟨M, by rintro _ ⟨z, rfl⟩; exact hcircle z z.property⟩
  have hL0 : 0 ≤ L := Real.iInf_nonneg (fun z => norm_nonneg (f z))
  have hL : L ≤ Real.exp U := (ciInf_le hlower zpos).trans hpositive
  have hS : Real.exp B ≤ S := hnegative.trans (le_ciSup hupper zneg)
  have hS0 : 0 < S := (Real.exp_pos B).trans_le hS
  have hlogS : B ≤ Real.log S := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos B) hS
  have hlogL : Real.log L ≤ U := by
    rcases eq_or_lt_of_le hL0 with hzero | hpos
    · rw [← hzero, Real.log_zero]
      exact hU
    · simpa only [Real.log_exp] using Real.log_le_log hpos hL
  change Real.log L / Real.log S ≤ U / B
  calc
    Real.log L / Real.log S ≤ U / Real.log S :=
      div_le_div_of_nonneg_right hlogL (hB.trans_le hlogS).le
    _ ≤ U / B := div_le_div_of_nonneg_left hU hB hlogS

/- ## Counterexample -/

open Filter


theorem final_quotient_bound (p : ℕ) :
    (5 * A (p + 16) + Real.log ((p : ℝ) + 5)) / A (p + 17) ≤ 1 / 2 := by
  have hA := A_pos (show 16 ≤ p + 16 by omega)
  have hB := A_pos (show 16 ≤ p + 17 by omega)
  have hg := A_succ_growth (show 16 ≤ p + 16 by omega)
  rw [show p + 16 + 1 = p + 17 by omega] at hg
  have hp : (32 : ℝ) ≤ 2 ^ (2 * (p + 16)) := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
      (show 5 ≤ 2 * (p + 16) by omega)
    norm_num at h
    exact h
  have hmul := mul_le_mul_of_nonneg_right hp hA.le
  have hs := sq_le_A (show 16 ≤ p + 17 by omega)
  push_cast at hs
  have hlog : Real.log ((p : ℝ) + 5) ≤ (p : ℝ) + 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < p + 5 by positivity)
    linarith
  have hp0 : (0 : ℝ) ≤ p := by positivity
  apply (div_le_iff₀ hB).2
  nlinarith [sq_nonneg (p : ℝ)]

theorem ratio_on_interval (p : ℕ) {u : ℝ}
    (hlo : s (p + 2) ≤ u) (hhi : u ≤ s (p + 3)) :
    Erdos516Target.ratio (Real.exp u) f ≤ 1 / 2 := by
  let U := 5 * A (p + 16) + Real.log ((p : ℝ) + 5)
  have hU : 0 ≤ U := add_nonneg (mul_nonneg (by norm_num) (A_pos (by omega)).le)
    (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) p; linarith))
  have hpositive : ‖f (Real.exp u : ℂ)‖ ≤ Real.exp U := by
    have h := positive_axis_bound p hlo hhi
    dsimp [U]
    rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < p + 5)]
    simpa only [mul_comm] using h
  have hratio := ratio_le_of_circle_bounds (f := f) (r := Real.exp u)
    (M := ∑' k, majorant k (Real.exp u)) (U := U) (B := A (p + 17))
    (Real.exp_pos u).le (A_pos (by omega)) hU
    (fun z hz => by simpa only [hz] using norm_f_le z)
    (negative_axis_lower p hlo) hpositive
  exact hratio.trans (final_quotient_bound p)

theorem ratio_eventually_le_half :
    ∀ᶠ r in atTop, Erdos516Target.ratio r f ≤ (1 / 2 : ℝ) := by
  filter_upwards [eventually_ge_atTop (Real.exp (s 2))] with r hr
  have hr0 : 0 < r := (Real.exp_pos _).trans_le hr
  have hlog : s 2 ≤ Real.log r := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (s 2)) hr
  obtain ⟨k, hk, hlo, hhi⟩ := exists_interval hlog
  let p := k - 2
  have hp : p + 2 = k := by dsimp [p]; omega
  have hp' : p + 3 = k + 1 := by omega
  have hb := ratio_on_interval p (u := Real.log r) (by simpa only [hp] using hlo) (by simpa only [hp'] using hhi)
  simpa only [Real.exp_log hr0] using hb

theorem counterexample_limsup_ne_one : limsup (fun r => Erdos516Target.ratio r f) atTop ≠ 1 :=
  limsup_ne_one_of_eventually_le_half ratio_eventually_le_half

/-- The explicit entire function, exponents and coefficients satisfy all original hypotheses. -/
theorem explicit_counterexample :
    Differentiable ℂ f ∧ Erdos516Target.HasFejerGaps exponents ∧
      (∀ k, coefficients k ≠ 0) ∧
      (∀ z, HasSum (fun k => coefficients k * z ^ exponents k) (f z)) ∧
      limsup (fun r => Erdos516Target.ratio r f) atTop ≠ 1 :=
  ⟨differentiable_f, exponents_hasFejerGaps, coefficients_ne_zero,
    hasSum_coefficients, counterexample_limsup_ne_one⟩

/-- Standalone form of the registered target, with the explicit answer `False`. -/
theorem erdos_516_fejer_gap_variant_answer_false :
    False ↔
      ∀ {f : ℂ → ℂ} {n : ℕ → ℕ} (_hn : Erdos516Target.HasFejerGaps n)
        {a : ℕ → ℂ} (_ha : ∀ n, a n ≠ 0)
        (_hfn : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)),
        limsup (fun r => Erdos516Target.ratio r f) atTop = 1 := by
  simp only [false_iff]
  intro h
  exact counterexample_limsup_ne_one
    (h exponents_hasFejerGaps coefficients_ne_zero hasSum_coefficients)

#print axioms explicit_counterexample
#print axioms erdos_516_fejer_gap_variant_answer_false

end Erdos516Proof
