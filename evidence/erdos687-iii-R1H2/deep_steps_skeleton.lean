import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1_H2_R1
import Mathlib

-- Credit: @LordMike
-- Disproof of step H2 of reduction Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1.H2.R1.
--
-- Idea. Chaining the three merged reductions above this step (their main theorems) with their
-- H1 hypotheses turns H2 into the short-interval rough-number lower bound
--   exists c > 0, for every eps in (0,1), eventually every block of length x^(1+eps)
--   has at least c * x^(1+eps) / log x integers with no prime factor <= x,
-- with c chosen before eps. That statement is false by the first step of the Erdos-Rankin
-- construction: put the block at a point divisible by every prime in (w, x], w = x^alpha, and
-- average over the residues modulo the primes <= w. The survivors are w-smooth numbers
-- (at most 2048 alpha^2 N) and multiples of primes > x (at most about 3 eps N), and the
-- averaging multiplies by prod_{p <= w} (1 - 1/p) <= 1 / log w. With alpha ~ c and eps ~ c alpha
-- the count drops below c N / log x.
--
-- The namespace OMA.Mertens687 below is the merged proof of step
-- Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H1 by @ivillar, copied unchanged (its lemmas
-- A_le and theta_le are reused in Part C).

open Real Finset

namespace OMA.Mertens687
lemma log_factorial_eq (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ m ∈ Finset.Ioc 0 n, Real.log m := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), ih,
      Finset.sum_Ioc_succ_top (by omega)]
    push_cast
    ring

lemma sum_floor_log_le (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((n / p : ℕ) : ℝ) * Real.log p
      ≤ Real.log (n.factorial : ℝ) := by
  rw [log_factorial_eq]
  have key : ∀ m ∈ Finset.Ioc 0 n,
      ∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (· ∣ m), Real.log p
        ≤ Real.log m := by
    intro m hm
    have hm0 : m ≠ 0 := by
      simp only [Finset.mem_Ioc] at hm
      omega
    rw [← ArithmeticFunction.vonMangoldt_sum]
    calc ∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (· ∣ m), Real.log p
        = ∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (· ∣ m),
            ArithmeticFunction.vonMangoldt p := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp
          rw [ArithmeticFunction.vonMangoldt_apply_prime hp.1.2]
      _ ≤ ∑ i ∈ m.divisors, ArithmeticFunction.vonMangoldt i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_range] at hp
            simp only [Nat.mem_divisors]
            exact ⟨hp.2, hm0⟩
          · intro i _ _
            exact ArithmeticFunction.vonMangoldt_nonneg
  calc ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((n / p : ℕ) : ℝ) * Real.log p
      = ∑ m ∈ Finset.Ioc 0 n,
          ∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (· ∣ m), Real.log p := by
        simp_rw [Finset.sum_filter (s := (Finset.range (n + 1)).filter Nat.Prime)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ m ∈ Finset.Ioc 0 n, Real.log m := Finset.sum_le_sum key

lemma theta_le (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p ≤ Real.log 4 * n := by
  have h1 := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (Nat.cast_nonneg n)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at h1
  exact h1

lemma A_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log n + Real.log 4 := by
  have h1 := sum_floor_log_le n
  have h2 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    have hle := Nat.factorial_le_pow n
    have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := by
          apply Real.log_le_log hpos
          exact_mod_cast hle
      _ = n * Real.log n := by rw [Real.log_pow]
  have h3 := theta_le n
  have h4 : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((n : ℝ) / p - 1) * Real.log p
      ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((n / p : ℕ) : ℝ) * Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    have hp' : p.Prime := (Finset.mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
    rw [div_sub_one hp0.ne', div_le_iff₀ hp0]
    have hdm := Nat.div_add_mod n p
    have hmod := Nat.mod_lt n hp'.pos
    have e1 : (n : ℝ) = p * (n / p : ℕ) + (n % p : ℕ) := by exact_mod_cast hdm.symm
    have e2 : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast hmod
    nlinarith
  have h5 : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((n : ℝ) / p - 1) * Real.log p
      = n * ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p
        - ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h6 : (n : ℝ) * ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p
      ≤ n * (Real.log n + Real.log 4) := by nlinarith
  exact le_of_mul_le_mul_left h6 hn'

lemma filter_succ (n : ℕ) :
    (Finset.range (n + 1 + 1)).filter Nat.Prime
      = if (n + 1).Prime then insert (n + 1) ((Finset.range (n + 1)).filter Nat.Prime)
        else (Finset.range (n + 1)).filter Nat.Prime := by
  rw [Finset.range_add_one (n := n + 1), Finset.filter_insert]

lemma not_mem_filter (n : ℕ) : n + 1 ∉ (Finset.range (n + 1)).filter Nat.Prime := by
  simp

lemma step_bound (n : ℕ) (hn : 1 ≤ n) :
    -Real.log (1 - ((n + 1 : ℕ) : ℝ)⁻¹) - 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 / (n : ℝ) - 1 / (n + 1 : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast
  have e : (1 : ℝ) - ((n : ℝ) + 1)⁻¹ = n / (n + 1) := by field_simp; ring
  rw [e, Real.log_div hn'.ne' (by positivity)]
  have h := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
  rw [Real.log_div (by positivity) hn'.ne'] at h
  have e2 : ((n : ℝ) + 1) / n - 1 = 1 / n := by
    field_simp
    ring
  rw [e2] at h
  linarith

lemma main_ind (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, -Real.log (1 - (p : ℝ)⁻¹)
      - (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p) / Real.log n
      ≤ Real.log (Real.log n) - Real.log (Real.log 2) + Real.log 4 / Real.log 2
        - Real.log 4 / Real.log n + 1 - 1 / n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hP : (Finset.range (2 + 1)).filter Nat.Prime = {2} := by decide
    rw [hP, Finset.sum_singleton, Finset.sum_singleton]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlt : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    push_cast
    have e1 : (1 : ℝ) - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
    rw [e1, Real.log_inv]
    have e2 : Real.log 2 / 2 / Real.log 2 = 1 / 2 := by field_simp
    rw [e2]
    linarith
  | succ n hn ih =>
    set S := (Finset.range (n + 1)).filter Nat.Prime with hS
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hL : 0 < Real.log n := Real.log_pos hn1
    have hL' : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
    have hLL : Real.log n < Real.log ((n : ℝ) + 1) := Real.log_lt_log (by linarith) (by linarith)
    have hA := A_le n (by omega)
    have hA0 : 0 ≤ ∑ p ∈ S, Real.log p / p := by
      apply Finset.sum_nonneg
      intro p hp
      have hp' : p.Prime := (Finset.mem_filter.mp hp).2
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)) (Nat.cast_nonneg p)
    -- the increment
    have hinc : ∑ p ∈ (Finset.range (n + 1 + 1)).filter Nat.Prime, -Real.log (1 - (p : ℝ)⁻¹)
        - (∑ p ∈ (Finset.range (n + 1 + 1)).filter Nat.Prime, Real.log p / p) / Real.log ((n : ℝ) + 1)
        ≤ ∑ p ∈ S, -Real.log (1 - (p : ℝ)⁻¹) - (∑ p ∈ S, Real.log p / p) / Real.log ((n : ℝ) + 1)
          + (1 / (n : ℝ) - 1 / (n + 1 : ℝ)) := by
      rw [filter_succ]
      split_ifs with hpr
      · rw [Finset.sum_insert (not_mem_filter n), Finset.sum_insert (not_mem_filter n)]
        have hsb := step_bound n (by omega)
        have e : Real.log (((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) / Real.log ((n : ℝ) + 1)
            = 1 / ((n + 1 : ℕ) : ℝ) := by
          push_cast
          field_simp
        rw [add_div, e]
        linarith
      · have : (0 : ℝ) ≤ 1 / (n : ℝ) - 1 / (n + 1 : ℝ) := by
          rw [div_sub_div _ _ (by positivity) (by positivity)]
          apply div_nonneg <;> nlinarith
        linarith
    -- the change of logarithm in the denominator
    have hden : (∑ p ∈ S, Real.log p / p) / Real.log n - (∑ p ∈ S, Real.log p / p) / Real.log ((n : ℝ) + 1)
        ≤ Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n)
          + Real.log 4 / Real.log n - Real.log 4 / Real.log ((n : ℝ) + 1) := by
      have hd : 0 ≤ 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1) := by
        rw [div_sub_div _ _ hL.ne' hL'.ne']
        apply div_nonneg <;> nlinarith
      have h1 : (∑ p ∈ S, Real.log p / p) * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1))
          ≤ (Real.log n + Real.log 4) * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hA hd
      have h2 : 1 - (Real.log ((n : ℝ) + 1) / Real.log n)⁻¹ ≤ Real.log (Real.log ((n : ℝ) + 1) / Real.log n) :=
        Real.one_sub_inv_le_log_of_pos (by positivity)
      rw [Real.log_div hL'.ne' hL.ne', inv_div] at h2
      have e3 : (Real.log n + Real.log 4) * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1))
          = (1 - Real.log n / Real.log ((n : ℝ) + 1)) + (Real.log 4 / Real.log n - Real.log 4 / Real.log ((n : ℝ) + 1)) := by
        field_simp
      have e4 : (∑ p ∈ S, Real.log p / p) / Real.log n - (∑ p ∈ S, Real.log p / p) / Real.log ((n : ℝ) + 1)
          = (∑ p ∈ S, Real.log p / p) * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by ring
      rw [e4]
      linarith
    push_cast
    linarith

theorem mertens_lower : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℕ, 2 ≤ x →
    c₀ / Real.log (x : ℝ) ≤
      ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨Real.exp (-(1 + Real.log 4 / Real.log 2
    + (-Real.log (Real.log 2) + Real.log 4 / Real.log 2 + 1))), Real.exp_pos _, ?_⟩
  intro x hx
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hind := main_ind x hx
  have hA := A_le x (by omega)
  have hL2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  have hAdiv : (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, Real.log p / p) / Real.log x
      ≤ 1 + Real.log 4 / Real.log 2 := by
    rw [div_le_iff₀ hL]
    have h1 : Real.log 4 ≤ Real.log 4 / Real.log 2 * Real.log x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      nlinarith
    nlinarith
  have h4 : 0 ≤ Real.log 4 / Real.log x := div_nonneg hK hL.le
  have h5 : 0 ≤ 1 / (x : ℝ) := by positivity
  have hG : ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, -Real.log (1 - (p : ℝ)⁻¹)
      ≤ Real.log (Real.log x) + (1 + Real.log 4 / Real.log 2
        + (-Real.log (Real.log 2) + Real.log 4 / Real.log 2 + 1)) := by
    linarith
  have hfac_pos : ∀ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hp' : p.Prime := (Finset.mem_filter.mp hp).2
    have h1 : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
    have h2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    linarith
  have hprod_pos : 0 < ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_pos hfac_pos
  have hlogprod : Real.log (∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))
      = -∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, -Real.log (1 - (p : ℝ)⁻¹) := by
    rw [Real.log_prod (fun p hp => (hfac_pos p hp).ne'), Finset.sum_neg_distrib, neg_neg]
  rw [← Real.log_le_log_iff (div_pos (Real.exp_pos _) hL) hprod_pos, hlogprod,
    Real.log_div (Real.exp_pos _).ne' hL.ne', Real.log_exp]
  linarith

end OMA.Mertens687

/- ## Rankin construction: the short-interval rough-number lower bound is false

Notation used in the comments (no definitions are introduced):
* rough count: number of `n` in `[M+1, M+N]` with no prime factor `≤ x`;
* `V w` : the Euler product `∏_{p ≤ w} (1 - 1/p)`;
* `K` : `j` in `[1, N]` with no prime factor in `(w, x]`;
* `S` : `w`-smooth `j` in `[1, N]`;
* `B` : `j` in `[1, N]` with a prime factor `> x`.
-/

namespace E687Rankin

open Finset Filter
open scoped Classical

/- ### Part A: averaging over the small primes and CRT -/

lemma card_coprime_shift (Q j : ℕ) (hQ : 0 < Q) :
    ((range Q).filter fun c => Nat.Coprime (c + j) Q).card = Nat.totient Q := by
  rw [← Nat.filter_coprime_Ico_eq_totient Q j]
  refine Finset.card_bij (fun c _ => c + j) ?_ ?_ ?_
  · intro c hc
    simp only [mem_filter, mem_range, mem_Ico] at hc ⊢
    exact ⟨⟨by omega, by omega⟩, hc.2.symm⟩
  · intro a _ b _ h
    simpa using h
  · intro b hb
    simp only [mem_filter, mem_Ico] at hb
    refine ⟨b - j, ?_, by omega⟩
    simp only [mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    rw [Nat.sub_add_cancel hb.1.1]
    exact hb.2.symm

lemma totient_prod_primes_aux1 (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ((Nat.totient (∏ p ∈ S, p) : ℕ) : ℝ) =
      (∏ p ∈ S, (1 - (p : ℝ)⁻¹)) * ((∏ p ∈ S, p : ℕ) : ℝ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hap : a.Prime := hS a (mem_insert_self a S)
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ S, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hap (hS' p hp)).mpr (fun h => ha (h ▸ hp))
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast hap.ne_zero
    rw [prod_insert ha, prod_insert ha, Nat.totient_mul hcop, Nat.totient_prime hap,
      Nat.cast_mul, ih hS', Nat.cast_sub hap.one_lt.le, Nat.cast_mul]
    push_cast
    field_simp

lemma totient_prod_primes (w : ℕ) :
    ((Nat.totient (∏ p ∈ (range (w + 1)).filter Nat.Prime, p) : ℕ) : ℝ) =
      (∏ p ∈ (range (w + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) *
        ((∏ p ∈ (range (w + 1)).filter Nat.Prime, p : ℕ) : ℝ) :=
  totient_prod_primes_aux1 _ fun _ hp => (mem_filter.mp hp).2

lemma exists_shift_le_avg (K : Finset ℕ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ c ∈ range Q,
      (K.filter fun j => Nat.Coprime (c + j) Q).card * Q ≤ K.card * Nat.totient Q := by
  have hsum : ∑ c ∈ range Q, (K.filter fun j => Nat.Coprime (c + j) Q).card =
      K.card * Nat.totient Q := by
    have h1 : ∀ c ∈ range Q, (K.filter fun j => Nat.Coprime (c + j) Q).card =
        ∑ j ∈ K, if Nat.Coprime (c + j) Q then 1 else 0 := fun c _ => Finset.card_filter _ _
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ j ∈ K, (∑ c ∈ range Q, if Nat.Coprime (c + j) Q then 1 else 0) =
        Nat.totient Q := fun j _ => by
      rw [← Finset.card_filter]
      exact card_coprime_shift Q j hQ
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]
  by_contra hcon
  push Not at hcon
  have hne : (range Q).Nonempty := nonempty_range_iff.mpr hQ.ne'
  have hlt : ∑ _c ∈ range Q, K.card * Nat.totient Q <
      ∑ c ∈ range Q, (K.filter fun j => Nat.Coprime (c + j) Q).card * Q :=
    Finset.sum_lt_sum_of_nonempty hne hcon
  have h3 : ∑ c ∈ range Q, (K.filter fun j => Nat.Coprime (c + j) Q).card * Q =
      K.card * Nat.totient Q * Q := by rw [← Finset.sum_mul, hsum]
  have h4 : ∑ _c ∈ range Q, K.card * Nat.totient Q = Q * (K.card * Nat.totient Q) := by
    rw [Finset.sum_const, card_range, smul_eq_mul]
  rw [h3, h4, mul_comm] at hlt
  exact lt_irrefl _ hlt

lemma rough_shift_card_le_filter (x w N c : ℕ) (hwx : w ≤ x) :
    ∃ M : ℕ, ((Icc (M + 1) (M + N)).filter fun n => ∀ p ≤ x, p.Prime → ¬ p ∣ n).card ≤
      (((Icc 1 N).filter fun j => ∀ p, p.Prime → w < p → p ≤ x → ¬ p ∣ j).filter
        fun j => Nat.Coprime (c + j) (∏ p ∈ (range (w + 1)).filter Nat.Prime, p)).card := by
  have hcop : Nat.Coprime (∏ p ∈ (range (w + 1)).filter Nat.Prime, p)
      (∏ p ∈ (Ioc w x).filter Nat.Prime, p) := by
    refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
    simp only [mem_filter, mem_range, mem_Ioc] at hp hq
    exact (Nat.coprime_primes hp.2 hq.2).mpr (by omega)
  obtain ⟨M, hM1, hM2⟩ : ∃ M : ℕ,
      M ≡ c [MOD ∏ p ∈ (range (w + 1)).filter Nat.Prime, p] ∧
      M ≡ 0 [MOD ∏ p ∈ (Ioc w x).filter Nat.Prime, p] :=
    ⟨(Nat.chineseRemainder hcop c 0 : ℕ), (Nat.chineseRemainder hcop c 0).2.1,
      (Nat.chineseRemainder hcop c 0).2.2⟩
  refine ⟨M, Finset.card_le_card_of_injOn (fun n => n - M) ?_ ?_⟩
  · intro n hn
    simp only [Finset.mem_coe, mem_filter, mem_Icc] at hn ⊢
    obtain ⟨⟨h1, h2⟩, hr⟩ := hn
    have hnM : M + (n - M) = n := by omega
    refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
    · intro p hp hwp hpx hdvd
      have hpQ : p ∣ ∏ p ∈ (Ioc w x).filter Nat.Prime, p :=
        Finset.dvd_prod_of_mem _ (by simp [hp, hwp, hpx])
      have hpM : p ∣ M := hpQ.trans ((Nat.modEq_zero_iff_dvd).mp hM2)
      have hpn : p ∣ M + (n - M) := Nat.dvd_add hpM hdvd
      rw [hnM] at hpn
      exact hr p hpx hp hpn
    · refine Nat.Coprime.prod_right fun p hp => ?_
      simp only [mem_filter, mem_range] at hp
      rw [Nat.coprime_comm, hp.2.coprime_iff_not_dvd]
      intro hdvd
      have hpQ : p ∣ ∏ p ∈ (range (w + 1)).filter Nat.Prime, p :=
        Finset.dvd_prod_of_mem _ (by simp [hp.1, hp.2])
      have hmod : M ≡ c [MOD p] := hM1.of_dvd hpQ
      have h3 : M + (n - M) ≡ c + (n - M) [MOD p] := hmod.add_right _
      have hpn : p ∣ M + (n - M) :=
        (Nat.modEq_zero_iff_dvd).mp (h3.trans ((Nat.modEq_zero_iff_dvd).mpr hdvd))
      rw [hnM] at hpn
      exact hr p (by omega) hp.2 hpn
  · intro a ha b hb h
    simp only [Finset.mem_coe, mem_filter, mem_Icc] at ha hb
    have h' : a - M = b - M := h
    omega

lemma exists_shift_rough_card_le (x w N : ℕ) (hwx : w ≤ x) :
    ∃ M : ℕ,
      (((Icc (M + 1) (M + N)).filter fun n => ∀ p ≤ x, p.Prime → ¬ p ∣ n).card : ℝ) ≤
        (∏ p ∈ (range (w + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) *
          (((Icc 1 N).filter fun j => ∀ p, p.Prime → w < p → p ≤ x → ¬ p ∣ j).card : ℝ) := by
  have hQpos : 0 < ∏ p ∈ (range (w + 1)).filter Nat.Prime, p :=
    Finset.prod_pos fun p hp => (mem_filter.mp hp).2.pos
  obtain ⟨c, -, hc⟩ := exists_shift_le_avg
    ((Icc 1 N).filter fun j => ∀ p, p.Prime → w < p → p ≤ x → ¬ p ∣ j) _ hQpos
  obtain ⟨M, hM⟩ := rough_shift_card_le_filter x w N c hwx
  refine ⟨M, ?_⟩
  have h1 : (((Icc (M + 1) (M + N)).filter fun n => ∀ p ≤ x, p.Prime → ¬ p ∣ n).card : ℝ) ≤
      ((((Icc 1 N).filter fun j => ∀ p, p.Prime → w < p → p ≤ x → ¬ p ∣ j).filter
        fun j => Nat.Coprime (c + j) (∏ p ∈ (range (w + 1)).filter Nat.Prime, p)).card : ℝ) := by
    exact_mod_cast hM
  have h2 : ((((Icc 1 N).filter fun j => ∀ p, p.Prime → w < p → p ≤ x → ¬ p ∣ j).filter
        fun j => Nat.Coprime (c + j) (∏ p ∈ (range (w + 1)).filter Nat.Prime, p)).card : ℝ) *
        ((∏ p ∈ (range (w + 1)).filter Nat.Prime, p : ℕ) : ℝ) ≤
      (((Icc 1 N).filter fun j => ∀ p, p.Prime → w < p → p ≤ x → ¬ p ∣ j).card : ℝ) *
        ((Nat.totient (∏ p ∈ (range (w + 1)).filter Nat.Prime, p) : ℕ) : ℝ) := by
    exact_mod_cast hc
  rw [totient_prod_primes w] at h2
  have hQR : (0 : ℝ) < ((∏ p ∈ (range (w + 1)).filter Nat.Prime, p : ℕ) : ℝ) := by
    exact_mod_cast hQpos
  refine h1.trans (le_of_mul_le_mul_right ?_ hQR)
  calc _ ≤ _ := h2
    _ = _ := by ring
-- LEMMA B1
lemma card_K_le (x w N : ℕ) :
    ((Icc 1 N).filter fun j => ∀ p, p.Prime → w < p → p ≤ x → ¬ p ∣ j).card ≤
      ((Icc 1 N).filter fun j => ∀ p, p.Prime → p ∣ j → p ≤ w).card +
      ((Icc 1 N).filter fun j => ∃ q, q.Prime ∧ x < q ∧ q ∣ j).card := by
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro j hj
  rw [mem_filter] at hj
  rw [mem_union, mem_filter, mem_filter]
  by_cases h : ∀ p, p.Prime → p ∣ j → p ≤ w
  · exact Or.inl ⟨hj.1, h⟩
  · right
    by_contra hB
    apply h
    intro p hp hpj
    by_contra hpw
    apply hB
    refine ⟨hj.1, p, hp, ?_, hpj⟩
    by_contra hx
    exact hj.2 p hp (not_le.mp hpw) (not_lt.mp hx) hpj

-- LEMMA B2
lemma card_bigprime_le_sum (x N : ℕ) (hx : 1 ≤ x) :
    ((Icc 1 N).filter fun j => ∃ q, q.Prime ∧ x < q ∧ q ∣ j).card ≤
      ∑ m ∈ Icc 1 (N / x), Nat.primeCounting (N / m) := by
  have hsub : ((Icc 1 N).filter fun j => ∃ q, q.Prime ∧ x < q ∧ q ∣ j) ⊆
      (Icc 1 (N / x)).biUnion
        (fun m => ((Icc 1 (N / m)).filter Nat.Prime).image (fun q => m * q)) := by
    intro j hj
    rw [mem_filter, mem_Icc] at hj
    obtain ⟨⟨hj1, hjN⟩, q, hq, hxq, hqj⟩ := hj
    obtain ⟨m, rfl⟩ := hqj
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        simp at hj1
      · exact h
    rw [mem_biUnion]
    refine ⟨m, mem_Icc.mpr ⟨hm, ?_⟩, mem_image.mpr
      ⟨q, mem_filter.mpr ⟨mem_Icc.mpr ⟨hq.one_le, ?_⟩, hq⟩, mul_comm m q⟩⟩
    · rw [Nat.le_div_iff_mul_le (by omega)]
      calc m * x ≤ m * q := Nat.mul_le_mul_left m hxq.le
        _ = q * m := mul_comm _ _
        _ ≤ N := hjN
    · rw [Nat.le_div_iff_mul_le (by omega)]
      exact hjN
  calc ((Icc 1 N).filter fun j => ∃ q, q.Prime ∧ x < q ∧ q ∣ j).card
      ≤ ((Icc 1 (N / x)).biUnion
        (fun m => ((Icc 1 (N / m)).filter Nat.Prime).image (fun q => m * q))).card :=
        card_le_card hsub
    _ ≤ ∑ m ∈ Icc 1 (N / x),
          (((Icc 1 (N / m)).filter Nat.Prime).image (fun q => m * q)).card := card_biUnion_le
    _ ≤ ∑ m ∈ Icc 1 (N / x), Nat.primeCounting (N / m) := by
      refine sum_le_sum fun m _ => ?_
      refine card_image_le.trans ?_
      rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one]

-- LEMMA B3
lemma primeCounting_div_le (x N m : ℕ) (hx : 2 ≤ x) (hm : 1 ≤ m) (hmx : m ≤ N / x) :
    (Nat.primeCounting (N / m) : ℝ) ≤
      3 * ((N : ℝ) / m) / Real.log x + Real.sqrt ((N : ℝ) / m) := by
  have hx0 : 0 < x := by omega
  have hmx' : m * x ≤ N := (Nat.le_div_iff_mul_le hx0).mp hmx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have ht : (x : ℝ) ≤ (N : ℝ) / m := by
    rw [le_div_iff₀ hmR]
    exact_mod_cast (by rw [mul_comm]; exact hmx' : x * m ≤ N)
  have ht0 : (0 : ℝ) ≤ (N : ℝ) / m := by linarith
  have ht1 : (1 : ℝ) < (N : ℝ) / m := by linarith
  have h := Chebyshev.pi_le_log4_mul_div ht1
  rw [Nat.floor_div_eq_div, Real.log_sqrt ht0] at h
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogt : Real.log x ≤ Real.log ((N : ℝ) / m) := Real.log_le_log (by linarith) ht
  have hlog4 : Real.log 4 ≤ 3 / 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    linarith [Real.log_two_lt_d9]
  have hkey : Real.log 4 * ((N : ℝ) / m) / (Real.log ((N : ℝ) / m) / 2) ≤
      3 * ((N : ℝ) / m) / Real.log x := by
    rw [div_le_div_iff₀ (by linarith) hlogx]
    calc Real.log 4 * ((N : ℝ) / m) * Real.log x
        ≤ 3 / 2 * ((N : ℝ) / m) * Real.log x := by gcongr
      _ ≤ 3 / 2 * ((N : ℝ) / m) * Real.log ((N : ℝ) / m) := by gcongr
      _ = 3 * ((N : ℝ) / m) * (Real.log ((N : ℝ) / m) / 2) := by ring
  linarith

-- LEMMA B4
lemma sum_inv_sqrt_le (B : ℕ) :
    ∑ m ∈ Icc 1 B, (1 / Real.sqrt (m : ℝ)) ≤ 2 * Real.sqrt B := by
  induction B with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega)]
    have h1 : (0 : ℝ) < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have h0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hs1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = n + 1 := by
      rw [Real.sq_sqrt (by positivity)]
      push_cast
      ring
    have hs0 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
    have hstep : 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((n + 1 : ℕ) : ℝ) - 2 * Real.sqrt n := by
      rw [div_le_iff₀ h1]
      nlinarith [sq_nonneg (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))]
    linarith

-- LEMMA B5
lemma card_bigprime_le (x N : ℕ) (hx : 2 ≤ x) (hxN : x ≤ N) :
    (((Icc 1 N).filter fun j => ∃ q, q.Prime ∧ x < q ∧ q ∣ j).card : ℝ) ≤
      3 * N * (1 + Real.log ((N : ℝ) / x)) / Real.log x + 2 * N / Real.sqrt x := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hB1 : 1 ≤ N / x := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hxN)
  have hBle : ((N / x : ℕ) : ℝ) ≤ (N : ℝ) / x := Nat.cast_div_le
  have h1 : (((Icc 1 N).filter fun j => ∃ q, q.Prime ∧ x < q ∧ q ∣ j).card : ℝ) ≤
      ∑ m ∈ Icc 1 (N / x),
        (3 * ((N : ℝ) / m) / Real.log x + Real.sqrt ((N : ℝ) / m)) := by
    have h := card_bigprime_le_sum x N (by omega)
    calc (((Icc 1 N).filter fun j => ∃ q, q.Prime ∧ x < q ∧ q ∣ j).card : ℝ)
        ≤ ((∑ m ∈ Icc 1 (N / x), Nat.primeCounting (N / m) : ℕ) : ℝ) := by exact_mod_cast h
      _ = ∑ m ∈ Icc 1 (N / x), (Nat.primeCounting (N / m) : ℝ) := by push_cast; rfl
      _ ≤ _ := sum_le_sum fun m hm =>
          primeCounting_div_le x N m hx (mem_Icc.mp hm).1 (mem_Icc.mp hm).2
  have h2 : ∑ m ∈ Icc 1 (N / x), (3 * ((N : ℝ) / m) / Real.log x) =
      3 * N / Real.log x * ∑ m ∈ Icc 1 (N / x), ((m : ℝ))⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    ring
  have h3 : ∑ m ∈ Icc 1 (N / x), ((m : ℝ))⁻¹ ≤ 1 + Real.log ((N : ℝ) / x) := by
    have h := harmonic_le_one_add_log (N / x)
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    have hl : Real.log ((N / x : ℕ) : ℝ) ≤ Real.log ((N : ℝ) / x) :=
      Real.log_le_log (by exact_mod_cast hB1) hBle
    linarith
  have h4 : ∑ m ∈ Icc 1 (N / x), Real.sqrt ((N : ℝ) / m) =
      Real.sqrt N * ∑ m ∈ Icc 1 (N / x), (1 / Real.sqrt (m : ℝ)) := by
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [Real.sqrt_div (Nat.cast_nonneg N)]
    ring
  have h5 : Real.sqrt N * ∑ m ∈ Icc 1 (N / x), (1 / Real.sqrt (m : ℝ)) ≤
      2 * N / Real.sqrt x := by
    have hs := sum_inv_sqrt_le (N / x)
    have hsB : Real.sqrt ((N / x : ℕ) : ℝ) ≤ Real.sqrt N / Real.sqrt x := by
      rw [← Real.sqrt_div (Nat.cast_nonneg N)]
      exact Real.sqrt_le_sqrt hBle
    have hN0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    calc Real.sqrt N * ∑ m ∈ Icc 1 (N / x), (1 / Real.sqrt (m : ℝ))
        ≤ Real.sqrt N * (2 * (Real.sqrt N / Real.sqrt x)) :=
          mul_le_mul_of_nonneg_left (by linarith) hN0
      _ = 2 * (Real.sqrt N * Real.sqrt N) / Real.sqrt x := by ring
      _ = 2 * N / Real.sqrt x := by rw [Real.mul_self_sqrt (Nat.cast_nonneg N)]
  rw [sum_add_distrib, h2, h4] at h1
  have h6 : 3 * N / Real.log x * ∑ m ∈ Icc 1 (N / x), ((m : ℝ))⁻¹ ≤
      3 * N * (1 + Real.log ((N : ℝ) / x)) / Real.log x := by
    have hnn : 0 ≤ 3 * (N : ℝ) / Real.log x := by positivity
    calc 3 * N / Real.log x * ∑ m ∈ Icc 1 (N / x), ((m : ℝ))⁻¹
        ≤ 3 * N / Real.log x * (1 + Real.log ((N : ℝ) / x)) :=
          mul_le_mul_of_nonneg_left h3 hnn
      _ = 3 * N * (1 + Real.log ((N : ℝ) / x)) / Real.log x := by ring
  linarith

-- LEMMA D2
lemma eventually_floor_rpow (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ∀ᶠ x : ℕ in atTop,
      2 ≤ ⌊(x : ℝ) ^ α⌋₊ ∧ ⌊(x : ℝ) ^ α⌋₊ ^ 4 ≤ x ∧
        α / 2 * Real.log x ≤ Real.log (⌊(x : ℝ) ^ α⌋₊ : ℝ) ∧
        Real.log (⌊(x : ℝ) ^ α⌋₊ : ℝ) ≤ α * Real.log x := by
  have ht : Tendsto (fun x : ℕ => (x : ℝ) ^ (α / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < α / 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 2, eventually_ge_atTop 1] with x hy hx1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have hx1R : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hxa : (x : ℝ) ^ α = (x : ℝ) ^ (α / 2) * (x : ℝ) ^ (α / 2) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hxa0 : 0 ≤ (x : ℝ) ^ α := (Real.rpow_pos_of_pos hxpos _).le
  have hF1 : (⌊(x : ℝ) ^ α⌋₊ : ℝ) ≤ (x : ℝ) ^ α := Nat.floor_le hxa0
  have hF2 : (x : ℝ) ^ α < (⌊(x : ℝ) ^ α⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hFy : (x : ℝ) ^ (α / 2) ≤ (⌊(x : ℝ) ^ α⌋₊ : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hy (by linarith : (0 : ℝ) ≤ (x : ℝ) ^ (α / 2))]
  have hFpos : (0 : ℝ) < (⌊(x : ℝ) ^ α⌋₊ : ℝ) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast (le_trans hy hFy)
  · have h4 : ((⌊(x : ℝ) ^ α⌋₊ : ℝ)) ^ 4 ≤ (x : ℝ) := by
      calc ((⌊(x : ℝ) ^ α⌋₊ : ℝ)) ^ 4 ≤ ((x : ℝ) ^ α) ^ 4 := pow_le_pow_left₀ hFpos.le hF1 4
        _ = (x : ℝ) ^ (α * 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
          norm_num
        _ ≤ (x : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1R (by linarith)
        _ = x := Real.rpow_one _
    exact_mod_cast h4
  · have hl : Real.log ((x : ℝ) ^ (α / 2)) = α / 2 * Real.log x := Real.log_rpow hxpos _
    rw [← hl]
    exact Real.log_le_log (by linarith) hFy
  · have hl : Real.log ((x : ℝ) ^ α) = α * Real.log x := Real.log_rpow hxpos _
    rw [← hl]
    exact Real.log_le_log hFpos hF1

-- LEMMA D3
lemma eventually_small_terms (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      1 / α * (14 / (x : ℝ) ^ ((1 : ℝ) / 4) + 12 / Real.log x + 4 / Real.sqrt x) < δ := by
  have hc : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun x : ℕ => 14 / (x : ℝ) ^ ((1 : ℝ) / 4)) atTop (nhds 0) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hc).const_div_atTop 14
  have h2 : Tendsto (fun x : ℕ => 12 / Real.log (x : ℝ)) atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp hc).const_div_atTop 12
  have h3 : Tendsto (fun x : ℕ => 4 / Real.sqrt (x : ℝ)) atTop (nhds 0) :=
    (Real.tendsto_sqrt_atTop.comp hc).const_div_atTop 4
  have h : Tendsto (fun x : ℕ =>
      1 / α * (14 / (x : ℝ) ^ ((1 : ℝ) / 4) + 12 / Real.log x + 4 / Real.sqrt x))
      atTop (nhds (1 / α * (0 + 0 + 0))) := ((h1.add h2).add h3).const_mul (1 / α)
  have h' : Tendsto (fun x : ℕ =>
      1 / α * (14 / (x : ℝ) ^ ((1 : ℝ) / 4) + 12 / Real.log x + 4 / Real.sqrt x))
      atTop (nhds 0) := by simpa using h
  exact (tendsto_order.1 h').2 δ hδ

-- LEMMA D4
lemma ceil_rpow_facts (ε : ℝ) (hε : 0 < ε) (x : ℕ) (hx : 2 ≤ x) :
    x ≤ ⌈(x : ℝ) ^ (1 + ε)⌉₊ ∧
      Real.log ((⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) / x) ≤ 1 + ε * Real.log x := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
  have hp : (x : ℝ) ≤ (x : ℝ) ^ (1 + ε) := by
    calc (x : ℝ) = (x : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (x : ℝ) ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hc1 : (x : ℝ) ^ (1 + ε) ≤ (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) < (x : ℝ) ^ (1 + ε) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_pos_of_pos hxpos _).le
  refine ⟨by exact_mod_cast hp.trans hc1, ?_⟩
  have hsplit : (x : ℝ) ^ (1 + ε) = x * (x : ℝ) ^ ε := by
    rw [Real.rpow_add hxpos, Real.rpow_one]
  have hxe : (0 : ℝ) < (x : ℝ) ^ ε := Real.rpow_pos_of_pos hxpos _
  have hle : (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) / x ≤ 2 * (x : ℝ) ^ ε := by
    rw [div_le_iff₀ hxpos]
    nlinarith
  have hpos : (0 : ℝ) < (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) / x := by
    apply div_pos _ hxpos
    linarith
  calc Real.log ((⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) / x)
      ≤ Real.log (2 * (x : ℝ) ^ ε) := Real.log_le_log hpos hle
    _ = Real.log 2 + ε * Real.log x := by
      rw [Real.log_mul (by norm_num) hxe.ne', Real.log_rpow hxpos]
    _ ≤ 1 + ε * Real.log x := by linarith [Real.log_two_lt_d9]

lemma explicit_bound_lt_aux1 (α lx lw : ℝ) (hα : 0 < α) (hlx : 0 < lx)
    (hlw1 : α / 2 * lx ≤ lw) : 0 < lw⁻¹ ∧ lw⁻¹ ≤ 2 / (α * lx) := by
  have h0 : 0 < α / 2 * lx := by positivity
  have hlw : 0 < lw := lt_of_lt_of_le h0 hlw1
  refine ⟨inv_pos.mpr hlw, ?_⟩
  rw [inv_eq_one_div, div_le_div_iff₀ hlw (by positivity)]
  nlinarith

lemma explicit_bound_lt_aux2 (α lx lw lN N : ℝ) (hα : 0 < α) (hlx : 0 < lx)
    (hlw1 : α / 2 * lx ≤ lw) (hlw2 : lw ≤ α * lx) (hlN : lx ≤ lN) (hN : 0 < N) :
    lw⁻¹ * (2048 * N * lw ^ 2 / lN ^ 2) ≤ N / lx * (2048 * α) := by
  have h0 : 0 < α / 2 * lx := by positivity
  have hlw : 0 < lw := lt_of_lt_of_le h0 hlw1
  have hlN0 : 0 < lN := lt_of_lt_of_le hlx hlN
  have e1 : lw⁻¹ * (2048 * N * lw ^ 2 / lN ^ 2) = 2048 * N * lw / lN ^ 2 := by
    field_simp
  have e2 : N / lx * (2048 * α) = 2048 * N * (α * lx) / lx ^ 2 := by
    field_simp
  rw [e1, e2]
  apply div_le_div₀ (by positivity) _ (by positivity) (pow_le_pow_left₀ hlx.le hlN 2)
  exact mul_le_mul_of_nonneg_left hlw2 (by positivity)

lemma explicit_bound_lt_aux3 (α lx u N T s4 : ℝ) (hα : 0 < α) (hlx : 0 < lx)
    (hu : 0 < u) (hu2 : u ≤ 2 / (α * lx)) (hN : 0 < N) (hs4 : 0 < s4) (hT : T ≤ N / s4) :
    u * (7 * T) ≤ N / lx * (1 / α * (14 / s4)) := by
  have h1 : u * (7 * T) ≤ u * (7 * (N / s4)) :=
    mul_le_mul_of_nonneg_left (by linarith) hu.le
  have h2 : u * (7 * (N / s4)) ≤ 2 / (α * lx) * (7 * (N / s4)) :=
    mul_le_mul_of_nonneg_right hu2 (by positivity)
  have e : 2 / (α * lx) * (7 * (N / s4)) = N / lx * (1 / α * (14 / s4)) := by
    field_simp
    ring
  linarith

lemma explicit_bound_lt_aux4 (α ε lx u N LNX : ℝ) (hα : 0 < α) (hε : 0 < ε) (hlx : 0 < lx)
    (hu : 0 < u) (hu2 : u ≤ 2 / (α * lx)) (hN : 0 < N) (hLNX : LNX ≤ 1 + ε * lx) :
    u * (3 * N * (1 + LNX) / lx) ≤ N / lx * (1 / α * (12 / lx) + 6 * ε / α) := by
  have h0 : 3 * N * (1 + LNX) / lx ≤ 3 * N * (2 + ε * lx) / lx := by
    apply div_le_div_of_nonneg_right _ hlx.le
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h1 : u * (3 * N * (1 + LNX) / lx) ≤ u * (3 * N * (2 + ε * lx) / lx) :=
    mul_le_mul_of_nonneg_left h0 hu.le
  have h2 : u * (3 * N * (2 + ε * lx) / lx) ≤ 2 / (α * lx) * (3 * N * (2 + ε * lx) / lx) :=
    mul_le_mul_of_nonneg_right hu2 (by positivity)
  have e : 2 / (α * lx) * (3 * N * (2 + ε * lx) / lx) =
      N / lx * (1 / α * (12 / lx) + 6 * ε / α) := by
    field_simp
    ring
  linarith

lemma explicit_bound_lt_aux5 (α lx u N sx : ℝ) (hα : 0 < α) (hlx : 0 < lx)
    (hu : 0 < u) (hu2 : u ≤ 2 / (α * lx)) (hN : 0 < N) (hsx : 0 < sx) :
    u * (2 * N / sx) ≤ N / lx * (1 / α * (4 / sx)) := by
  have h2 : u * (2 * N / sx) ≤ 2 / (α * lx) * (2 * N / sx) :=
    mul_le_mul_of_nonneg_right hu2 (by positivity)
  have e : 2 / (α * lx) * (2 * N / sx) = N / lx * (1 / α * (4 / sx)) := by
    field_simp
    ring
  linarith

-- LEMMA D5
lemma explicit_bound_lt (c α ε lx lw lN N T s4 sx LNX : ℝ) (hc : 0 < c) (hα : 0 < α)
    (hαc : α ≤ c / 8192) (hε : 0 < ε) (hεc : ε ≤ c * α / 24) (hlx : 0 < lx)
    (hlw1 : α / 2 * lx ≤ lw) (hlw2 : lw ≤ α * lx) (hlN : lx ≤ lN) (hN : 0 < N)
    (hs4 : 0 < s4) (hsx : 0 < sx) (hT : T ≤ N / s4) (hLNX : LNX ≤ 1 + ε * lx)
    (hsmall : 1 / α * (14 / s4 + 12 / lx + 4 / sx) < c / 4) :
    lw⁻¹ * (2048 * N * lw ^ 2 / lN ^ 2 + 7 * T + 3 * N * (1 + LNX) / lx + 2 * N / sx) <
      c * N / lx := by
  obtain ⟨hu, hu2⟩ := explicit_bound_lt_aux1 α lx lw hα hlx hlw1
  have a2 := explicit_bound_lt_aux2 α lx lw lN N hα hlx hlw1 hlw2 hlN hN
  have a3 := explicit_bound_lt_aux3 α lx lw⁻¹ N T s4 hα hlx hu hu2 hN hs4 hT
  have a4 := explicit_bound_lt_aux4 α ε lx lw⁻¹ N LNX hα hε hlx hu hu2 hN hLNX
  have a5 := explicit_bound_lt_aux5 α lx lw⁻¹ N sx hα hlx hu hu2 hN hsx
  have hNl : 0 < N / lx := div_pos hN hlx
  have he : 6 * ε / α ≤ c / 4 := by
    rw [div_le_iff₀ hα]
    linarith
  have hsum : 2048 * α + 1 / α * (14 / s4) + (1 / α * (12 / lx) + 6 * ε / α) +
      1 / α * (4 / sx) < c := by
    have hexp : 1 / α * (14 / s4 + 12 / lx + 4 / sx) =
        1 / α * (14 / s4) + 1 / α * (12 / lx) + 1 / α * (4 / sx) := by ring
    linarith
  have hfin : N / lx * (2048 * α + 1 / α * (14 / s4) + (1 / α * (12 / lx) + 6 * ε / α) +
      1 / α * (4 / sx)) < N / lx * c := mul_lt_mul_of_pos_left hsum hNl
  have hrw : c * N / lx = N / lx * c := by ring
  rw [hrw]
  calc lw⁻¹ * (2048 * N * lw ^ 2 / lN ^ 2 + 7 * T + 3 * N * (1 + LNX) / lx + 2 * N / sx)
      = lw⁻¹ * (2048 * N * lw ^ 2 / lN ^ 2) + lw⁻¹ * (7 * T) +
          lw⁻¹ * (3 * N * (1 + LNX) / lx) + lw⁻¹ * (2 * N / sx) := by ring
    _ ≤ N / lx * (2048 * α) + N / lx * (1 / α * (14 / s4)) +
          N / lx * (1 / α * (12 / lx) + 6 * ε / α) + N / lx * (1 / α * (4 / sx)) := by
        linarith
    _ = N / lx * (2048 * α + 1 / α * (14 / s4) + (1 / α * (12 / lx) + 6 * ε / α) +
          1 / α * (4 / sx)) := by ring
    _ < N / lx * c := hfin

-- LEMMA C1
lemma log_eq_sum_prime_pow_aux1 (N n p : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (pp : p.Prime) :
    ((n.factorization p : ℕ) : ℝ) * Real.log p =
      ∑ i ∈ Icc 1 (Nat.log 2 N), if p ^ i ∣ n then Real.log p else 0 := by
  have hlt : n < p ^ (Nat.log 2 N + 1) := by
    have h1 : n < 2 ^ (Nat.log 2 N + 1) :=
      lt_of_le_of_lt hnN (Nat.lt_pow_succ_log_self (by norm_num) N)
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_left pp.two_le _)
  rw [Nat.factorization_eq_card_pow_dvd_of_lt pp (by omega) hlt]
  have hI : Ico 1 (Nat.log 2 N + 1) = Icc 1 (Nat.log 2 N) := by
    ext i; simp only [mem_Ico, mem_Icc]; omega
  rw [hI, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma log_eq_sum_prime_pow (w N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hs : ∀ p, p.Prime → p ∣ n → p ≤ w) :
    Real.log n = ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 (Nat.log 2 N),
      if p ^ i ∣ n then Real.log p else 0 := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have hsub : n.factorization.support ⊆ (range (w + 1)).filter Nat.Prime := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have pp := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (hs p pp hd)), pp⟩
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun p hp => ?_
    exact log_eq_sum_prime_pow_aux1 N n p hn hnN (mem_filter.mp hp).2
  · intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp]
    simp

-- LEMMA C2
lemma card_smooth_dvd_le (w N d : ℕ) (hd : 1 ≤ d) :
    (((Icc 1 N).filter fun j => ∀ p, p.Prime → p ∣ j → p ≤ w).filter fun n => d ∣ n).card ≤
      ((Icc 1 (N / d)).filter fun j => ∀ q, q.Prime → q ∣ j → q ≤ w).card := by
  refine Finset.card_le_card_of_injOn (fun n => n / d) ?_ ?_
  · intro n hn
    have hn' := mem_filter.mp (Finset.mem_coe.mp hn)
    obtain ⟨h1, hsm⟩ := mem_filter.mp hn'.1
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp h1
    obtain ⟨k, rfl⟩ := hn'.2
    have hk : d * k / d = k := Nat.mul_div_cancel_left k (by omega)
    refine Finset.mem_coe.mpr (mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩)
    · show 1 ≤ d * k / d
      rw [hk]
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at hn1
      · exact h
    · exact Nat.div_le_div_right hnN
    · intro q hq hqk
      have hqk' : q ∣ k := by simpa [hk] using hqk
      exact hsm q hq (Dvd.dvd.mul_left hqk' d)
  · intro a ha b hb hab
    have ha' := (mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hb' := (mem_filter.mp (Finset.mem_coe.mp hb)).2
    have hab' : a / d = b / d := hab
    rw [← Nat.div_mul_cancel ha', ← Nat.div_mul_cancel hb', hab']

-- LEMMA C3
lemma sum_log_smooth_le (w N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (fun j => ∀ p, p.Prime → p ∣ j → p ≤ w), Real.log n ≤
      ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 (Nat.log 2 N),
        Real.log p *
          (((Icc 1 (N / p ^ i)).filter fun j => ∀ q, q.Prime → q ∣ j → q ≤ w).card : ℝ) := by
  have h1 : ∑ n ∈ (Icc 1 N).filter (fun j => ∀ p, p.Prime → p ∣ j → p ≤ w), Real.log n =
      ∑ n ∈ (Icc 1 N).filter (fun j => ∀ p, p.Prime → p ∣ j → p ≤ w),
        ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 (Nat.log 2 N),
          if p ^ i ∣ n then Real.log p else 0 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h1, hsm⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp h1
    exact log_eq_sum_prime_pow w N n hn1 hnN hsm
  rw [h1, Finset.sum_comm]
  refine Finset.sum_le_sum fun p hp => ?_
  have pp : p.Prime := (mem_filter.mp hp).2
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast pp.one_lt.le)
  refine mul_le_mul_of_nonneg_left ?_ hlog
  exact_mod_cast card_smooth_dvd_le w N (p ^ i) (Nat.one_le_pow _ _ pp.pos)

-- LEMMA C4
lemma sum_pow_inv_le_aux1 (p : ℕ) (hp : 2 ≤ p) (I : ℕ) :
    ∑ i ∈ Icc 1 (I + 1), 1 / (p : ℝ) ^ i ≤ 1 / p + 2 / (p : ℝ) ^ 2 - 2 / (p : ℝ) ^ (I + 2) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  induction I with
  | zero => simp
  | succ I ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hpow : (0 : ℝ) < (p : ℝ) ^ (I + 2) := pow_pos hp0 _
    have h1 : 2 / (p : ℝ) ^ (I + 1 + 2) ≤ 1 / (p : ℝ) ^ (I + 2) := by
      rw [show I + 1 + 2 = (I + 2) + 1 by ring, pow_succ, div_le_div_iff₀ (by positivity) hpow]
      nlinarith
    have h2 : (I + 1 + 1) = I + 2 := by ring
    rw [h2]
    have h3 : 2 / (p : ℝ) ^ (I + 2) = 2 * (1 / (p : ℝ) ^ (I + 2)) := by ring
    linarith

lemma sum_pow_inv_le (p I : ℕ) (hp : 2 ≤ p) :
    ∑ i ∈ Icc 1 I, 1 / (p : ℝ) ^ i ≤ 1 / p + 2 / (p : ℝ) ^ 2 := by
  rcases I with _ | I
  · simp only [zero_lt_one, Icc_eq_empty_of_lt, sum_empty]
    positivity
  · have h := sum_pow_inv_le_aux1 p hp I
    have hpos : (0 : ℝ) ≤ 2 / (p : ℝ) ^ (I + 2) := by positivity
    linarith

-- LEMMA C5
lemma sum_inv_mul_sqrt_le_aux1 (m : ℕ) (hm : 1 ≤ m) :
    1 / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤
      2 / Real.sqrt (m : ℝ) - 2 / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set a := Real.sqrt (m : ℝ) with ha
  set b := Real.sqrt ((m + 1 : ℕ) : ℝ) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr hm0
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a * a = m := Real.mul_self_sqrt hm0.le
  have hb2 : b * b = ((m + 1 : ℕ) : ℝ) := Real.mul_self_sqrt (by positivity)
  have hb2' : b * b = a * a + 1 := by rw [hb2, ha2]; push_cast; ring
  have hab : a ≤ b := Real.sqrt_le_sqrt (by push_cast; linarith)
  rw [← hb2]
  have hd : (b - a) * (b + a) = 1 := by nlinarith
  have hba : 0 < b - a := by
    by_contra h
    push Not at h
    nlinarith
  have key : 2 / a - 2 / b = 2 * (b - a) / (a * b) := by
    field_simp
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (b - a) * (b + a) ≤ (b - a) * (2 * b) :=
    mul_le_mul_of_nonneg_left (by linarith) hba.le
  have h4 : a * b ≤ b * b := by nlinarith
  have h5 : 0 < b * b := by positivity
  calc 1 * (a * b) ≤ 1 * (b * b) := by nlinarith
    _ ≤ ((b - a) * (2 * b)) * (b * b) := by nlinarith
    _ = 2 * (b - a) * (b * b * b) := by ring

lemma sum_inv_mul_sqrt_le_aux2 (w : ℕ) :
    ∑ n ∈ Icc 2 (w + 1), 1 / ((n : ℝ) * Real.sqrt n) ≤
      2 - 2 / Real.sqrt ((w + 1 : ℕ) : ℝ) := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h := sum_inv_mul_sqrt_le_aux1 (w + 1) (by omega)
    linarith

lemma sum_inv_mul_sqrt_le (w : ℕ) :
    ∑ n ∈ Icc 2 w, 1 / ((n : ℝ) * Real.sqrt n) ≤ 2 := by
  rcases w with _ | w
  · simp
  · have h := sum_inv_mul_sqrt_le_aux2 w
    have hpos : (0 : ℝ) ≤ 2 / Real.sqrt ((w + 1 : ℕ) : ℝ) := by positivity
    linarith

-- LEMMA C6
lemma sum_log_div_prime_pow_le_aux1 (p I : ℕ) (pp : p.Prime) :
    ∑ i ∈ Icc 1 I, Real.log p / (p : ℝ) ^ i ≤
      Real.log p / p + 4 * (1 / ((p : ℝ) * Real.sqrt p)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast pp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  set s := Real.sqrt (p : ℝ) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hp0
  have hss : s * s = p := Real.mul_self_sqrt hp0.le
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hlog : Real.log p ≤ 2 * s := by
    have h1 : Real.log s = Real.log p / 2 := Real.log_sqrt hp0.le
    have h2 := Real.log_le_sub_one_of_pos hs0
    linarith
  have h1 : ∑ i ∈ Icc 1 I, Real.log p / (p : ℝ) ^ i =
      Real.log p * ∑ i ∈ Icc 1 I, 1 / (p : ℝ) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  have h2 := mul_le_mul_of_nonneg_left (sum_pow_inv_le p I pp.two_le) hlog0
  have h3 : Real.log p * (2 / (p : ℝ) ^ 2) ≤ 4 * (1 / ((p : ℝ) * s)) := by
    have e : 4 * (1 / ((p : ℝ) * s)) = (2 * s) * (2 / (p : ℝ) ^ 2) := by
      rw [← hss]
      field_simp
      norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_right hlog (by positivity)
  calc Real.log p * ∑ i ∈ Icc 1 I, 1 / (p : ℝ) ^ i
      ≤ Real.log p * (1 / p + 2 / (p : ℝ) ^ 2) := h2
    _ = Real.log p / p + Real.log p * (2 / (p : ℝ) ^ 2) := by ring
    _ ≤ _ := by linarith

lemma sum_log_div_prime_pow_le (w I : ℕ) (hw : 1 ≤ w) :
    ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 I, Real.log p / (p : ℝ) ^ i ≤
      Real.log w + 10 := by
  have h1 : ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 I, Real.log p / (p : ℝ) ^ i ≤
      ∑ p ∈ (range (w + 1)).filter Nat.Prime,
        (Real.log p / p + 4 * (1 / ((p : ℝ) * Real.sqrt p))) :=
    Finset.sum_le_sum fun p hp => sum_log_div_prime_pow_le_aux1 p I (mem_filter.mp hp).2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  have h2 := OMA.Mertens687.A_le w hw
  have h3 : ∑ p ∈ (range (w + 1)).filter Nat.Prime, 1 / ((p : ℝ) * Real.sqrt p) ≤
      ∑ n ∈ Icc 2 w, 1 / ((n : ℝ) * Real.sqrt n) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
    intro p hp
    obtain ⟨hr, pp⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨pp.two_le, Nat.lt_succ_iff.mp (mem_range.mp hr)⟩
  have h4 := sum_inv_mul_sqrt_le w
  have h5 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  linarith

-- LEMMA C7
lemma card_smooth_mul_log_le (w N : ℕ) (hN : 1 ≤ N) :
    ((((Icc 1 N).filter fun j => ∀ p, p.Prime → p ∣ j → p ≤ w).card : ℝ) - Real.sqrt N) *
        (Real.log N / 2) ≤
      ∑ n ∈ (Icc 1 N).filter (fun j => ∀ p, p.Prime → p ∣ j → p ≤ w), Real.log n := by
  set S := (Icc 1 N).filter (fun j => ∀ p, p.Prime → p ∣ j → p ≤ w) with hS
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun n => n * n ≤ N)
  have hsmall : (S.filter fun n => n * n ≤ N).card ≤ Nat.sqrt N := by
    have hsub : (S.filter fun n => n * n ≤ N) ⊆ Icc 1 (Nat.sqrt N) := by
      intro n hn
      obtain ⟨hnS, hnn⟩ := mem_filter.mp hn
      have h1 := (mem_Icc.mp (mem_filter.mp hnS).1).1
      exact mem_Icc.mpr ⟨h1, Nat.le_sqrt.mpr hnn⟩
    simpa using Finset.card_le_card hsub
  have hsmall' : ((S.filter fun n => n * n ≤ N).card : ℝ) ≤ Real.sqrt N :=
    le_trans (by exact_mod_cast hsmall) Real.nat_sqrt_le_real_sqrt
  have hbig : ((S.filter fun n => ¬ n * n ≤ N).card : ℝ) * (Real.log N / 2) ≤
      ∑ n ∈ S.filter (fun n => ¬ n * n ≤ N), Real.log n := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hnS, hnn⟩ := mem_filter.mp hn
    have h1 := (mem_Icc.mp (mem_filter.mp hnS).1).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have h2 : (N : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : N ≤ n * n := by omega
      rw [pow_two]
      exact_mod_cast this
    have h3 := Real.log_le_log (by exact_mod_cast hN) h2
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  have hsum : ∑ n ∈ S.filter (fun n => ¬ n * n ≤ N), Real.log n ≤ ∑ n ∈ S, Real.log n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n hn _ => ?_
    have h1 := (mem_Icc.mp (mem_filter.mp hn).1).1
    exact Real.log_nonneg (by exact_mod_cast h1)
  have hc : (S.card : ℝ) =
      ((S.filter fun n => n * n ≤ N).card : ℝ) + ((S.filter fun n => ¬ n * n ≤ N).card : ℝ) := by
    exact_mod_cast hcard.symm
  have h6 : ((S.card : ℝ) - Real.sqrt N) * (Real.log N / 2) ≤
      ((S.filter fun n => ¬ n * n ≤ N).card : ℝ) * (Real.log N / 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

-- LEMMA C8
lemma card_smooth_le_first_aux1 (w t : ℕ) :
    (((Icc 1 t).filter fun j => ∀ p, p.Prime → p ∣ j → p ≤ w).card : ℝ) ≤ t := by
  have h := Finset.card_filter_le (Icc 1 t) (fun j => ∀ p, p.Prime → p ∣ j → p ≤ w)
  rw [Nat.card_Icc] at h
  have h' : ((Icc 1 t).filter fun j => ∀ p, p.Prime → p ∣ j → p ≤ w).card ≤ t := by omega
  exact_mod_cast h'

lemma card_smooth_le_first_aux2 (w N : ℕ) (hw : 1 ≤ w) :
    ∑ n ∈ (Icc 1 N).filter (fun j => ∀ p, p.Prime → p ∣ j → p ≤ w), Real.log n ≤
      N * (Real.log w + 10) := by
  refine le_trans (sum_log_smooth_le w N) ?_
  have h1 : ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 (Nat.log 2 N),
        Real.log p *
          (((Icc 1 (N / p ^ i)).filter fun j => ∀ q, q.Prime → q ∣ j → q ≤ w).card : ℝ) ≤
      ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 (Nat.log 2 N),
        (N : ℝ) * (Real.log p / (p : ℝ) ^ i) := by
    refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun i _ => ?_
    have pp : p.Prime := (mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast pp.one_lt.le)
    have h2 : (((Icc 1 (N / p ^ i)).filter fun j => ∀ q, q.Prime → q ∣ j → q ≤ w).card : ℝ) ≤
        (N : ℝ) / (p : ℝ) ^ i := by
      refine le_trans (card_smooth_le_first_aux1 w (N / p ^ i)) ?_
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := p ^ i)
      simpa using this
    calc Real.log p * _ ≤ Real.log p * ((N : ℝ) / (p : ℝ) ^ i) :=
          mul_le_mul_of_nonneg_left h2 hlog
      _ = (N : ℝ) * (Real.log p / (p : ℝ) ^ i) := by ring
  refine le_trans h1 ?_
  simp_rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_log_div_prime_pow_le w _ hw) (Nat.cast_nonneg N)

lemma card_smooth_le_first (w N : ℕ) (hw : 1 ≤ w) (hN : 2 ≤ N) :
    (((Icc 1 N).filter fun j => ∀ p, p.Prime → p ∣ j → p ≤ w).card : ℝ) ≤
      Real.sqrt N + 2 * N * (Real.log w + 10) / Real.log N := by
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have h1 := card_smooth_mul_log_le w N (by omega)
  have h2 := card_smooth_le_first_aux2 w N hw
  have h3 : (((Icc 1 N).filter fun j => ∀ p, p.Prime → p ∣ j → p ≤ w).card : ℝ) - Real.sqrt N ≤
      2 * N * (Real.log w + 10) / Real.log N := by
    rw [le_div_iff₀ hlogN]
    linarith
  linarith

-- LEMMA C9
lemma card_smooth_div_le (w N d : ℕ) (hw : 1 ≤ w) (hN : 16 ≤ N) (hd : 1 ≤ d) :
    (((Icc 1 (N / d)).filter fun j => ∀ p, p.Prime → p ∣ j → p ≤ w).card : ℝ) ≤
      Real.sqrt N + 4 * ((N : ℝ) / d) * (Real.log w + 10) / Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hc : 0 < Real.log w + 10 := by
    have : 0 ≤ Real.log w := Real.log_nonneg (by exact_mod_cast hw)
    linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have htle : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have hsec : 0 ≤ 4 * ((N : ℝ) / d) * (Real.log w + 10) / Real.log N := by positivity
  by_cases hcase : N ≤ (N / d) * (N / d)
  · set t := N / d with ht
    have ht4 : 4 ≤ t := by
      by_contra h
      push Not at h
      have : t * t ≤ 3 * 3 := Nat.mul_le_mul (by omega) (by omega)
      omega
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
    have h1 := card_smooth_le_first w t hw (by omega)
    have hlogt : Real.log N / 2 ≤ Real.log t := by
      have h2 : (N : ℝ) ≤ (t : ℝ) ^ 2 := by
        rw [pow_two]; exact_mod_cast hcase
      have h3 := Real.log_le_log hN0 h2
      rw [Real.log_pow] at h3
      push_cast at h3
      linarith
    have hlogt0 : 0 < Real.log t := by linarith
    have htN : (t : ℝ) ≤ N := by
      exact_mod_cast Nat.div_le_self N d
    have hsq : Real.sqrt t ≤ Real.sqrt N := Real.sqrt_le_sqrt htN
    have h4 : 2 * (t : ℝ) * (Real.log w + 10) / Real.log t ≤
        4 * ((N : ℝ) / d) * (Real.log w + 10) / Real.log N := by
      rw [div_le_div_iff₀ hlogt0 hlogN]
      have e1 : 2 * (t : ℝ) * (Real.log w + 10) * Real.log N ≤
          2 * ((N : ℝ) / d) * (Real.log w + 10) * Real.log N := by
        have := mul_le_mul_of_nonneg_right htle (mul_pos hc hlogN).le
        nlinarith
      have e2 : 2 * ((N : ℝ) / d) * (Real.log w + 10) * Real.log N ≤
          4 * ((N : ℝ) / d) * (Real.log w + 10) * Real.log t := by
        have hpos : 0 ≤ ((N : ℝ) / d) * (Real.log w + 10) := by positivity
        have := mul_le_mul_of_nonneg_left hlogt hpos
        nlinarith
      linarith
    linarith
  · push Not at hcase
    have h1 := card_smooth_le_first_aux1 w (N / d)
    have h2 : ((N / d : ℕ) : ℝ) ≤ Real.sqrt N := by
      apply Real.le_sqrt_of_sq_le
      rw [pow_two]
      exact_mod_cast hcase.le
    linarith

-- LEMMA C10
lemma sum_log_smooth_le_second_aux1 (w N : ℕ) (hN : 1 ≤ N) (hwN : w ^ 4 ≤ N) :
    (w : ℝ) * Real.sqrt N ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set a := (N : ℝ) ^ ((1 : ℝ) / 4) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg hN0.le _
  have ha4 : a ^ 4 = (N : ℝ) := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hw4 : (w : ℝ) ^ 4 ≤ a ^ 4 := by
    rw [ha4]; exact_mod_cast hwN
  have hwa : (w : ℝ) ≤ a :=
    (pow_le_pow_iff_left₀ (Nat.cast_nonneg w) ha0 (by norm_num)).mp hw4
  have hsplit : (N : ℝ) ^ ((3 : ℝ) / 4) = a * Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, ha, ← Real.rpow_add hN0]
    norm_num
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hwa (Real.sqrt_nonneg _)

lemma sum_log_smooth_le_second_aux2 (N : ℕ) (hN : 1 ≤ N) :
    ((Nat.log 2 N : ℕ) : ℝ) * Real.log 2 ≤ Real.log N := by
  have h1 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 N ≤ N := by exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rwa [Real.log_pow] at h3

lemma sum_log_smooth_le_second_aux3 (w N : ℕ) (hw : 1 ≤ w) (hN : 16 ≤ N) :
    ∑ n ∈ (Icc 1 N).filter (fun j => ∀ p, p.Prime → p ∣ j → p ≤ w), Real.log n ≤
      (Nat.log 2 N : ℝ) * Real.sqrt N * (Real.log 4 * w) +
        4 * N * (Real.log w + 10) / Real.log N * (Real.log w + 10) := by
  refine le_trans (sum_log_smooth_le w N) ?_
  have h1 : ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 (Nat.log 2 N),
        Real.log p *
          (((Icc 1 (N / p ^ i)).filter fun j => ∀ q, q.Prime → q ∣ j → q ≤ w).card : ℝ) ≤
      ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 (Nat.log 2 N),
        (Real.log p * Real.sqrt N +
          4 * N * (Real.log w + 10) / Real.log N * (Real.log p / (p : ℝ) ^ i)) := by
    refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun i _ => ?_
    have pp : p.Prime := (mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast pp.one_lt.le)
    have h2 := card_smooth_div_le w N (p ^ i) hw hN (Nat.one_le_pow _ _ pp.pos)
    push_cast at h2
    calc Real.log p * _ ≤ Real.log p * (Real.sqrt N +
            4 * ((N : ℝ) / (p : ℝ) ^ i) * (Real.log w + 10) / Real.log N) :=
          mul_le_mul_of_nonneg_left h2 hlog
      _ = _ := by ring
  refine le_trans h1 ?_
  have hsplit : ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 (Nat.log 2 N),
        (Real.log p * Real.sqrt N +
          4 * N * (Real.log w + 10) / Real.log N * (Real.log p / (p : ℝ) ^ i)) =
      ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ _i ∈ Icc 1 (Nat.log 2 N),
        Real.log p * Real.sqrt N +
      4 * N * (Real.log w + 10) / Real.log N *
        ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 (Nat.log 2 N),
          Real.log p / (p : ℝ) ^ i := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit]
  have h3 := OMA.Mertens687.theta_le w
  have h4 := sum_log_div_prime_pow_le w (Nat.log 2 N) hw
  have hK : 0 ≤ 4 * (N : ℝ) * (Real.log w + 10) / Real.log N := by
    have : 0 ≤ Real.log w := Real.log_nonneg (by exact_mod_cast hw)
    have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    positivity
  have h5 := mul_le_mul_of_nonneg_left h4 hK
  have h6 : ∑ p ∈ (range (w + 1)).filter Nat.Prime, ∑ _i ∈ Icc 1 (Nat.log 2 N),
      Real.log p * Real.sqrt N ≤ (Nat.log 2 N : ℝ) * Real.sqrt N * (Real.log 4 * w) := by
    simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    have := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg (N : ℝ))
    have h7 := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg (Nat.log 2 N))
    linarith
  linarith

lemma sum_log_smooth_le_second (w N : ℕ) (hw : 2 ≤ w) (hwN : w ^ 4 ≤ N) :
    ∑ n ∈ (Icc 1 N).filter (fun j => ∀ p, p.Prime → p ∣ j → p ≤ w), Real.log n ≤
      2 * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log N +
        4 * N * (Real.log w + 10) ^ 2 / Real.log N := by
  have hN : 16 ≤ N := le_trans (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ w ^ 4 := Nat.pow_le_pow_left hw 4) hwN
  refine le_trans (sum_log_smooth_le_second_aux3 w N (by omega) hN) ?_
  have h1 := sum_log_smooth_le_second_aux1 w N (by omega) hwN
  have h2 := sum_log_smooth_le_second_aux2 N (by omega)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hI : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) * Real.log 2 := by positivity
  have hT : (0 : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hws : (0 : ℝ) ≤ (w : ℝ) * Real.sqrt N := by positivity
  have h3 : ((Nat.log 2 N : ℕ) : ℝ) * Real.log 2 * ((w : ℝ) * Real.sqrt N) ≤
      Real.log N * (N : ℝ) ^ ((3 : ℝ) / 4) := mul_le_mul h2 h1 hws (le_trans hI h2)
  have e1 : (Nat.log 2 N : ℝ) * Real.sqrt N * (Real.log 4 * w) =
      2 * ((Nat.log 2 N : ℝ) * Real.log 2 * ((w : ℝ) * Real.sqrt N)) := by
    rw [hl4]; ring
  have e2 : 4 * (N : ℝ) * (Real.log w + 10) / Real.log N * (Real.log w + 10) =
      4 * N * (Real.log w + 10) ^ 2 / Real.log N := by ring
  rw [e1, e2]
  linarith

-- LEMMA C11
lemma card_smooth_le (w N : ℕ) (hw : 2 ≤ w) (hwN : w ^ 4 ≤ N) :
    (((Icc 1 N).filter fun j => ∀ p, p.Prime → p ∣ j → p ≤ w).card : ℝ) ≤
      2048 * N * (Real.log w) ^ 2 / (Real.log N) ^ 2 + 7 * (N : ℝ) ^ ((3 : ℝ) / 4) := by
  have hN : 16 ≤ N := le_trans (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ w ^ 4 := Nat.pow_le_pow_left hw 4) hwN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  set L := Real.log (N : ℝ) with hLdef
  set T := (N : ℝ) ^ ((3 : ℝ) / 4) with hTdef
  set c := Real.log (w : ℝ) + 10 with hcdef
  have h1 := card_smooth_mul_log_le w N (by omega)
  have h2 := sum_log_smooth_le_second w N hw hwN
  have hT0 : 0 ≤ T := Real.rpow_nonneg (by linarith) _
  have hsq : Real.sqrt N ≤ T := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hlw : Real.log 2 ≤ Real.log w :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hw)
  have hlw0 : 0 < Real.log (w : ℝ) := by
    have := Real.log_two_gt_d9; linarith
  have hc0 : 0 ≤ c := by linarith
  have hc16 : c ≤ 16 * Real.log w := by
    have := Real.log_two_gt_d9; linarith
  have hc2 : c ^ 2 ≤ 256 * (Real.log w) ^ 2 := by
    have := pow_le_pow_left₀ hc0 hc16 2
    nlinarith
  have hX : (((Icc 1 N).filter fun j => ∀ p, p.Prime → p ∣ j → p ≤ w).card : ℝ) - Real.sqrt N ≤
      4 * T + 8 * N * c ^ 2 / L ^ 2 := by
    have hL2 : 0 < L / 2 := by linarith
    refine le_of_mul_le_mul_right ?_ hL2
    have e : (4 * T + 8 * N * c ^ 2 / L ^ 2) * (L / 2) = 2 * T * L + 4 * N * c ^ 2 / L := by
      field_simp
      ring
    rw [e]
    linarith
  have h8 : 8 * (N : ℝ) * c ^ 2 / L ^ 2 ≤ 2048 * N * (Real.log w) ^ 2 / L ^ 2 := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith
  linarith

/- ### Part D: assembly -/

lemma exists_shift_rough_card_le_explicit (x w N : ℕ) (hw : 2 ≤ w) (hwx : w ≤ x)
    (hxN : x ≤ N) (hwN : w ^ 4 ≤ N) :
    ∃ M : ℕ,
      (((Icc (M + 1) (M + N)).filter fun n => ∀ p ≤ x, p.Prime → ¬ p ∣ n).card : ℝ) ≤
        (Real.log w)⁻¹ *
          (2048 * N * (Real.log w) ^ 2 / (Real.log N) ^ 2 + 7 * (N : ℝ) ^ ((3 : ℝ) / 4)
            + 3 * N * (1 + Real.log ((N : ℝ) / x)) / Real.log x + 2 * N / Real.sqrt x) := by
  obtain ⟨M, hM⟩ := exists_shift_rough_card_le x w N hwx
  refine ⟨M, hM.trans ?_⟩
  have hV := OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1.eulerProd_le_inv_log hw
  have hK : (((Icc 1 N).filter fun j => ∀ p, p.Prime → w < p → p ≤ x → ¬ p ∣ j).card : ℝ) ≤
      (((Icc 1 N).filter fun j => ∀ p, p.Prime → p ∣ j → p ≤ w).card : ℝ) +
      (((Icc 1 N).filter fun j => ∃ q, q.Prime ∧ x < q ∧ q ∣ j).card : ℝ) := by
    exact_mod_cast card_K_le x w N
  have hS := card_smooth_le w N hw hwN
  have hB := card_bigprime_le x N (by omega) hxN
  have hlw : 0 ≤ (Real.log w)⁻¹ := inv_nonneg.mpr (Real.log_natCast_nonneg w)
  calc _ ≤ (Real.log w)⁻¹ *
        (((Icc 1 N).filter fun j => ∀ p, p.Prime → w < p → p ≤ x → ¬ p ∣ j).card : ℝ) :=
        mul_le_mul_of_nonneg_right hV (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hlw

lemma eventually_exists_shift (c : ℝ) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ x : ℕ in atTop, ∃ M : ℕ,
      (((Icc (M + 1) (M + ⌈(x : ℝ) ^ (1 + ε)⌉₊)).filter
          fun n => ∀ p ≤ x, p.Prime → ¬ p ∣ n).card : ℝ) <
        c * (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) / Real.log x := by
  have hα : 0 < min (1 / 4 : ℝ) (c / 8192) := lt_min (by norm_num) (by positivity)
  have hα4 : min (1 / 4 : ℝ) (c / 8192) ≤ 1 / 4 := min_le_left _ _
  have hαc : min (1 / 4 : ℝ) (c / 8192) ≤ c / 8192 := min_le_right _ _
  generalize min (1 / 4 : ℝ) (c / 8192) = α at hα hα4 hαc
  have hε : 0 < min (1 / 2 : ℝ) (c * α / 24) := lt_min (by norm_num) (by positivity)
  have hε1 : min (1 / 2 : ℝ) (c * α / 24) < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hεc : min (1 / 2 : ℝ) (c * α / 24) ≤ c * α / 24 := min_le_right _ _
  generalize min (1 / 2 : ℝ) (c * α / 24) = ε at hε hε1 hεc
  refine ⟨ε, hε, hε1, ?_⟩
  filter_upwards [eventually_floor_rpow α hα hα4,
    eventually_small_terms α (c / 4) hα (by positivity), eventually_ge_atTop 2]
    with x hfl hsmall hx2
  obtain ⟨hw2, hw4, hlw1, hlw2⟩ := hfl
  obtain ⟨hxN, hLNX⟩ := ceil_rpow_facts ε hε x hx2
  have hwx : ⌊(x : ℝ) ^ α⌋₊ ≤ x := le_trans (Nat.le_self_pow (by norm_num) _) hw4
  obtain ⟨M, hM⟩ := exists_shift_rough_card_le_explicit x ⌊(x : ℝ) ^ α⌋₊
    ⌈(x : ℝ) ^ (1 + ε)⌉₊ hw2 hwx hxN (hw4.trans hxN)
  refine ⟨M, lt_of_le_of_lt hM ?_⟩
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hNR : (x : ℝ) ≤ (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := by exact_mod_cast hxN
  have hNpos : (0 : ℝ) < (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := by linarith
  have hlN : Real.log x ≤ Real.log (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := Real.log_le_log hx0 hNR
  have hs4 : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hx0 _
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hT : ((⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ)) ^ ((3 : ℝ) / 4) ≤
      (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [le_div_iff₀ hs4]
    have h1 : (x : ℝ) ^ ((1 : ℝ) / 4) ≤ ((⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow hx0.le hNR (by norm_num)
    have h2 : ((⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ)) ^ ((3 : ℝ) / 4) *
        ((⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ)) ^ ((1 : ℝ) / 4) = (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := by
      rw [← Real.rpow_add hNpos]
      norm_num
    calc _ ≤ ((⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ)) ^ ((3 : ℝ) / 4) *
          ((⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ)) ^ ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hNpos.le _)
      _ = _ := h2
  exact explicit_bound_lt c α ε (Real.log x) (Real.log (⌊(x : ℝ) ^ α⌋₊ : ℝ))
    (Real.log (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ)) (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) _ _ _ _ hc hα hαc hε hεc
    hlx hlw1 hlw2 hlN hNpos hs4 hsx hT hLNX hsmall

/-- The short-interval rough-number lower bound (step `R1.H2.R1.H2` of part iii) is false. -/
theorem not_roughLB : ¬ OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1.H2 := by
  rintro ⟨c, hc, h⟩
  obtain ⟨ε, hε0, hε1, hev⟩ := eventually_exists_shift c hc
  obtain ⟨x, hx1, M, hM⟩ := ((h ε hε0 hε1).and hev).exists
  exact absurd (hx1 M) (not_le.mpr hM)

end E687Rankin

/- ## The chain: the sibling hypotheses, then the disproof -/

/-- Step `R1.H2.R1.H2.R1.H2` (one-sided minor-arc bound) is false: it needs only the merged
Mertens step. -/
theorem E687Rankin.not_minorArc : ¬ OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.H2 :=
  fun h => E687Rankin.not_roughLB
    (OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.main OMA.Mertens687.mertens_lower h)

-- LEMMA E1 (sibling step R1.H2.R1.H2.R1.H2.R1.H1; open PR 7570 by @Salofe, CI green)
lemma E687Rankin.l2_H1 : OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1.H1 := by
  sorry

-- LEMMA E2 (sibling step R1.H2.R1.H2.R1.H2.R1.H2.R1.H1; open PR 3541 by @santiemanuel, CI green)
lemma E687Rankin.crt_H1 :
    OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1_H2_R1.H1 := by
  sorry

/-- Step `R1.H2.R1.H2.R1.H2.R1.H2` (bad-set multiplicity) is false, given the L2 step. -/
theorem E687Rankin.not_multiplicity :
    ¬ OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1.H2 :=
  fun h => E687Rankin.not_minorArc
    (OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1.main E687Rankin.l2_H1 h)

theorem OMA.disproof : ¬ OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1_H2_R1.H2 :=
  fun h => E687Rankin.not_multiplicity
    (OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1_H2_R1.main E687Rankin.crt_H1 h)
