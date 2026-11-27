import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1
import Mathlib

-- Credit: @LordMike
-- Disproof of step H2 of reduction Erdos687.erdos_687.parts.iii.R1 (Buchstab large-prime tail
-- bound). The constant c is chosen before eps, and the bound fails for small eps.
--
-- With the fundamental lemma (step R1.H1, proved by @santiemanuel, copied below) the tail bound
-- gives at least (c/2) * y * prod_{p <= x} (1 - 1/p) survivors in [1, y], y = ceil(x^(1+eps)),
-- for every residue system and every eps > 0. The first step of the Erdos-Rankin construction
-- contradicts this: put the block at a point divisible by every prime in (w, x], w = x^alpha,
-- and average over the residues modulo the primes <= w. The survivors are w-smooth numbers
-- (at most 2048 alpha^2 N + 7 N^(3/4)) and multiples of primes > x (at most about 3 eps N), and
-- the averaging multiplies by prod_{p <= w} (1 - 1/p) <= 1 / log w. With alpha ~ c / 8192 and
-- eps ~ c alpha / 24 the count drops below c N / log x.
--
-- Copied unchanged, with credit: the proof of step R1.H1 (@santiemanuel) in section R1H1, and
-- the proof of step R1.H2.R1.H2.R1.H1 (@ivillar) in namespace OMA.Mertens687. The lemmas
-- buchstab_identity, chebyshev_eulerProd_ratio and eulerProd_le_inv_log of the imported
-- reductions are by @santiemanuel.

section R1H1

open Filter Finset Real

private lemma alternating_choose_sum {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) =
      (-1 : ℝ) ^ m * ((n - 1).choose m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hpas : n.choose (m + 1) = (n - 1).choose m + (n - 1).choose (m + 1) := by
      have h := Nat.choose_succ_succ (n - 1) m
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hn] at h
      exact h
    have hpas_r : (n.choose (m + 1) : ℝ) = ((n - 1).choose m : ℝ) + ((n - 1).choose (m + 1) : ℝ) := by
      exact_mod_cast hpas
    rw [hpas_r, pow_succ (-1 : ℝ) m]
    ring

private lemma alternating_powerset_eq (B : Finset ℕ) (M : ℕ) :
    ∑ D ∈ B.powerset.filter (fun D => D.card ≤ M), (-1 : ℝ) ^ D.card =
      ∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * (B.card.choose j : ℝ) := by
  have hpart : B.powerset.filter (fun D => D.card ≤ M) =
      (Finset.range (M + 1)).biUnion (fun j => B.powersetCard j) := by
    ext D
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
    constructor
    · rintro ⟨hDB, hcard⟩
      exact ⟨D.card, by omega, hDB, rfl⟩
    · rintro ⟨j, hj, hDB, rfl⟩
      exact ⟨hDB, by omega⟩
  have hpw : (Finset.range (M + 1) : Set ℕ).PairwiseDisjoint (fun j => B.powersetCard j) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro D hDi hDj
    have hi := (mem_powersetCard.mp hDi).2
    have hj := (mem_powersetCard.mp hDj).2
    exact hij (hi.symm.trans hj)
  rw [hpart, Finset.sum_biUnion hpw]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconst : ∑ D ∈ B.powersetCard j, (-1 : ℝ) ^ D.card =
      ∑ _D ∈ B.powersetCard j, (-1 : ℝ) ^ j :=
    Finset.sum_congr rfl fun D hD => by rw [(mem_powersetCard.mp hD).2]
  rw [hconst, Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, mul_comm]

private lemma icc_succ_eq_insert {a b : ℕ} (h : a ≤ b + 1) :
    Icc a (b + 1) = insert (b + 1) (Icc a b) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

private def brunPredIco (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (i : ℕ) (D : Finset ℕ) : Prop :=
  ∀ j ∈ Ico 1 i, (D ∩ Q j).card ≤ 2 * b j - 1

private instance instDecidableBrunPredIco (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (i : ℕ) :
    DecidablePred (brunPredIco Q b i) :=
  fun _ => Finset.decidableDforallFinset

private def brunPred (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (r : ℕ) (D : Finset ℕ) : Prop :=
  ∀ i ∈ Icc 1 r, (D ∩ Q i).card ≤ 2 * b i - 1

private instance instDecidableBrunPred (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (r : ℕ) :
    DecidablePred (brunPred Q b r) :=
  fun _ => Finset.decidableDforallFinset

/-- Brun's combinatorial lower bound: for pairwise disjoint blocks `P 1, ..., P r` and
nondecreasing depths `1 ≤ b 1 ≤ b 2 ≤ ...`, restricting inclusion-exclusion to sets with
`|D ∩ (P 1 ∪ ⋯ ∪ P i)| ≤ 2 * b i - 1` yields a pointwise lower bound on `1_{B = ∅}`. -/
private lemma brun_pointwise_lower (P : ℕ → Finset ℕ) (b : ℕ → ℕ)
    (hb1 : 1 ≤ b 1) (hb_mono : ∀ i, 1 ≤ i → b i ≤ b (i + 1))
    (hdisj : ∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → Disjoint (P i) (P j)) :
    ∀ (r : ℕ) (B : Finset ℕ), B ⊆ (Icc 1 r).biUnion P →
      ∑ D ∈ B.powerset.filter (brunPred (fun k => (Icc 1 k).biUnion P) b r),
        (-1 : ℝ) ^ D.card ≤ if B = ∅ then 1 else 0 := by
  have hb_ge1 : ∀ k, 1 ≤ k → 1 ≤ b k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hb1
    | succ m hm ih => exact ih.trans (hb_mono m hm)
  intro r
  induction r with
  | zero =>
    intro B hB
    have hBe : B = ∅ := by
      rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.biUnion_empty] at hB
      exact Finset.subset_empty.mp hB
    subst hBe
    have hfilt : (∅ : Finset ℕ).powerset.filter (brunPred (fun k => (Icc 1 k).biUnion P) b 0) = {∅} := by
      ext D
      simp [brunPred]
    rw [hfilt]
    simp
  | succ r ih =>
    intro B hB
    let Q : ℕ → Finset ℕ := fun k => (Icc 1 k).biUnion P
    have hQsucc : Q (r + 1) = Q r ∪ P (r + 1) := by
      dsimp [Q]
      rw [icc_succ_eq_insert (by omega : 1 ≤ r + 1), Finset.biUnion_insert,
        Finset.union_comm]
    have hQdisj : Disjoint (Q r) (P (r + 1)) := by
      rw [Finset.disjoint_left]
      intro x hxQ hxP
      rw [mem_biUnion] at hxQ
      obtain ⟨j, hj, hxj⟩ := hxQ
      have hj_mem := mem_Icc.mp hj
      exact Finset.disjoint_left.mp (hdisj j (r + 1) hj_mem.1 (by omega) (by omega)) hxj hxP
    let B' := B ∩ Q r
    let B₁ := B ∩ P (r + 1)
    have hB_union : B = B' ∪ B₁ := by
      ext x
      simp only [B', B₁, mem_union, mem_inter]
      constructor
      · intro hxB
        have hxQ := hB hxB
        change x ∈ Q (r + 1) at hxQ
        rw [hQsucc, mem_union] at hxQ
        rcases hxQ with h | h
        · exact Or.inl ⟨hxB, h⟩
        · exact Or.inr ⟨hxB, h⟩
      · rintro (⟨hxB, _⟩ | ⟨hxB, _⟩) <;> exact hxB
    by_cases hB₁_empty : B₁ = ∅
    · have hBeq : B = B' := by rw [hB_union, hB₁_empty, Finset.union_empty]
      have hB_sub : B ⊆ Q r := by
        rw [hBeq]
        exact Finset.inter_subset_right
      have hfilt_eq :
          B.powerset.filter (brunPred Q b (r + 1)) =
          B.powerset.filter (brunPred Q b r) := by
        ext D
        simp only [mem_filter, mem_powerset, brunPred]
        constructor
        · rintro ⟨hDB, hall⟩
          exact ⟨hDB, fun i hi => hall i (mem_Icc.mpr ⟨(mem_Icc.mp hi).1, (mem_Icc.mp hi).2.trans (Nat.le_succ r)⟩)⟩
        · rintro ⟨hDB, hall⟩
          refine ⟨hDB, fun i hi => ?_⟩
          have hi' := mem_Icc.mp hi
          by_cases hir : i ≤ r
          · exact hall i (mem_Icc.mpr ⟨hi'.1, hir⟩)
          · have hieq : i = r + 1 := by omega
            subst hieq
            have hDsub : D ⊆ Q r := hDB.trans hB_sub
            have hDQ : D ∩ Q (r + 1) = D := by
              rw [hQsucc]
              exact Finset.inter_eq_left.mpr (hDsub.trans Finset.subset_union_left)
            rw [hDQ]
            by_cases hr0 : r = 0
            · subst hr0
              have hDe : D = ∅ := by
                dsimp [Q] at hDsub
                rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.biUnion_empty] at hDsub
                exact Finset.subset_empty.mp hDsub
              subst hDe
              simp only [Finset.card_empty]
              exact Nat.zero_le _
            · have hr1 : 1 ≤ r := by omega
              have hDr := hall r (mem_Icc.mpr ⟨hr1, le_rfl⟩)
              rw [Finset.inter_eq_left.mpr hDsub] at hDr
              have hbm := hb_mono r hr1
              omega
      change ∑ D ∈ B.powerset.filter (brunPred Q b (r + 1)),
          (-1 : ℝ) ^ D.card ≤ _
      rw [hfilt_eq]
      exact ih B hB_sub
    · have hB₁_ne : B₁.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB₁_empty
      have hB_ne : B ≠ ∅ := by
        intro h
        obtain ⟨x, hx⟩ := hB₁_ne
        simp [B₁, h] at hx
      rw [if_neg hB_ne]
      let M := 2 * b (r + 1) - 1
      have hM_odd : (-1 : ℝ) ^ M = -1 := by
        have hbr1 : 1 ≤ b (r + 1) := hb_ge1 (r + 1) (by omega)
        have hMeq : M = 2 * (b (r + 1) - 1) + 1 := by dsimp [M]; omega
        rw [hMeq, pow_succ, pow_mul]
        norm_num
      let F_prev := B'.powerset.filter (brunPred Q b r)
      let F_full := B.powerset.filter (brunPred Q b (r + 1))
      let S_sig := F_prev.sigma fun D' => B₁.powerset.filter (fun D₁ => D₁.card ≤ M - D'.card)
      have hD'_le_M : ∀ D' ∈ F_prev, D'.card ≤ M := by
        intro D' hD'
        have hD'sub : D' ⊆ Q r := (mem_powerset.mp (mem_filter.mp hD').1).trans Finset.inter_subset_right
        by_cases hr0 : r = 0
        · subst hr0
          dsimp [Q] at hD'sub
          rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.biUnion_empty] at hD'sub
          rw [Finset.subset_empty.mp hD'sub]
          simp [M]
        · have hr1 : 1 ≤ r := by omega
          have h := (mem_filter.mp hD').2 r (mem_Icc.mpr ⟨hr1, le_rfl⟩)
          rw [Finset.inter_eq_left.mpr hD'sub] at h
          have hbm := hb_mono r hr1
          dsimp [M]
          omega
      have hbij : ∑ D ∈ F_full, (-1 : ℝ) ^ D.card =
          ∑ x ∈ S_sig, (-1 : ℝ) ^ (x.1 ∪ x.2).card := by
        refine (Finset.sum_nbij (fun x => x.1 ∪ x.2) ?_ ?_ ?_ ?_).symm
        · intro x hx
          rw [mem_sigma] at hx
          obtain ⟨hD', hD₁⟩ := hx
          have hD'p := mem_filter.mp hD'
          have hD₁p := mem_filter.mp hD₁
          have hD'B' : x.1 ⊆ B' := mem_powerset.mp hD'p.1
          have hD₁B₁ : x.2 ⊆ B₁ := mem_powerset.mp hD₁p.1
          have hdisj_x : Disjoint x.1 x.2 :=
            Disjoint.mono (hD'B'.trans Finset.inter_subset_right)
              (hD₁B₁.trans Finset.inter_subset_right) hQdisj
          refine mem_filter.mpr ⟨mem_powerset.mpr ?_, fun i hi => ?_⟩
          · rw [hB_union]
            exact Finset.union_subset_union hD'B' hD₁B₁
          · have hi' := mem_Icc.mp hi
            by_cases hir : i ≤ r
            · have hQi_sub : Q i ⊆ Q r :=
                Finset.biUnion_subset_biUnion_of_subset_left P
                  (Finset.Icc_subset_Icc_right hir)
              have hdisj_2 : Disjoint x.2 (Q i) :=
                (Disjoint.mono (hD₁B₁.trans Finset.inter_subset_right) hQi_sub hQdisj.symm)
              have hinter : (x.1 ∪ x.2) ∩ Q i = x.1 ∩ Q i := by
                rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdisj_2,
                  Finset.union_empty]
              rw [hinter]
              exact hD'p.2 i (mem_Icc.mpr ⟨hi'.1, hir⟩)
            · have hieq : i = r + 1 := by omega
              subst hieq
              have hsub_Q : x.1 ∪ x.2 ⊆ Q (r + 1) := by
                rw [hQsucc]
                exact Finset.union_subset_union (hD'B'.trans Finset.inter_subset_right)
                  (hD₁B₁.trans Finset.inter_subset_right)
              rw [Finset.inter_eq_left.mpr hsub_Q, Finset.card_union_of_disjoint hdisj_x]
              have h1 := hD'_le_M x.1 hD'
              have h2 : x.2.card ≤ M - x.1.card := hD₁p.2
              change x.1.card + x.2.card ≤ M
              omega
        · intro x hx y hy hxy
          rw [mem_coe, mem_sigma] at hx hy
          have hx1 : x.1 ⊆ Q r := (mem_powerset.mp (mem_filter.mp hx.1).1).trans Finset.inter_subset_right
          have hx2 : x.2 ⊆ P (r + 1) := (mem_powerset.mp (mem_filter.mp hx.2).1).trans Finset.inter_subset_right
          have hy1 : y.1 ⊆ Q r := (mem_powerset.mp (mem_filter.mp hy.1).1).trans Finset.inter_subset_right
          have hy2 : y.2 ⊆ P (r + 1) := (mem_powerset.mp (mem_filter.mp hy.2).1).trans Finset.inter_subset_right
          have heq1 : x.1 = y.1 := by
            have := congrArg (· ∩ Q r) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx1,
              Finset.inter_eq_left.mpr hy1,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx2 hQdisj.symm),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy2 hQdisj.symm),
              Finset.union_empty] using this
          have heq2 : x.2 = y.2 := by
            have := congrArg (· ∩ P (r + 1)) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx2,
              Finset.inter_eq_left.mpr hy2,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx1 hQdisj),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy1 hQdisj),
              Finset.empty_union] using this
          exact Sigma.ext heq1 (heq_of_eq heq2)
        · intro D hD
          rw [mem_coe] at hD
          have hDp := mem_filter.mp hD
          have hDB : D ⊆ B := mem_powerset.mp hDp.1
          let D' := D ∩ Q r
          let D₁ := D ∩ P (r + 1)
          have hD_eq : D' ∪ D₁ = D := by
            ext z
            simp only [D', D₁, mem_union, mem_inter]
            constructor
            · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
            · intro hz
              have hzQ : z ∈ Q (r + 1) := hB (hDB hz)
              rw [hQsucc, mem_union] at hzQ
              rcases hzQ with h | h
              · exact Or.inl ⟨hz, h⟩
              · exact Or.inr ⟨hz, h⟩
          have hD'mem : D' ∈ F_prev := by
            refine mem_filter.mpr ⟨mem_powerset.mpr (Finset.inter_subset_inter_right hDB), fun i hi => ?_⟩
            have hi' := mem_Icc.mp hi
            have hQi_sub : Q i ⊆ Q r :=
              Finset.biUnion_subset_biUnion_of_subset_left P (Finset.Icc_subset_Icc_right hi'.2)
            have hinter : D' ∩ Q i = D ∩ Q i := by
              dsimp [D']
              rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hQi_sub]
            rw [hinter]
            exact hDp.2 i (mem_Icc.mpr ⟨hi'.1, hi'.2.trans (Nat.le_succ r)⟩)
          have hD₁mem : D₁ ∈ B₁.powerset.filter (fun E => E.card ≤ M - D'.card) := by
            refine mem_filter.mpr ⟨mem_powerset.mpr (Finset.inter_subset_inter_right hDB), ?_⟩
            have hdisj_D : Disjoint D' D₁ :=
              Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hQdisj
            have htot := hDp.2 (r + 1) (mem_Icc.mpr ⟨by omega, le_rfl⟩)
            have hDQ : D ∩ Q (r + 1) = D := Finset.inter_eq_left.mpr (hDB.trans hB)
            rw [hDQ, ← hD_eq, Finset.card_union_of_disjoint hdisj_D] at htot
            change D₁.card ≤ M - D'.card
            dsimp [M]
            omega
          exact ⟨⟨D', D₁⟩, mem_coe.mpr (mem_sigma.mpr ⟨hD'mem, hD₁mem⟩), hD_eq⟩
        · intro _ _
          rfl
      change ∑ D ∈ F_full, (-1 : ℝ) ^ D.card ≤ 0
      rw [hbij, Finset.sum_sigma]
      refine Finset.sum_nonpos fun D' hD' => ?_
      have hD'sub : D' ⊆ Q r := (mem_powerset.mp (mem_filter.mp hD').1).trans Finset.inter_subset_right
      have hfactor : ∑ D₁ ∈ B₁.powerset.filter (fun E => E.card ≤ M - D'.card),
          (-1 : ℝ) ^ (D' ∪ D₁).card =
          (-1 : ℝ) ^ D'.card *
            ∑ D₁ ∈ B₁.powerset.filter (fun E => E.card ≤ M - D'.card), (-1 : ℝ) ^ D₁.card := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun D₁ hD₁ => ?_
        have hD₁sub : D₁ ⊆ P (r + 1) :=
          (mem_powerset.mp (mem_filter.mp hD₁).1).trans Finset.inter_subset_right
        have hdisj_D : Disjoint D' D₁ := Disjoint.mono hD'sub hD₁sub hQdisj
        rw [Finset.card_union_of_disjoint hdisj_D, pow_add]
      rw [hfactor, alternating_powerset_eq,
        alternating_choose_sum (Finset.card_pos.mpr hB₁_ne), ← mul_assoc, ← pow_add,
        Nat.add_sub_of_le (hD'_le_M D' hD'), hM_odd]
      have hnn : (0 : ℝ) ≤ ((B₁.card - 1).choose (M - D'.card) : ℝ) := Nat.cast_nonneg _
      linarith

/-- Counting elements of `[1, y]` in a fixed residue class modulo `d > 0` has error at most `1`. -/
private lemma count_modEq_Icc_error {d : ℕ} (hd : 0 < d) (k y : ℕ) :
    |(((Icc 1 y).filter fun m => m ≡ k [MOD d]).card : ℝ) - (y : ℝ) / (d : ℝ)| ≤ 1 := by
  let r := k % d
  let r' := if r = 0 then d else r
  have hr_lt : r < d := Nat.mod_lt k hd
  have hr'1 : 1 ≤ r' := by
    dsimp [r', r]
    split_ifs <;> omega
  have hr'd : r' ≤ d := by
    dsimp [r', r]
    split_ifs <;> omega
  have hr'mod : r' % d = r := by
    dsimp [r', r]
    split_ifs with h
    · rw [Nat.mod_self, h]
    · exact Nat.mod_eq_of_lt hr_lt
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  by_cases hyr : y < r'
  · have hemp : ((Icc 1 y).filter fun m => m ≡ k [MOD d]) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      rw [mem_filter, mem_Icc] at hm
      have hmod : m % d = r := hm.2
      have hm_lt : m < d := by omega
      have hmr : m = r := by rwa [Nat.mod_eq_of_lt hm_lt] at hmod
      dsimp [r'] at hyr
      split_ifs at hyr with h0
      · omega
      · omega
    rw [hemp, Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (by positivity)]
    rw [div_le_one hd_pos]
    exact_mod_cast (show y ≤ d by omega)
  · push Not at hyr
    let q := (y - r') / d
    have hcard : ((Icc 1 y).filter fun m => m ≡ k [MOD d]).card = q + 1 := by
      have himg : ((Icc 1 y).filter fun m => m ≡ k [MOD d]) =
          (Finset.range (q + 1)).image (fun j => j * d + r') := by
        ext m
        simp only [mem_filter, mem_Icc, mem_image, mem_range]
        constructor
        · rintro ⟨⟨hm1, hmy⟩, hmod⟩
          have hmd : m % d = r := hmod
          have hmr' : r' ≤ m := by
            by_contra hlt
            push Not at hlt
            have hm_lt_d : m < d := by omega
            have := Nat.mod_eq_of_lt hm_lt_d
            dsimp [r'] at hlt
            split_ifs at hlt with h0 <;> omega
          have hdvd : d ∣ m - r' := by
            have h1 : m ≡ r' [MOD d] := hmod.trans (Nat.ModEq.symm (by
              change r' % d = k % d
              exact hr'mod))
            exact (Nat.modEq_iff_dvd' hmr').mp h1.symm
          obtain ⟨j, hj⟩ := hdvd
          have hmeq : j * d + r' = m := by
            rw [Nat.mul_comm]
            omega
          refine ⟨j, ?_, hmeq⟩
          have hj_le : j ≤ q := by
            dsimp [q]
            exact (Nat.le_div_iff_mul_le hd).mpr (by omega)
          omega
        · rintro ⟨j, hj, rfl⟩
          have hj_le : j ≤ q := by omega
          have hmul : j * d ≤ y - r' := by
            have hqmul : q * d ≤ y - r' := Nat.div_mul_le_self (y - r') d
            exact (Nat.mul_le_mul_right d hj_le).trans hqmul
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          change (j * d + r') % d = k % d
          rw [Nat.mul_add_mod_self_right, hr'mod]
      rw [himg, Finset.card_image_of_injective _ (fun j₁ j₂ h => by
        have := Nat.add_right_cancel h
        exact Nat.eq_of_mul_eq_mul_right hd this), Finset.card_range]
    rw [hcard, abs_le]
    have hlo_nat : q * d ≤ y := (Nat.div_mul_le_self (y - r') d).trans (Nat.sub_le y r')
    have hhi_nat : y < (q + 2) * d := by
      have hlt : y - r' < (q + 1) * d := by
        dsimp [q]
        rw [Nat.add_mul, Nat.one_mul]
        have hdm : ((y - r') / d) * d + (y - r') % d = y - r' := by
          rw [Nat.mul_comm]
          exact Nat.div_add_mod (y - r') d
        have := Nat.mod_lt (y - r') hd
        omega
      rw [show q + 2 = (q + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
    have hlo : (q : ℝ) ≤ (y : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hd_pos]
      exact_mod_cast hlo_nat
    have hhi : (y : ℝ) / (d : ℝ) ≤ (q : ℝ) + 2 := by
      rw [div_le_iff₀ hd_pos]
      have : (y : ℝ) < ((q + 2 : ℕ) : ℝ) * (d : ℝ) := by exact_mod_cast hhi_nat
      push_cast at this
      linarith
    push_cast
    constructor <;> linarith

private lemma finset_prod_dvd_of_nat_coprime {D : Finset ℕ} {n : ℕ}
    (hcop : Set.Pairwise (D : Set ℕ) (Function.onFun Nat.Coprime id))
    (hdvd : ∀ p ∈ D, p ∣ n) : (∏ p ∈ D, p) ∣ n := by
  induction D using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    rw [Finset.prod_cons]
    have hcop_s : Set.Pairwise (s : Set ℕ) (Function.onFun Nat.Coprime id) :=
      hcop.mono fun x hx => Finset.mem_coe.mpr (Finset.mem_cons_of_mem (Finset.mem_coe.mp hx))
    have hs_dvd : (∏ p ∈ s, p) ∣ n := ih hcop_s (fun p hp => hdvd p (Finset.mem_cons_of_mem hp))
    have ha_dvd : a ∣ n := hdvd a (Finset.mem_cons_self a s)
    have ha_cop : Nat.Coprime a (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        hcop (Finset.mem_coe.mpr (Finset.mem_cons_self a s))
          (Finset.mem_coe.mpr (Finset.mem_cons_of_mem hp))
          (fun heq => has (heq ▸ hp))
    exact ha_cop.mul_dvd_of_dvd_of_dvd ha_dvd hs_dvd

/-- Chinese remainder theorem count of simultaneous residue hits in `[1, y]`. -/
private lemma crt_count_sub_div_le_one {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime)
    (a : ℕ → ℕ) (y : ℕ) :
    |(((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) -
      (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹)| ≤ 1 := by
  let d := ∏ p ∈ D, p
  have hd_pos : 0 < d := Finset.prod_pos fun p hp => (hD p hp).pos
  have hs : ∀ p ∈ D, id p ≠ 0 := fun p hp => (hD p hp).ne_zero
  have pp : Set.Pairwise (D : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hD p hp) (hD q hq)).2 hpq
  let k := Nat.chineseRemainderOfFinset a id D hs pp
  have hfilt : ((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]) =
      ((Icc 1 y).filter fun m => m ≡ (k : ℕ) [MOD d]) := by
    ext m
    simp only [mem_filter]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hm
      have hmk : ∀ p ∈ D, m ≡ (k : ℕ) [MOD p] := fun p hp => (hm p hp).trans (k.2 p hp).symm
      rcases le_total (k : ℕ) m with hle | hle
      · apply Nat.ModEq.symm
        apply (Nat.modEq_iff_dvd' hle).mpr
        refine finset_prod_dvd_of_nat_coprime pp fun p hp => ?_
        exact (Nat.modEq_iff_dvd' hle).mp (hmk p hp).symm
      · apply (Nat.modEq_iff_dvd' hle).mpr
        refine finset_prod_dvd_of_nat_coprime pp fun p hp => ?_
        exact (Nat.modEq_iff_dvd' hle).mp (hmk p hp)
    · intro hmd p hp
      have hpd : p ∣ d := Finset.dvd_prod_of_mem id hp
      exact (hmd.of_dvd hpd).trans (k.2 p hp)
  have hprod : (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹) = (y : ℝ) / (d : ℝ) := by
    rw [div_eq_mul_inv]
    congr 1
    dsimp [d]
    rw [Nat.cast_prod, Finset.prod_inv_distrib]
  rw [hfilt, hprod]
  exact count_modEq_Icc_error hd_pos k y

private lemma eulerProd_eq_powerset_sum (S : Finset ℕ) :
    ∏ p ∈ S, (1 - (p : ℝ)⁻¹) =
      ∑ D ∈ S.powerset, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) := by
  have h1 : ∏ p ∈ S, (1 - (p : ℝ)⁻¹) = ∏ p ∈ S, (-(p : ℝ)⁻¹ + 1) :=
    Finset.prod_congr rfl fun _ _ => by ring
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [Finset.prod_const_one, mul_one, Finset.prod_neg]

private lemma eulerProd_pos_finset (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 < ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
  linarith

private lemma eulerProd_ge_inv {z : ℕ} (hz : 1 ≤ z) :
    (z : ℝ)⁻¹ ≤ ∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
  have htele : ∏ n ∈ Icc 2 z, (1 - (n : ℝ)⁻¹) = (z : ℝ)⁻¹ := by
    induction z, hz using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ m + 1), ih]
      have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      have hm1_ne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
      push_cast
      field_simp
      ring
  rw [← htele]
  have hsub : (range (z + 1)).filter Nat.Prime ⊆ Icc 2 z := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    exact mem_Icc.mpr ⟨hp.2.two_le, by omega⟩
  rw [← Finset.prod_sdiff hsub]
  have hle1 : ∏ n ∈ Icc 2 z \ (range (z + 1)).filter Nat.Prime, (1 - (n : ℝ)⁻¹) ≤ 1 := by
    apply Finset.prod_le_one
    · intro n hn
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (mem_Icc.mp (mem_sdiff.mp hn).1).1
      have hinv : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hn2
      linarith
    · intro n hn
      have hn0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      linarith
  have hpos : 0 ≤ ∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) :=
    (eulerProd_pos_finset _ fun _ hp => (mem_filter.mp hp).2).le
  calc
    (∏ n ∈ Icc 2 z \ (range (z + 1)).filter Nat.Prime, (1 - (n : ℝ)⁻¹)) *
        (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))
        ≤ 1 * (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_right hle1 hpos
    _ = _ := one_mul _

private lemma one_sub_inv_inv_le_exp_two {p : ℕ} (hp : 2 ≤ p) :
    (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * (p : ℝ)⁻¹) := by
  set u : ℝ := (p : ℝ)⁻¹
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hu_pos : 0 < u := inv_pos.mpr hp_pos
  have hu_le : u ≤ 1 / 2 := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    simpa [u, one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2
  have h1u_pos : 0 < 1 - u := by linarith
  have hquad : 1 ≤ (1 - u) * (1 + 2 * u) := by nlinarith
  have hexp : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have hmul : 1 ≤ (1 - u) * Real.exp (2 * u) :=
    hquad.trans (mul_le_mul_of_nonneg_left hexp h1u_pos.le)
  rw [inv_eq_one_div, div_le_iff₀ h1u_pos]
  linarith

/-- Rankin's trick bound on the tail of reciprocal products over subsets of size `≥ m`. -/
private lemma brun_tail_bound (Q : Finset ℕ) (m : ℕ) :
    ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹) ≤
      Real.exp (-(m : ℝ) + Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) := by
  have h1 : ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹) ≤
      Real.exp (-(m : ℝ)) *
        ∑ D ∈ Q.powerset, (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) := by
    rw [Finset.mul_sum]
    calc
      ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹)
          ≤ ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card),
              Real.exp (-(m : ℝ)) * (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) := by
        refine Finset.sum_le_sum fun D hD => ?_
        have hmD : (m : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast (mem_filter.mp hD).2
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_nat_mul, mul_one,
          ← mul_assoc, ← Real.exp_add]
        have hexp_ge1 : (1 : ℝ) ≤ Real.exp (-(m : ℝ) + (D.card : ℝ)) :=
          Real.one_le_exp (by linarith)
        have hprod_nn : 0 ≤ ∏ p ∈ D, (p : ℝ)⁻¹ := Finset.prod_nonneg fun _ _ => by positivity
        calc
          ∏ p ∈ D, (p : ℝ)⁻¹ = 1 * ∏ p ∈ D, (p : ℝ)⁻¹ := (one_mul _).symm
          _ ≤ Real.exp (-(m : ℝ) + (D.card : ℝ)) * ∏ p ∈ D, (p : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hexp_ge1 hprod_nn
      _ ≤ ∑ D ∈ Q.powerset, Real.exp (-(m : ℝ)) * (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => ?_
        positivity
  have h2 : ∑ D ∈ Q.powerset, (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) =
      ∏ p ∈ Q, (1 + Real.exp 1 * (p : ℝ)⁻¹) := by
    have hadd := Finset.prod_add (fun p : ℕ => Real.exp 1 * (p : ℝ)⁻¹) (fun _ => (1 : ℝ)) Q
    have hcomm : ∏ p ∈ Q, (1 + Real.exp 1 * (p : ℝ)⁻¹) =
        ∏ p ∈ Q, (Real.exp 1 * (p : ℝ)⁻¹ + 1) :=
      Finset.prod_congr rfl fun _ _ => add_comm _ _
    rw [hcomm, hadd]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [Finset.prod_const_one, mul_one]
  have h3 : ∏ p ∈ Q, (1 + Real.exp 1 * (p : ℝ)⁻¹) ≤
      Real.exp (Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) := by
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p _; positivity
    · intro p _; linarith [Real.add_one_le_exp (Real.exp 1 * (p : ℝ)⁻¹)]
  calc
    ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹)
        ≤ Real.exp (-(m : ℝ)) * Real.exp (Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) :=
      h1.trans (mul_le_mul_of_nonneg_left (h2.le.trans h3) (by positivity))
    _ = Real.exp (-(m : ℝ) + Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) := (Real.exp_add _ _).symm

/-- Distinct finite sets of primes have distinct products. -/
private lemma prime_finset_prod_injOn (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p) (P.powerset : Set (Finset ℕ)) := by
  intro D₁ hD₁ D₂ hD₂ heq
  have hD₁p : ∀ p ∈ D₁, p.Prime := fun p hp => hP p (mem_powerset.mp (mem_coe.mp hD₁) hp)
  have hD₂p : ∀ p ∈ D₂, p.Prime := fun p hp => hP p (mem_powerset.mp (mem_coe.mp hD₂) hp)
  dsimp only at heq
  ext p
  constructor
  · intro hp
    have hdvd : p ∣ ∏ q ∈ D₂, q := by
      rw [← heq]
      exact Finset.dvd_prod_of_mem id hp
    obtain ⟨q, hq, hpq⟩ := ((hD₁p p hp).prime.dvd_finsetProd_iff id).mp hdvd
    have hpeq : p = q := ((hD₂p q hq).eq_one_or_self_of_dvd p hpq).resolve_left (hD₁p p hp).ne_one
    rwa [hpeq]
  · intro hp
    have hdvd : p ∣ ∏ q ∈ D₁, q := by
      rw [heq]
      exact Finset.dvd_prod_of_mem id hp
    obtain ⟨q, hq, hpq⟩ := ((hD₂p p hp).prime.dvd_finsetProd_iff id).mp hdvd
    have hpeq : p = q := ((hD₁p q hq).eq_one_or_self_of_dvd p hpq).resolve_left (hD₂p p hp).ne_one
    rwa [hpeq]

/-- Summation by parts bound for Brun's dyadic block exponents. -/
private lemma brun_dyadic_weight_bound (b K : ℕ) :
    ∀ r : ℕ, 1 ≤ r →
      ((2 * b + 2 * K * r : ℝ) / (2 : ℝ) ^ (r - 1)) +
        ∑ i ∈ Icc 1 (r - 1), ((2 * b + 2 * K * i : ℝ) / (2 : ℝ) ^ i) =
      (2 * b + 4 * K : ℝ) - (2 * K : ℝ) / (2 : ℝ) ^ (r - 1) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    simp
    ring
  | succ m hm ih =>
    have hm1 : 1 ≤ m := hm
    have hsub : m + 1 - 1 = m := by omega
    rw [hsub]
    have hIcc : Icc 1 m = insert m (Icc 1 (m - 1)) := by
      ext i
      simp only [mem_Icc, mem_insert]
      omega
    have hnotmem : m ∉ Icc 1 (m - 1) := by
      simp only [mem_Icc]
      omega
    rw [hIcc, Finset.sum_insert hnotmem]
    have hpow : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hm1]
    have hsum_eq : ∑ i ∈ Icc 1 (m - 1), ((2 * b + 2 * K * i : ℝ) / (2 : ℝ) ^ i) =
        (2 * b + 4 * K : ℝ) - (2 * K : ℝ) / (2 : ℝ) ^ (m - 1) -
          ((2 * b + 2 * K * m : ℝ) / (2 : ℝ) ^ (m - 1)) := by
      linarith
    rw [hsum_eq, hpow]
    have h2m : (2 : ℝ) ^ (m - 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private lemma geom_half_sum_le_one (r : ℕ) :
    ∑ i ∈ Icc 1 r, ((1 / 2 : ℝ) ^ i) ≤ 1 := by
  have heq : ∀ n : ℕ, ∑ i ∈ Icc 1 n, ((1 / 2 : ℝ) ^ i) = 1 - (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih, pow_succ]
      ring
  rw [heq r]
  have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ r := by positivity
  linarith

private lemma pow_four_div_le_exp {x : ℝ} (hx : 0 ≤ x) :
    x ^ 4 / 256 ≤ Real.exp x := by
  have h1 : x / 4 ≤ 1 + x / 4 := by linarith
  have h2 : 1 + x / 4 ≤ Real.exp (x / 4) := by linarith [Real.add_one_le_exp (x / 4)]
  have h3 : (x / 4) ^ 4 ≤ (Real.exp (x / 4)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (h1.trans h2) 4
  rw [← Real.exp_nat_mul] at h3
  have hexp : (4 : ℕ) * (x / 4) = x := by push_cast; ring
  rw [hexp] at h3
  have hpow : (x / 4) ^ 4 = x ^ 4 / 256 := by ring
  rwa [hpow] at h3

/-- Reciprocal prime sum over `(cut, z]` for Brun's doubly-exponential cutoff `cut i`. -/
private lemma brun_block_recip_sum_le {z i : ℕ} (hz : 16 ≤ z) (hi : 1 ≤ i) :
    let L := Nat.log 2 z + 1
    let c := min z (2 ^ (L / 2 ^ i))
    ∑ q ∈ (Ioc c z).filter Nat.Prime, (q : ℝ)⁻¹ ≤ 18 + 2 * (i : ℝ) := by
  intro L c
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hL_ge5 : 5 ≤ L := by
    dsimp [L]
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by omega : 2 ^ 4 ≤ z)
    omega
  have hc_eq : c = 2 ^ (L / 2 ^ i) := by
    dsimp [c]
    apply min_eq_right
    have hdiv : L / 2 ^ i ≤ L - 1 := by
      have h2i : 2 ≤ 2 ^ i := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      have hq : L / 2 ^ i ≤ L / 2 := Nat.div_le_div_left h2i (by norm_num)
      omega
    have h1 : 2 ^ (L / 2 ^ i) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) hdiv
    have h2 : 2 ^ (L - 1) ≤ z := by
      have hsub : L - 1 = Nat.log 2 z := Nat.add_sub_cancel _ 1
      rw [hsub]
      exact Nat.pow_log_le_self 2 (by omega)
    exact h1.trans h2
  have hc_le_z : c ≤ z := min_le_left _ _
  by_cases hc10 : 10 ≤ c
  · have hbase := OMA.R_Erdos687_erdos_687_parts_iii_R1.sum_prime_inv_Ioc_le hc10 hc_le_z
    have hlogc : Nat.log 2 c = L / 2 ^ i := by
      rw [hc_eq, Nat.log_pow (by norm_num : 1 < 2)]
    have hlogc_ge3 : 3 ≤ Nat.log 2 c :=
      Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by omega : 2 ^ 3 ≤ c)
    have hratio : (Nat.log 2 z : ℝ) / (Nat.log 2 c : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by
      have hlogc_pos : (0 : ℝ) < (Nat.log 2 c : ℝ) := by exact_mod_cast (show 0 < Nat.log 2 c by omega)
      rw [div_le_iff₀ hlogc_pos]
      have hnat : Nat.log 2 z ≤ 2 ^ (i + 1) * Nat.log 2 c := by
        rw [hlogc, pow_succ, Nat.mul_assoc]
        have hdm := Nat.div_add_mod L (2 ^ i)
        have hmod := Nat.mod_lt L (Nat.two_pow_pos i)
        have hq1 : 1 ≤ L / 2 ^ i := by omega
        have hL_le : L ≤ 2 ^ i * (L / 2 ^ i + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
        have h2q : L / 2 ^ i + 1 ≤ 2 * (L / 2 ^ i) := by omega
        have h1 : L ≤ 2 ^ i * (2 * (L / 2 ^ i)) := hL_le.trans (Nat.mul_le_mul_left _ h2q)
        exact (Nat.le_succ (Nat.log 2 z)).trans h1
      exact_mod_cast hnat
    have hlogz_pos : (0 : ℝ) < (Nat.log 2 z : ℝ) := by exact_mod_cast (show 0 < Nat.log 2 z by omega)
    have hlogc_pos : (0 : ℝ) < (Nat.log 2 c : ℝ) := by exact_mod_cast (show 0 < Nat.log 2 c by omega)
    have hlog_mono : Real.log ((Nat.log 2 z : ℝ) / (Nat.log 2 c : ℝ)) ≤
        Real.log ((2 : ℝ) ^ (i + 1)) :=
      Real.log_le_log (div_pos hlogz_pos hlogc_pos) hratio
    rw [Real.log_pow] at hlog_mono
    have hlog_le : ((i + 1 : ℕ) : ℝ) * Real.log 2 ≤ (i : ℝ) + 1 := by
      push_cast
      nlinarith
    linarith
  · push Not at hc10
    have hdiv_le3 : L / 2 ^ i ≤ 3 := by
      by_contra hgt
      push Not at hgt
      have hpow : 2 ^ 4 ≤ 2 ^ (L / 2 ^ i) := Nat.pow_le_pow_right (by norm_num) hgt
      rw [← hc_eq] at hpow
      omega
    have hL_lt : L < 2 ^ (i + 2) := by
      have hdm := Nat.div_add_mod L (2 ^ i)
      have hmod := Nat.mod_lt L (Nat.two_pow_pos i)
      have hmul : 2 ^ i * (L / 2 ^ i) ≤ 2 ^ i * 3 := Nat.mul_le_mul_left _ hdiv_le3
      have hpow : 2 ^ (i + 2) = 2 ^ i * 4 := by rw [pow_add]; norm_num
      omega
    have hsplit : (Ioc c z).filter Nat.Prime ⊆
        (range 11).filter Nat.Prime ∪ (Ioc 10 z).filter Nat.Prime := by
      intro q hq
      rw [mem_filter, mem_Ioc] at hq
      rw [mem_union, mem_filter, mem_filter, mem_range, mem_Ioc]
      by_cases hq10 : q ≤ 10
      · exact Or.inl ⟨by omega, hq.2⟩
      · exact Or.inr ⟨⟨by omega, hq.1.2⟩, hq.2⟩
    have hdisj_sp : Disjoint ((range 11).filter Nat.Prime) ((Ioc 10 z).filter Nat.Prime) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 := mem_range.mp (mem_filter.mp hp1).1
      have h2 := (mem_Ioc.mp (mem_filter.mp hp2).1).1
      omega
    have hsum_split : ∑ q ∈ (Ioc c z).filter Nat.Prime, (q : ℝ)⁻¹ ≤
        ∑ q ∈ (range 11).filter Nat.Prime, (q : ℝ)⁻¹ +
          ∑ q ∈ (Ioc 10 z).filter Nat.Prime, (q : ℝ)⁻¹ := by
      calc
        ∑ q ∈ (Ioc c z).filter Nat.Prime, (q : ℝ)⁻¹
            ≤ ∑ q ∈ (range 11).filter Nat.Prime ∪ (Ioc 10 z).filter Nat.Prime, (q : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsplit (fun _ _ _ => by positivity)
        _ = _ := Finset.sum_union hdisj_sp
    have hsmall : ∑ q ∈ (range 11).filter Nat.Prime, (q : ℝ)⁻¹ ≤ 10 := by
      calc
        ∑ q ∈ (range 11).filter Nat.Prime, (q : ℝ)⁻¹
            ≤ ∑ _q ∈ (range 11).filter Nat.Prime, (1 : ℝ) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (mem_filter.mp hq).2.one_le
          exact inv_le_one_of_one_le₀ hq1
        _ = (((range 11).filter Nat.Prime).card : ℝ) := by simp
        _ ≤ 10 := by
          have hcard : ((range 11).filter Nat.Prime).card ≤ 10 := by decide
          exact_mod_cast hcard
    have hbig := OMA.R_Erdos687_erdos_687_parts_iii_R1.sum_prime_inv_Ioc_le
      (show 10 ≤ 10 by norm_num) (by omega : 10 ≤ z)
    have hlog10 : Nat.log 2 10 = 3 := by decide
    have hratio : (Nat.log 2 z : ℝ) / (Nat.log 2 10 : ℝ) ≤ (2 : ℝ) ^ (i + 2) := by
      rw [hlog10]
      have h1 : (Nat.log 2 z : ℝ) ≤ (2 : ℝ) ^ (i + 2) := by
        have : Nat.log 2 z ≤ 2 ^ (i + 2) := by dsimp [L] at hL_lt; omega
        exact_mod_cast this
      have h2 : (Nat.log 2 z : ℝ) / (3 : ℝ) ≤ (Nat.log 2 z : ℝ) :=
        div_le_self (Nat.cast_nonneg _) (by norm_num)
      exact h2.trans h1
    have hlogz_pos : (0 : ℝ) < (Nat.log 2 z : ℝ) := by exact_mod_cast (show 0 < Nat.log 2 z by omega)
    have hlog10_pos : (0 : ℝ) < (Nat.log 2 10 : ℝ) := by rw [hlog10]; norm_num
    have hlog_mono : Real.log ((Nat.log 2 z : ℝ) / (Nat.log 2 10 : ℝ)) ≤
        Real.log ((2 : ℝ) ^ (i + 2)) :=
      Real.log_le_log (div_pos hlogz_pos hlog10_pos) hratio
    rw [Real.log_pow] at hlog_mono
    have hlog_le : ((i + 2 : ℕ) : ℝ) * Real.log 2 ≤ (i : ℝ) + 2 := by
      push_cast
      nlinarith
    linarith

/-- Product bound for every divisor set `D` retained in Brun's combinatorial sieve. -/
private lemma brun_prod_le {z b K : ℕ} (hz : 16 ≤ z) (_hb : 1 ≤ b)
    (D : Finset ℕ) (hD_sub : D ⊆ (range (z + 1)).filter Nat.Prime)
    (hD_brun :
      let L := Nat.log 2 z + 1
      let r := Nat.log 2 L + 1
      let cut : ℕ → ℕ := fun i => if i = 0 then z else min z (2 ^ (L / 2 ^ i))
      ∀ i ∈ Icc 1 r, (D ∩ (Ioc (cut i) z).filter Nat.Prime).card ≤ 2 * (b + K * i) - 1) :
    ∏ p ∈ D, p ≤ z ^ (4 * b + 8 * K) := by
  let L := Nat.log 2 z + 1
  let r := Nat.log 2 L + 1
  let cut : ℕ → ℕ := fun i => if i = 0 then z else min z (2 ^ (L / 2 ^ i))
  let P : ℕ → Finset ℕ := fun i => (Ioc (cut i) (cut (i - 1))).filter Nat.Prime
  have hL_ge5 : 5 ≤ L := by
    dsimp [L]
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by omega : 2 ^ 4 ≤ z)
    omega
  have hr_ge1 : 1 ≤ r := by dsimp [r]; omega
  have hcut_anti : Antitone cut := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst hi0
      dsimp only [cut]
      rw [if_pos rfl]
      split_ifs
      · exact le_rfl
      · exact min_le_left z _
    · have hj0 : j ≠ 0 := by omega
      dsimp only [cut]
      rw [if_neg hi0, if_neg hj0]
      apply min_le_min_left z
      exact Nat.pow_le_pow_right (by norm_num)
        (Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hij) (Nat.two_pow_pos i))
  have hcut_r : cut r = 1 := by
    dsimp [cut, r]
    have hlt : L < 2 ^ (Nat.log 2 L + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) L
    rw [Nat.div_eq_of_lt hlt, pow_zero]
    exact min_eq_right (by omega)
  have hcut_le_pow : ∀ i : ℕ, cut i ≤ 2 ^ (L / 2 ^ i) := by
    intro i
    dsimp [cut]
    split_ifs with h0
    · subst h0
      rw [pow_zero, Nat.div_one]
      exact le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) z)
    · exact min_le_right _ _
  have hP_disj : (Icc 1 r : Set ℕ).PairwiseDisjoint P := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    have h1 := mem_Ioc.mp (mem_filter.mp hpi).1
    have h2 := mem_Ioc.mp (mem_filter.mp hpj).1
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have : cut (j - 1) ≤ cut i := hcut_anti (by omega)
      omega
    · have : cut (i - 1) ≤ cut j := hcut_anti (by omega)
      omega
  have hP_union : ∀ k ≤ r, (Icc 1 k).biUnion P = (Ioc (cut k) z).filter Nat.Prime := by
    intro k hk
    induction k with
    | zero =>
      simp [cut]
    | succ m hm =>
      rw [icc_succ_eq_insert (by omega : 1 ≤ m + 1), Finset.biUnion_insert,
        hm (by omega)]
      ext p
      simp only [P, mem_union, mem_filter, mem_Ioc, Nat.add_sub_cancel]
      have hm1 : cut (m + 1) ≤ cut m := hcut_anti (Nat.le_succ m)
      have hm2 : cut m ≤ z := hcut_anti (Nat.zero_le m)
      constructor
      · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
        · exact ⟨⟨h1, h2.trans hm2⟩, hp⟩
        · exact ⟨⟨lt_of_le_of_lt hm1 h1, h2⟩, hp⟩
      · rintro ⟨⟨h1, h2⟩, hp⟩
        by_cases hpm : p ≤ cut m
        · exact Or.inl ⟨⟨h1, hpm⟩, hp⟩
        · exact Or.inr ⟨⟨by omega, h2⟩, hp⟩
  have hD_part : D = (Icc 1 r).biUnion (fun i => D ∩ P i) := by
    have hfull : (range (z + 1)).filter Nat.Prime = (Icc 1 r).biUnion P := by
      rw [hP_union r le_rfl, hcut_r]
      ext p
      simp only [mem_filter, mem_range, mem_Ioc]
      constructor
      · rintro ⟨hpz, hpp⟩
        exact ⟨⟨hpp.one_lt, by omega⟩, hpp⟩
      · rintro ⟨⟨_, hpz⟩, hpp⟩
        exact ⟨by omega, hpp⟩
    rw [← Finset.inter_biUnion, ← hfull, Finset.inter_eq_left.mpr hD_sub]
  have hDP_disj : (Icc 1 r : Set ℕ).PairwiseDisjoint (fun i => D ∩ P i) := by
    intro i hi j hj hij
    rw [Function.onFun]
    exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hP_disj hi hj hij)
  have hprod_bound : ∏ p ∈ D, p ≤ 2 ^ (∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1))) := by
    conv_lhs => rw [hD_part]
    rw [Finset.prod_biUnion hDP_disj, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod' fun i _ => ?_
    calc
      ∏ p ∈ D ∩ P i, p ≤ ∏ _p ∈ D ∩ P i, 2 ^ (L / 2 ^ (i - 1)) := by
        refine Finset.prod_le_prod' fun p hp => ?_
        have hp_le : p ≤ cut (i - 1) := (mem_Ioc.mp (mem_filter.mp (mem_inter.mp hp).2).1).2
        exact hp_le.trans (hcut_le_pow (i - 1))
      _ = (2 ^ (L / 2 ^ (i - 1))) ^ (D ∩ P i).card := Finset.prod_const _
      _ = 2 ^ ((D ∩ P i).card * (L / 2 ^ (i - 1))) := by rw [← pow_mul, Nat.mul_comm]
  -- Bound the natural-number exponent via summation by parts in `ℝ`.
  let N : ℕ → ℝ := fun k => ((D ∩ (Ioc (cut k) z).filter Nat.Prime).card : ℝ)
  have hN0 : N 0 = 0 := by simp [N, cut]
  have hN_step : ∀ i ∈ Icc 1 r, ((D ∩ P i).card : ℝ) = N i - N (i - 1) := by
    intro i hi
    have hi' := mem_Icc.mp hi
    have hdisj_i : Disjoint (D ∩ (Ioc (cut (i - 1)) z).filter Nat.Prime) (D ∩ P i) := by
      rw [← hP_union (i - 1) (by omega), Finset.disjoint_left]
      intro p hp1 hp2
      have h1 := (mem_inter.mp hp1).2
      have h2 := (mem_inter.mp hp2).2
      rw [mem_biUnion] at h1
      obtain ⟨j, hj, hpj⟩ := h1
      have hj' := mem_Icc.mp hj
      exact Finset.disjoint_left.mp
        (hP_disj (mem_coe.mpr (mem_Icc.mpr ⟨hj'.1, by omega⟩)) (mem_coe.mpr hi) (by omega)) hpj h2
    have hunion_i : D ∩ (Ioc (cut i) z).filter Nat.Prime =
        (D ∩ (Ioc (cut (i - 1)) z).filter Nat.Prime) ∪ (D ∩ P i) := by
      rw [← hP_union i hi'.2, ← hP_union (i - 1) (by omega)]
      have hIcc : Icc 1 i = insert i (Icc 1 (i - 1)) := by
        ext j
        simp only [mem_Icc, mem_insert]
        omega
      rw [hIcc, Finset.biUnion_insert, Finset.inter_union_distrib_left, Finset.union_comm]
    have hcard_add : (D ∩ (Ioc (cut i) z).filter Nat.Prime).card =
        (D ∩ (Ioc (cut (i - 1)) z).filter Nat.Prime).card + (D ∩ P i).card := by
      rw [hunion_i, Finset.card_union_of_disjoint hdisj_i]
    have hcard_r : N i = N (i - 1) + ((D ∩ P i).card : ℝ) := by
      dsimp [N]
      exact_mod_cast hcard_add
    linarith
  have hN_le : ∀ i ∈ Icc 1 r, N i ≤ (2 * b + 2 * K * i : ℝ) := by
    intro i hi
    have h : (D ∩ (Ioc (cut i) z).filter Nat.Prime).card ≤ 2 * (b + K * i) - 1 := hD_brun i hi
    have hle : (D ∩ (Ioc (cut i) z).filter Nat.Prime).card ≤ 2 * (b + K * i) :=
      h.trans (Nat.sub_le _ _)
    have hle_r : N i ≤ ((2 * (b + K * i) : ℕ) : ℝ) := by
      dsimp [N]
      exact_mod_cast hle
    push_cast at hle_r
    linarith
  have hexp_real : ((∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1)) : ℕ) : ℝ) ≤
      ((2 * b + 4 * K) * L : ℝ) := by
    push_cast
    have h1 : ∑ i ∈ Icc 1 r, ((D ∩ P i).card : ℝ) * ((L / 2 ^ (i - 1) : ℕ) : ℝ) ≤
        ∑ i ∈ Icc 1 r, (N i - N (i - 1)) * ((L : ℝ) / (2 : ℝ) ^ (i - 1)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [hN_step i hi]
      have hnn : 0 ≤ N i - N (i - 1) := by rw [← hN_step i hi]; exact Nat.cast_nonneg _
      have hdiv : ((L / 2 ^ (i - 1) : ℕ) : ℝ) ≤ (L : ℝ) / (2 : ℝ) ^ (i - 1) := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self L (2 ^ (i - 1))
      exact mul_le_mul_of_nonneg_left hdiv hnn
    have hsbp : ∑ i ∈ Icc 1 r, (N i - N (i - 1)) * ((L : ℝ) / (2 : ℝ) ^ (i - 1)) =
        (L : ℝ) * (N r / (2 : ℝ) ^ (r - 1) + ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i) := by
      have htele : ∀ n : ℕ, 1 ≤ n →
          ∑ i ∈ Icc 1 n, (N i - N (i - 1)) * ((L : ℝ) / (2 : ℝ) ^ (i - 1)) =
          (L : ℝ) * (N n / (2 : ℝ) ^ (n - 1) + ∑ i ∈ Icc 1 (n - 1), N i / (2 : ℝ) ^ i) := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => simp [hN0]; ring
        | succ m hm ih =>
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
          have hsub : m + 1 - 1 = m := by omega
          rw [hsub]
          have hIcc : Icc 1 m = insert m (Icc 1 (m - 1)) := by
            ext i; simp only [mem_Icc, mem_insert]; omega
          have hnotmem : m ∉ Icc 1 (m - 1) := by simp only [mem_Icc]; omega
          rw [hIcc, Finset.sum_insert hnotmem]
          have hpow : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel hm]
          rw [hpow]
          have h2m : (2 : ℝ) ^ (m - 1) ≠ 0 := by positivity
          field_simp
          ring
      exact htele r hr_ge1
    have h2 : N r / (2 : ℝ) ^ (r - 1) + ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i ≤
        (2 * b + 4 * K : ℝ) := by
      have hterm1 : N r / (2 : ℝ) ^ (r - 1) ≤ (2 * b + 2 * K * r : ℝ) / (2 : ℝ) ^ (r - 1) :=
        div_le_div_of_nonneg_right (hN_le r (mem_Icc.mpr ⟨hr_ge1, le_rfl⟩)) (by positivity)
      have hterm2 : ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i ≤
          ∑ i ∈ Icc 1 (r - 1), (2 * b + 2 * K * i : ℝ) / (2 : ℝ) ^ i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := mem_Icc.mp hi
        exact div_le_div_of_nonneg_right (hN_le i (mem_Icc.mpr ⟨hi'.1, by omega⟩)) (by positivity)
      have hident := brun_dyadic_weight_bound b K r hr_ge1
      have hKnn : (0 : ℝ) ≤ (2 * K : ℝ) / (2 : ℝ) ^ (r - 1) := by positivity
      linarith
    calc
      ∑ i ∈ Icc 1 r, ((D ∩ P i).card : ℝ) * ((L / 2 ^ (i - 1) : ℕ) : ℝ)
          ≤ (L : ℝ) * (N r / (2 : ℝ) ^ (r - 1) + ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i) :=
        h1.trans_eq hsbp
      _ ≤ (L : ℝ) * (2 * b + 4 * K : ℝ) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg L)
      _ = ((2 * b + 4 * K) * L : ℝ) := by ring
  have hexp_nat : ∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1)) ≤ (2 * b + 4 * K) * L := by
    exact_mod_cast hexp_real
  have h2L_le : 2 ^ L ≤ z ^ 2 := by
    have h1 : 2 ^ (Nat.log 2 z) ≤ z := Nat.pow_log_le_self 2 (by omega)
    dsimp [L]
    rw [pow_succ, sq]
    nlinarith
  calc
    ∏ p ∈ D, p ≤ 2 ^ (∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1))) := hprod_bound
    _ ≤ 2 ^ ((2 * b + 4 * K) * L) := Nat.pow_le_pow_right (by norm_num) hexp_nat
    _ = (2 ^ L) ^ (2 * b + 4 * K) := by rw [Nat.mul_comm, pow_mul]
    _ ≤ (z ^ 2) ^ (2 * b + 4 * K) := Nat.pow_le_pow_left h2L_le _
    _ = z ^ (4 * b + 8 * K) := by rw [← pow_mul]; congr 1; ring

theorem E687Rankin.r1_H1 : OMA.R_Erdos687_erdos_687_parts_iii_R1.H1 := by
  intro δ hδ s₀
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge (2 + Real.exp 1)
  let K : ℕ := K₀ + 1
  let A : ℝ := 18 * (K₀ : ℝ)
  let C₁ : ℝ := (24 + 16 * (K : ℝ)) ^ 3
  have hC₁_pos : 0 < C₁ := by dsimp [C₁]; positivity
  obtain ⟨b₀, hb₀⟩ := exists_nat_ge (32 * Real.exp A * C₁ / δ)
  let b : ℕ := max 1 (max s₀ (b₀ + 1))
  have hb1 : 1 ≤ b := le_max_left _ _
  have hbs₀ : s₀ ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have hbb₀ : b₀ + 1 ≤ b := (le_max_right _ _).trans (le_max_right _ _)
  let s : ℕ := 8 * b + 16 * K + 4
  refine ⟨s, by dsimp [s]; omega, by dsimp [s]; omega, ?_⟩
  obtain ⟨Z₁, hZ₁⟩ := exists_nat_ge (2 * (s : ℝ) ^ 3 / δ)
  rw [eventually_atTop]
  refine ⟨max 16 (Z₁ + 1), fun z hz y hzy a => ?_⟩
  have hz16 : 16 ≤ z := le_trans (le_max_left _ _) hz
  have hzZ₁ : Z₁ + 1 ≤ z := le_trans (le_max_right _ _) hz
  let P_all := (range (z + 1)).filter Nat.Prime
  let L := Nat.log 2 z + 1
  let r := Nat.log 2 L + 1
  let cut : ℕ → ℕ := fun i => if i = 0 then z else min z (2 ^ (L / 2 ^ i))
  let P : ℕ → Finset ℕ := fun i => (Ioc (cut i) (cut (i - 1))).filter Nat.Prime
  let Q : ℕ → Finset ℕ := fun i => (Ioc (cut i) z).filter Nat.Prime
  let bf : ℕ → ℕ := fun i => b + K * i
  have hr_ge1 : 1 ≤ r := by dsimp [r]; omega
  have hcut_anti : Antitone cut := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst hi0
      dsimp only [cut]
      rw [if_pos rfl]
      split_ifs
      · exact le_rfl
      · exact min_le_left z _
    · have hj0 : j ≠ 0 := by omega
      dsimp only [cut]
      rw [if_neg hi0, if_neg hj0]
      apply min_le_min_left z
      exact Nat.pow_le_pow_right (by norm_num)
        (Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hij) (Nat.two_pow_pos i))
  have hcut_r : cut r = 1 := by
    dsimp [cut, r]
    have hlt : L < 2 ^ (Nat.log 2 L + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) L
    rw [Nat.div_eq_of_lt hlt, pow_zero]
    exact min_eq_right (by omega)
  have hP_disj : ∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → Disjoint (P i) (P j) := by
    intro i j hi hj hij
    rw [Finset.disjoint_left]
    intro p hpi hpj
    have h1 := mem_Ioc.mp (mem_filter.mp hpi).1
    have h2 := mem_Ioc.mp (mem_filter.mp hpj).1
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have : cut (j - 1) ≤ cut i := hcut_anti (by omega)
      omega
    · have : cut (i - 1) ≤ cut j := hcut_anti (by omega)
      omega
  have hQ_eq : ∀ k ≤ r, (Icc 1 k).biUnion P = Q k := by
    intro k hk
    induction k with
    | zero => simp [Q, cut]
    | succ m hm =>
      rw [icc_succ_eq_insert (by omega : 1 ≤ m + 1), Finset.biUnion_insert,
        hm (by omega)]
      ext p
      simp only [P, Q, mem_union, mem_filter, mem_Ioc, Nat.add_sub_cancel]
      have hm1 : cut (m + 1) ≤ cut m := hcut_anti (Nat.le_succ m)
      have hm2 : cut m ≤ z := hcut_anti (Nat.zero_le m)
      constructor
      · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
        · exact ⟨⟨h1, h2.trans hm2⟩, hp⟩
        · exact ⟨⟨lt_of_le_of_lt hm1 h1, h2⟩, hp⟩
      · rintro ⟨⟨h1, h2⟩, hp⟩
        by_cases hpm : p ≤ cut m
        · exact Or.inl ⟨⟨h1, hpm⟩, hp⟩
        · exact Or.inr ⟨⟨by omega, h2⟩, hp⟩
  have hP_all_eq : P_all = (Icc 1 r).biUnion P := by
    rw [hQ_eq r le_rfl]
    dsimp [P_all, Q]
    rw [hcut_r]
    ext p
    simp only [mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨hpz, hpp⟩; exact ⟨⟨hpp.one_lt, by omega⟩, hpp⟩
    · rintro ⟨⟨_, hpz⟩, hpp⟩; exact ⟨by omega, hpp⟩
  -- Define Brun's retained divisor family `D_brun ⊆ P_all.powerset`.
  let D_brun := P_all.powerset.filter (brunPred Q bf r)
  -- Step 1: Pointwise Brun lower bound summed over `m ∈ Icc 1 y`.
  have hstep1 :
      ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
        (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) ≤
      (((Icc 1 y).filter fun m => ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) := by
    let B : ℕ → Finset ℕ := fun m => P_all.filter (fun p => m ≡ a p [MOD p])
    have hsurv : (((Icc 1 y).filter fun m => ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) =
        ∑ m ∈ Icc 1 y, (if B m = ∅ then (1 : ℝ) else 0) := by
      rw [Finset.sum_boole]
      congr 2
      ext m
      simp only [B, P_all, mem_filter, Finset.eq_empty_iff_forall_notMem, mem_range]
      refine and_congr_right fun _ => ?_
      constructor
      · intro h p ⟨⟨hpz, hpp⟩, hmod⟩
        exact h p (by omega) hpp hmod
      · intro h p hpz hpp hmod
        exact h p ⟨⟨by omega, hpp⟩, hmod⟩
    rw [hsurv]
    have hpt : ∀ m ∈ Icc 1 y,
        ∑ D ∈ D_brun, (if ∀ p ∈ D, m ≡ a p [MOD p] then (-1 : ℝ) ^ D.card else 0) ≤
          if B m = ∅ then (1 : ℝ) else 0 := by
      intro m _
      have hBm_sub : B m ⊆ (Icc 1 r).biUnion P := by
        rw [← hP_all_eq]
        exact Finset.filter_subset _ _
      have hfilt_eq : D_brun.filter (fun D => ∀ p ∈ D, m ≡ a p [MOD p]) =
          (B m).powerset.filter (brunPred (fun k => (Icc 1 k).biUnion P) bf r) := by
        ext D
        simp only [D_brun, B, brunPred, mem_filter, mem_powerset]
        constructor
        · rintro ⟨⟨hDP, hDb⟩, hDm⟩
          refine ⟨fun p hp => mem_filter.mpr ⟨hDP hp, hDm p hp⟩, fun i hi => ?_⟩
          rw [hQ_eq i (mem_Icc.mp hi).2]
          exact hDb i hi
        · rintro ⟨hDB, hDb⟩
          refine ⟨⟨fun p hp => (mem_filter.mp (hDB hp)).1, fun i hi => ?_⟩,
            fun p hp => (mem_filter.mp (hDB hp)).2⟩
          rw [← hQ_eq i (mem_Icc.mp hi).2]
          exact hDb i hi
      rw [← Finset.sum_filter, hfilt_eq]
      exact brun_pointwise_lower P bf (by dsimp [bf]; omega)
        (fun i _ => by dsimp [bf]; rw [Nat.mul_succ]; omega) hP_disj r (B m) hBm_sub
    have hswap :
        ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
          (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) =
        ∑ m ∈ Icc 1 y, ∑ D ∈ D_brun,
          if ∀ p ∈ D, m ≡ a p [MOD p] then (-1 : ℝ) ^ D.card else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun D _ => ?_
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
        mul_comm]
    rw [hswap]
    exact Finset.sum_le_sum hpt
  -- Step 2: Apply CRT approximation to every retained divisor `D ∈ D_brun`.
  have hstep2 :
      (y : ℝ) * (∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)) -
        (D_brun.card : ℝ) ≤
      ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
        (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) := by
    have hdiff : ∀ D ∈ D_brun,
        (y : ℝ) * ((-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)) - 1 ≤
          (-1 : ℝ) ^ D.card *
            (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) := by
      intro D hD
      have hDp : ∀ p ∈ D, p.Prime := fun p hp =>
        (mem_filter.mp (mem_powerset.mp (mem_filter.mp hD).1 hp)).2
      have hcrt := crt_count_sub_div_le_one hDp a y
      have hmul_abs :
          |(-1 : ℝ) ^ D.card *
            ((((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) -
              (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹))| ≤ 1 := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact hcrt
      have hlo := (abs_le.mp hmul_abs).1
      linarith
    have hsum := Finset.sum_le_sum hdiff
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    exact hsum
  -- Step 3: Bound the truncation tail `|V(z) - ∑_{D ∈ D_brun} (-1)^|D| w(D)|`.
  let V : ℕ → ℝ := fun u => ∏ p ∈ (range (u + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)
  have hVz_pos : 0 < V z := eulerProd_pos_finset _ fun _ hp => (mem_filter.mp hp).2
  have htrunc :
      |V z - ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)| ≤
        Real.exp (A - 2 * (b : ℝ)) * V z := by
    have hsub_D : D_brun ⊆ P_all.powerset := Finset.filter_subset _ _
    -- Partition `P_all.powerset \ D_brun` by the first violated block `i ∈ Icc 1 r`.
    let Bad : ℕ → Finset (Finset ℕ) := fun i =>
      P_all.powerset.filter fun D =>
        brunPredIco Q bf i D ∧ 2 * bf i ≤ (D ∩ Q i).card
    have hBad_pw : (Icc 1 r : Set ℕ).PairwiseDisjoint Bad := by
      intro i hi j hj hij
      rw [Function.onFun, Finset.disjoint_left]
      intro D hDi hDj
      have h1 := (mem_filter.mp hDi).2
      have h2 := (mem_filter.mp hDj).2
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have := h2.1 i (mem_Ico.mpr ⟨(mem_Icc.mp hi).1, hlt⟩)
        have hbf1 : 1 ≤ bf i := by dsimp [bf]; omega
        omega
      · have := h1.1 j (mem_Ico.mpr ⟨(mem_Icc.mp hj).1, hgt⟩)
        have hbf1 : 1 ≤ bf j := by dsimp [bf]; omega
        omega
    have hBad_eq : P_all.powerset \ D_brun = (Icc 1 r).biUnion Bad := by
      ext D
      simp only [Finset.mem_sdiff, mem_biUnion, D_brun, Bad, mem_filter]
      simp only [brunPred, brunPredIco]
      constructor
      · rintro ⟨hDP, hnot⟩
        let S := (Icc 1 r).filter fun i => 2 * bf i ≤ (D ∩ Q i).card
        have hS_ne : S.Nonempty := by
          by_contra hnone
          rw [Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem] at hnone
          refine hnot ⟨hDP, fun i hi => ?_⟩
          have hni := hnone i
          simp only [S, mem_filter, hi, true_and, not_le] at hni
          omega
        let i := S.min' hS_ne
        have hi_mem : i ∈ S := Finset.min'_mem S hS_ne
        have hi_p := mem_filter.mp hi_mem
        refine ⟨i, hi_p.1, hDP, fun j hj => ?_, hi_p.2⟩
        have hj' := mem_Ico.mp hj
        have hj_not : j ∉ S := fun hjS =>
          (not_le_of_gt hj'.2) (Finset.min'_le S j hjS)
        have hj_icc : j ∈ Icc 1 r := mem_Icc.mpr ⟨hj'.1, hj'.2.le.trans (mem_Icc.mp hi_p.1).2⟩
        simp only [S, mem_filter, hj_icc, true_and, not_le] at hj_not
        omega
      · rintro ⟨i, hi, hDP, _, hviol⟩
        refine ⟨hDP, fun h => ?_⟩
        have hle := h.2 i hi
        have hbf1 : 1 ≤ bf i := by dsimp [bf]; omega
        omega
    have hdiff_eq : V z - ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) =
        ∑ i ∈ Icc 1 r, ∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) := by
      rw [show V z = ∑ D ∈ P_all.powerset, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) from
        eulerProd_eq_powerset_sum P_all, ← Finset.sum_sdiff hsub_D, add_sub_cancel_right,
        hBad_eq, Finset.sum_biUnion hBad_pw]
    rw [hdiff_eq]
    have hterm_i : ∀ i ∈ Icc 1 r,
        |∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)| ≤
          Real.exp (A - 2 * (b : ℝ)) * ((1 / 2 : ℝ) ^ i) * V z := by
      intro i hi
      have hi' := mem_Icc.mp hi
      let P_lo := (range (cut i + 1)).filter Nat.Prime
      have hQ_sub : Q i ⊆ P_all := by
        intro p hp
        rw [mem_filter, mem_Ioc] at hp
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp.2⟩
      have hPlo_sub : P_lo ⊆ P_all := by
        intro p hp
        rw [mem_filter, mem_range] at hp
        have hcz : cut i ≤ z := hcut_anti (Nat.zero_le i)
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp.2⟩
      have hQP_disj : Disjoint (Q i) P_lo := by
        rw [Finset.disjoint_left]
        intro p hpQ hpL
        have h1 := (mem_Ioc.mp (mem_filter.mp hpQ).1).1
        have h2 := mem_range.mp (mem_filter.mp hpL).1
        omega
      have hQP_union : Q i ∪ P_lo = P_all := by
        ext p
        simp only [Q, P_lo, P_all, mem_union, mem_filter, mem_Ioc, mem_range]
        have hcz : cut i ≤ z := hcut_anti (Nat.zero_le i)
        constructor
        · rintro (⟨⟨_, h2⟩, hp⟩ | ⟨h1, hp⟩) <;> exact ⟨by omega, hp⟩
        · rintro ⟨h1, hp⟩
          by_cases hpc : p ≤ cut i
          · exact Or.inr ⟨by omega, hp⟩
          · exact Or.inl ⟨⟨by omega, by omega⟩, hp⟩
      let A_i := (Q i).powerset.filter fun D₁ =>
        brunPredIco Q bf i D₁ ∧ 2 * bf i ≤ D₁.card
      -- Factor `Bad i` as `A_i ×ˢ P_lo.powerset`.
      have hfac : ∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) =
          (∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)) * V (cut i) := by
        rw [show V (cut i) = ∑ D₂ ∈ P_lo.powerset, (-1 : ℝ) ^ D₂.card * (∏ p ∈ D₂, (p : ℝ)⁻¹) from
          eulerProd_eq_powerset_sum P_lo, Finset.sum_mul_sum, ← Finset.sum_product']
        refine (Finset.sum_nbij (fun x : Finset ℕ × Finset ℕ => x.1 ∪ x.2) ?_ ?_ ?_ ?_).symm
        · intro x hx
          rw [mem_product] at hx
          obtain ⟨hD₁, hD₂⟩ := hx
          have hD₁p := mem_filter.mp hD₁
          have hD₁Q : x.1 ⊆ Q i := mem_powerset.mp hD₁p.1
          have hD₂L : x.2 ⊆ P_lo := mem_powerset.mp hD₂
          refine mem_filter.mpr ⟨mem_powerset.mpr ?_, fun j hj => ?_, ?_⟩
          · rw [← hQP_union]
            exact Finset.union_subset_union hD₁Q hD₂L
          · have hj' := mem_Ico.mp hj
            have hQj_sub : Q j ⊆ Q i := by
              intro p hp
              rw [mem_filter, mem_Ioc] at hp ⊢
              have : cut i ≤ cut j := hcut_anti hj'.2.le
              exact ⟨⟨lt_of_le_of_lt this hp.1.1, hp.1.2⟩, hp.2⟩
            have hdisj2 : Disjoint x.2 (Q j) := Disjoint.mono hD₂L hQj_sub hQP_disj.symm
            rw [Finset.union_inter_distrib_right,
              Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.union_empty]
            exact hD₁p.2.1 j hj
          · have hdisj2 : Disjoint x.2 (Q i) := Disjoint.mono_left hD₂L hQP_disj.symm
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hD₁Q,
              Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.union_empty]
            exact hD₁p.2.2
        · intro x hx y hy hxy
          rw [mem_coe, mem_product] at hx hy
          have hx1 : x.1 ⊆ Q i := mem_powerset.mp (mem_filter.mp hx.1).1
          have hx2 : x.2 ⊆ P_lo := mem_powerset.mp hx.2
          have hy1 : y.1 ⊆ Q i := mem_powerset.mp (mem_filter.mp hy.1).1
          have hy2 : y.2 ⊆ P_lo := mem_powerset.mp hy.2
          have heq1 : x.1 = y.1 := by
            have := congrArg (· ∩ Q i) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx1,
              Finset.inter_eq_left.mpr hy1,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx2 hQP_disj.symm),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy2 hQP_disj.symm),
              Finset.union_empty] using this
          have heq2 : x.2 = y.2 := by
            have := congrArg (· ∩ P_lo) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx2,
              Finset.inter_eq_left.mpr hy2,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx1 hQP_disj),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy1 hQP_disj),
              Finset.empty_union] using this
          exact Prod.ext heq1 heq2
        · intro D hD
          rw [mem_coe] at hD
          have hDp := mem_filter.mp hD
          have hDP : D ⊆ P_all := mem_powerset.mp hDp.1
          let D₁ := D ∩ Q i
          let D₂ := D ∩ P_lo
          have hDeq : D₁ ∪ D₂ = D := by
            rw [← Finset.inter_union_distrib_left, hQP_union, Finset.inter_eq_left.mpr hDP]
          have hD₁mem : D₁ ∈ A_i := by
            refine mem_filter.mpr ⟨mem_powerset.mpr Finset.inter_subset_right, fun j hj => ?_, hDp.2.2⟩
            have hj' := mem_Ico.mp hj
            have hQj_sub : Q j ⊆ Q i := by
              intro p hp
              rw [mem_filter, mem_Ioc] at hp ⊢
              have : cut i ≤ cut j := hcut_anti hj'.2.le
              exact ⟨⟨lt_of_le_of_lt this hp.1.1, hp.1.2⟩, hp.2⟩
            dsimp [D₁]
            rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hQj_sub]
            exact hDp.2.1 j hj
          have hD₂mem : D₂ ∈ P_lo.powerset := mem_powerset.mpr Finset.inter_subset_right
          exact ⟨(D₁, D₂), mem_coe.mpr (mem_product.mpr ⟨hD₁mem, hD₂mem⟩), hDeq⟩
        · intro x hx
          rw [mem_product] at hx
          have hx1 : x.1 ⊆ Q i := mem_powerset.mp (mem_filter.mp hx.1).1
          have hx2 : x.2 ⊆ P_lo := mem_powerset.mp hx.2
          have hdisj : Disjoint x.1 x.2 := Disjoint.mono hx1 hx2 hQP_disj
          rw [Finset.card_union_of_disjoint hdisj, pow_add, Finset.prod_union hdisj]
          ring
      rw [hfac, abs_mul, abs_of_pos (eulerProd_pos_finset _ fun _ hp => (mem_filter.mp hp).2)]
      have hAi_le : |∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)| ≤
          ∑ D₁ ∈ (Q i).powerset.filter (fun D₁ => 2 * bf i ≤ D₁.card),
            (∏ p ∈ D₁, (p : ℝ)⁻¹) := by
        calc
          |∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)|
              ≤ ∑ D₁ ∈ A_i, |(-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ D₁ ∈ A_i, (∏ p ∈ D₁, (p : ℝ)⁻¹) := by
            refine Finset.sum_congr rfl fun D₁ _ => ?_
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
              abs_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
          _ ≤ ∑ D₁ ∈ (Q i).powerset.filter (fun D₁ => 2 * bf i ≤ D₁.card),
                (∏ p ∈ D₁, (p : ℝ)⁻¹) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ =>
              Finset.prod_nonneg fun _ _ => by positivity)
            intro D₁ hD₁
            have h := mem_filter.mp hD₁
            exact mem_filter.mpr ⟨h.1, h.2.2⟩
      -- Bound `V (cut i) ≤ Real.exp (2 * S_i) * V z`.
      let S_i := ∑ q ∈ Q i, (q : ℝ)⁻¹
      have hV_ratio : V (cut i) ≤ Real.exp (2 * S_i) * V z := by
        have hVsplit : V z = V (cut i) * ∏ q ∈ Q i, (1 - (q : ℝ)⁻¹) := by
          dsimp [V]
          rw [show (range (z + 1)).filter Nat.Prime = Q i ∪ P_lo from hQP_union.symm,
            Finset.prod_union hQP_disj, mul_comm]
        have hQprod_pos : 0 < ∏ q ∈ Q i, (1 - (q : ℝ)⁻¹) :=
          eulerProd_pos_finset _ fun _ hq => (mem_filter.mp hq).2
        have hQinv : (∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))⁻¹ ≤ Real.exp (2 * S_i) := by
          rw [← Finset.prod_inv_distrib, Finset.mul_sum, Real.exp_sum]
          apply Finset.prod_le_prod
          · intro q hq
            have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (mem_filter.mp hq).2.two_le
            have hinv : (q : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq2
            exact inv_nonneg.mpr (by linarith)
          · intro q hq
            exact one_sub_inv_inv_le_exp_two (mem_filter.mp hq).2.two_le
        rw [hVsplit]
        calc
          V (cut i) = V (cut i) * ((∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))⁻¹ *
              (∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))) := by
            rw [inv_mul_cancel₀ hQprod_pos.ne', mul_one]
          _ ≤ V (cut i) * (Real.exp (2 * S_i) * (∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))) := by
            gcongr
            exact (eulerProd_pos_finset _ fun _ hp => (mem_filter.mp hp).2).le
          _ = Real.exp (2 * S_i) * (V (cut i) * ∏ q ∈ Q i, (1 - (q : ℝ)⁻¹)) := by ring
      have hS_i : S_i ≤ 18 + 2 * (i : ℝ) := by
        have hcut_eq : cut i = min z (2 ^ (L / 2 ^ i)) := if_neg (by omega)
        dsimp [S_i, Q]
        rw [hcut_eq]
        exact brun_block_recip_sum_le hz16 hi'.1
      have htail := brun_tail_bound (Q i) (2 * bf i)
      have hcomb_exp : -(2 * bf i : ℕ) + Real.exp 1 * S_i + 2 * S_i ≤
          A - 2 * (b : ℝ) - 2 * (i : ℝ) := by
        have hS_nn : 0 ≤ S_i := Finset.sum_nonneg fun _ _ => by positivity
        have h1 : (2 + Real.exp 1) * S_i ≤ (K₀ : ℝ) * (18 + 2 * (i : ℝ)) :=
          mul_le_mul hK₀ hS_i hS_nn (by positivity)
        have hbf_cast : ((2 * bf i : ℕ) : ℝ) = 2 * (b : ℝ) + 2 * ((K₀ : ℝ) + 1) * (i : ℝ) := by
          dsimp [bf, K]
          push_cast
          ring
        rw [hbf_cast]
        dsimp [A]
        linarith
      have hexp_half : Real.exp (-2 * (i : ℝ)) ≤ (1 / 2 : ℝ) ^ i := by
        have h2e : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
        have he_le : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) h2e
        have hpow : Real.exp (-2 * (i : ℝ)) = (Real.exp (-2 : ℝ)) ^ i := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        rw [hpow]
        exact pow_le_pow_left₀ (by positivity) he_le i
      calc
        |∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)| * V (cut i)
            ≤ Real.exp (-(2 * bf i : ℕ) + Real.exp 1 * S_i) * (Real.exp (2 * S_i) * V z) := by
          exact mul_le_mul (hAi_le.trans htail) hV_ratio
            (eulerProd_pos_finset _ fun _ hp => (mem_filter.mp hp).2).le (by positivity)
        _ = Real.exp (-(2 * bf i : ℕ) + Real.exp 1 * S_i + 2 * S_i) * V z := by
          rw [← mul_assoc, ← Real.exp_add]
        _ ≤ Real.exp (A - 2 * (b : ℝ) - 2 * (i : ℝ)) * V z := by
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcomb_exp) hVz_pos.le
        _ = Real.exp (A - 2 * (b : ℝ)) * Real.exp (-2 * (i : ℝ)) * V z := by
          rw [← Real.exp_add]
          congr 2
          ring
        _ ≤ Real.exp (A - 2 * (b : ℝ)) * ((1 / 2 : ℝ) ^ i) * V z := by
          have h1 := mul_le_mul_of_nonneg_left hexp_half (by positivity : 0 ≤ Real.exp (A - 2 * (b : ℝ)))
          exact mul_le_mul_of_nonneg_right h1 hVz_pos.le
    calc
      |∑ i ∈ Icc 1 r, ∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)|
          ≤ ∑ i ∈ Icc 1 r, |∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Icc 1 r, Real.exp (A - 2 * (b : ℝ)) * ((1 / 2 : ℝ) ^ i) * V z :=
        Finset.sum_le_sum hterm_i
      _ = Real.exp (A - 2 * (b : ℝ)) * (∑ i ∈ Icc 1 r, (1 / 2 : ℝ) ^ i) * V z := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ Real.exp (A - 2 * (b : ℝ)) * 1 * V z := by
        have h1 := mul_le_mul_of_nonneg_left (geom_half_sum_le_one r)
          (by positivity : 0 ≤ Real.exp (A - 2 * (b : ℝ)))
        exact mul_le_mul_of_nonneg_right h1 hVz_pos.le
      _ = Real.exp (A - 2 * (b : ℝ)) * V z := by rw [mul_one]
  -- Step 4: Bound `D_brun.card ≤ z ^ (4 * b + 8 * K)` using `brun_prod_le`.
  have hD_card : D_brun.card ≤ z ^ (4 * b + 8 * K) := by
    have hsub_D : D_brun ⊆ P_all.powerset := Finset.filter_subset _ _
    have hinj : Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p) (D_brun : Set (Finset ℕ)) :=
      (prime_finset_prod_injOn P_all fun _ hp => (mem_filter.mp hp).2).mono
        (Finset.coe_subset.mpr hsub_D)
    have hmaps : Set.MapsTo (fun D : Finset ℕ => ∏ p ∈ D, p) (D_brun : Set (Finset ℕ))
        (Icc 1 (z ^ (4 * b + 8 * K)) : Set ℕ) := by
      intro D hD
      rw [mem_coe] at hD ⊢
      have hDp := mem_filter.mp hD
      have hDsub : D ⊆ P_all := mem_powerset.mp hDp.1
      have hpos : 1 ≤ ∏ p ∈ D, p :=
        Finset.prod_pos fun p hp => (mem_filter.mp (hDsub hp)).2.pos
      have hle : ∏ p ∈ D, p ≤ z ^ (4 * b + 8 * K) := brun_prod_le hz16 hb1 D hDsub hDp.2
      exact mem_Icc.mpr ⟨hpos, hle⟩
    have hle := Finset.card_le_card_of_injOn (fun D : Finset ℕ => ∏ p ∈ D, p) hmaps hinj
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hle
  -- Step 5: Verify both error terms are at most `(δ / (2 * s ^ 3)) * y * V z`.
  have herr_trunc : Real.exp (A - 2 * (b : ℝ)) ≤ δ / (2 * (s : ℝ) ^ 3) := by
    have hs_le : (s : ℝ) ≤ (24 + 16 * (K : ℝ)) * (b : ℝ) := by
      have hb1_r : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
      dsimp [s]
      push_cast
      nlinarith
    have hs3_le : (s : ℝ) ^ 3 ≤ C₁ * (b : ℝ) ^ 3 := by
      dsimp [C₁]
      calc
        (s : ℝ) ^ 3 ≤ ((24 + 16 * (K : ℝ)) * (b : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (Nat.cast_nonneg s) hs_le 3
        _ = (24 + 16 * (K : ℝ)) ^ 3 * (b : ℝ) ^ 3 := mul_pow _ _ 3
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
    have hexp_ge : (2 * (b : ℝ)) ^ 4 / 256 ≤ Real.exp (2 * (b : ℝ)) :=
      pow_four_div_le_exp (by positivity)
    have h1 : Real.exp (A - 2 * (b : ℝ)) ≤ 16 * Real.exp A / (b : ℝ) ^ 4 := by
      rw [Real.exp_sub, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 16 * Real.exp A * ((2 * (b : ℝ)) ^ 4 / 256) = Real.exp A * (b : ℝ) ^ 4 := by ring
      nlinarith [mul_le_mul_of_nonneg_left hexp_ge (by positivity : 0 ≤ 16 * Real.exp A)]
    have hb_ge : 32 * Real.exp A * C₁ / δ ≤ (b : ℝ) := by
      have h1' : (b₀ : ℝ) ≤ (b : ℝ) := by exact_mod_cast (show b₀ ≤ b by omega)
      exact hb₀.trans h1'
    have h2 : 16 * Real.exp A / (b : ℝ) ^ 4 ≤ δ / (2 * (s : ℝ) ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hkey : 32 * Real.exp A * C₁ ≤ δ * (b : ℝ) := by
        rw [mul_comm δ]
        exact (div_le_iff₀ hδ).mp hb_ge
      have hkey2 : 32 * Real.exp A * (C₁ * (b : ℝ) ^ 3) ≤ δ * (b : ℝ) ^ 4 := by
        calc
          32 * Real.exp A * (C₁ * (b : ℝ) ^ 3) = (32 * Real.exp A * C₁) * (b : ℝ) ^ 3 := by ring
          _ ≤ (δ * (b : ℝ)) * (b : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hkey (by positivity)
          _ = δ * (b : ℝ) ^ 4 := by ring
      have hkey3 : 32 * Real.exp A * (s : ℝ) ^ 3 ≤ 32 * Real.exp A * (C₁ * (b : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hs3_le (by positivity)
      linarith
    exact h1.trans h2
  have herr_crt : (D_brun.card : ℝ) ≤ (δ / (2 * (s : ℝ) ^ 3)) * ((y : ℝ) * V z) := by
    have hz_pos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (show 0 < z by omega)
    have hVz_ge : (z : ℝ)⁻¹ ≤ V z := eulerProd_ge_inv (by omega)
    have hD_le_z : (D_brun.card : ℝ) ≤ (z : ℝ)⁻¹ * ((y : ℝ) * V z) := by
      have hpow_nat : z ^ (4 * b + 8 * K) * z ^ 2 ≤ z ^ s := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by dsimp [s]; omega)
      have hpow_y : ((z ^ (4 * b + 8 * K) : ℕ) : ℝ) * ((z : ℝ) ^ 2) ≤ (y : ℝ) := by
        exact_mod_cast hpow_nat.trans hzy
      have hcard_r : (D_brun.card : ℝ) ≤ ((z ^ (4 * b + 8 * K) : ℕ) : ℝ) := by
        exact_mod_cast hD_card
      have hcard_y : (D_brun.card : ℝ) ≤ (z : ℝ)⁻¹ * ((y : ℝ) * (z : ℝ)⁻¹) := by
        have h1 : (D_brun.card : ℝ) * (z : ℝ) ^ 2 ≤ (y : ℝ) :=
          (mul_le_mul_of_nonneg_right hcard_r (by positivity)).trans hpow_y
        have h2 : (D_brun.card : ℝ) ≤ (y : ℝ) / (z : ℝ) ^ 2 :=
          (le_div_iff₀ (by positivity)).mpr h1
        have h3 : (y : ℝ) / (z : ℝ) ^ 2 = (z : ℝ)⁻¹ * ((y : ℝ) * (z : ℝ)⁻¹) := by
          field_simp
        rwa [h3] at h2
      have h4 : (z : ℝ)⁻¹ * ((y : ℝ) * (z : ℝ)⁻¹) ≤ (z : ℝ)⁻¹ * ((y : ℝ) * V z) := by
        gcongr
      exact hcard_y.trans h4
    have hz_ge : 2 * (s : ℝ) ^ 3 / δ ≤ (z : ℝ) := by
      have h1 : (Z₁ : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show Z₁ ≤ z by omega)
      exact hZ₁.trans h1
    have hinv_le : (z : ℝ)⁻¹ ≤ δ / (2 * (s : ℝ) ^ 3) := by
      have hs3_pos : (0 : ℝ) < 2 * (s : ℝ) ^ 3 := by dsimp [s]; positivity
      rw [inv_eq_one_div, div_le_div_iff₀ hz_pos hs3_pos, one_mul, mul_comm δ]
      exact (div_le_iff₀ hδ).mp hz_ge
    exact hD_le_z.trans (mul_le_mul_of_nonneg_right hinv_le (by positivity))
  -- Final assembly.
  have hmain_lo : (1 - δ / (2 * (s : ℝ) ^ 3)) * V z ≤
      ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) := by
    have h1 := (abs_le.mp htrunc).2
    have h2 : Real.exp (A - 2 * (b : ℝ)) * V z ≤ (δ / (2 * (s : ℝ) ^ 3)) * V z :=
      mul_le_mul_of_nonneg_right herr_trunc hVz_pos.le
    linarith
  have hmain_mul : (1 - δ / (2 * (s : ℝ) ^ 3)) * ((y : ℝ) * V z) ≤
      (y : ℝ) * (∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)) := by
    have h := mul_le_mul_of_nonneg_left hmain_lo (Nat.cast_nonneg y)
    linarith
  have hcomb : (1 - δ / (s : ℝ) ^ 3) * (y : ℝ) * V z ≤
      (y : ℝ) * (∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)) - (D_brun.card : ℝ) := by
    have hs_eq : (1 - δ / (s : ℝ) ^ 3) * (y : ℝ) * V z =
        (1 - δ / (2 * (s : ℝ) ^ 3)) * ((y : ℝ) * V z) -
          (δ / (2 * (s : ℝ) ^ 3)) * ((y : ℝ) * V z) := by
      ring
    rw [hs_eq]
    linarith
  exact hcomb.trans (hstep2.trans hstep1)

end R1H1

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

/-- The short-interval rough-number lower bound (step R1.H2.R1.H2 of part iii) is false. -/
theorem not_roughLB : ¬ OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1.H2 := by
  rintro ⟨c, hc, h⟩
  obtain ⟨ε, hε0, hε1, hev⟩ := eventually_exists_shift c hc
  obtain ⟨x, hx1, M, hM⟩ := ((h ε hε0 hε1).and hev).exists
  exact absurd (hx1 M) (not_le.mpr hM)

end E687Rankin

/- ## The top step `R1.H2` (Buchstab large-prime tail bound) is false

With the merged step `R1.H1` (fundamental lemma), the tail bound gives at least `(c/2) * y * V(x)`
survivors in `[1, y]` for every residue system; this is the computation in the `main` theorem of
reduction `Erdos687.erdos_687.parts.iii.R1` (by @santiemanuel), repeated below. The Rankin shift
contradicts it. -/

namespace E687Rankin

open Finset Filter
open scoped Classical

lemma modEq_compl_iff (p M m : ℕ) (hp : 0 < p) : m ≡ (p - M % p) [MOD p] ↔ p ∣ M + m := by
  have hlt := Nat.mod_lt M hp
  have h0 : M + (p - M % p) ≡ 0 [MOD p] := by
    rw [Nat.modEq_zero_iff_dvd]
    have hdm := Nat.div_add_mod M p
    have h1 : M + (p - M % p) = p * (M / p + 1) := by
      rw [mul_add, mul_one]
      omega
    rw [h1]
    exact Dvd.intro _ rfl
  constructor
  · intro h
    exact (Nat.modEq_zero_iff_dvd).mp ((h.add_left M).trans h0)
  · intro h
    have h1 : M + m ≡ M + (p - M % p) [MOD p] :=
      ((Nat.modEq_zero_iff_dvd).mpr h).trans h0.symm
    exact Nat.ModEq.add_left_cancel' M h1

lemma residue_card_eq_shift (x y M : ℕ) (a : ℕ → ℕ) (ha : ∀ p, a p = p - M % p) :
    ((Icc 1 y).filter fun m => ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card =
      ((Icc (M + 1) (M + y)).filter fun n => ∀ p ≤ x, p.Prime → ¬ p ∣ n).card := by
  refine Finset.card_bij (fun m _ => M + m) ?_ ?_ ?_
  · intro m hm
    simp only [mem_filter, mem_Icc] at hm ⊢
    refine ⟨⟨by omega, by omega⟩, fun p hpx hp hdvd => hm.2 p hpx hp ?_⟩
    rw [ha p]
    exact (modEq_compl_iff p M m hp.pos).mpr hdvd
  · intro m₁ _ m₂ _ h
    simpa using h
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    refine ⟨n - M, ?_, by omega⟩
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨by omega, by omega⟩, fun p hpx hp hmod => hn.2 p hpx hp ?_⟩
    rw [ha p] at hmod
    have h1 := (modEq_compl_iff p M (n - M) hp.pos).mp hmod
    rwa [show M + (n - M) = n by omega] at h1

/-- The lower bound for survivors that `R1.H1` and the tail bound of `R1.H2` give at one `x`
(the computation of `OMA.R_Erdos687_erdos_687_parts_iii_R1.main`, by @santiemanuel). -/
lemma surv_lower_of_tail (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) (s Z₀ x : ℕ) (hs2 : 2 ≤ s)
    (hZ₀ : ∀ z ≥ Z₀, ∀ y : ℕ, z ^ s ≤ y → ∀ a : ℕ → ℕ,
      (1 - c / (2 * (8 * Real.exp 5)) / (s : ℝ) ^ 3) * (y : ℝ) *
        (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) ≤
      (((Icc 1 y).filter fun m => ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ))
    (hx : max 1 (max (10 ^ s) (Z₀ ^ s)) ≤ x)
    (hRatio : (∏ p ∈ (range (⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ + 1)).filter Nat.Prime,
        (1 - (p : ℝ)⁻¹)) ≤
      (8 * Real.exp 5) * (s : ℝ) ^ 3 *
        (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)))
    (a : ℕ → ℕ)
    (htail : (∑ q ∈ (Ioc ⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ x).filter Nat.Prime,
        (((Icc 1 ⌈(x : ℝ) ^ (1 + ε)⌉₊).filter fun m =>
          m ≡ a q [MOD q] ∧ ∀ p < q, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ)) ≤
      (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) *
        ((∏ p ∈ (range (⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ + 1)).filter Nat.Prime,
            (1 - (p : ℝ)⁻¹)) -
          c * (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)))) :
    (c / 2) * (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) *
        (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) ≤
      (((Icc 1 ⌈(x : ℝ) ^ (1 + ε)⌉₊).filter fun m =>
        ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) := by
  have hC₀_pos : (0 : ℝ) < 8 * Real.exp 5 := by positivity
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxZ : Z₀ ^ s ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hx_ge1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hz_ge_Z₀ : Z₀ ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ := by
    apply Nat.le_floor
    calc
      (Z₀ : ℝ) = ((Z₀ : ℝ) ^ (s : ℝ)) ^ ((1 : ℝ) / (s : ℝ)) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg Z₀), mul_one_div_cancel hs_pos.ne', Real.rpow_one]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        simpa [Real.rpow_natCast] using (show ((Z₀ ^ s : ℕ) : ℝ) ≤ (x : ℝ) by exact_mod_cast hxZ)
  have hzx : ⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ ≤ x := by
    have hrpow_le : (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) ≤ (x : ℝ) := by
      calc
        (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx_ge1
            ((div_le_one hs_pos).mpr (by exact_mod_cast (show 1 ≤ s by omega)))
        _ = (x : ℝ) := Real.rpow_one _
    exact_mod_cast (Nat.floor_le (by positivity)).trans hrpow_le
  have hx_rpow_ge : (x : ℝ) ≤ (x : ℝ) ^ (1 + ε) := by
    calc
      (x : ℝ) = (x : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (x : ℝ) ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
  have hzs_le_y : ⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ ^ s ≤ ⌈(x : ℝ) ^ (1 + ε)⌉₊ := by
    have h1 : ((⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ ^ s : ℕ) : ℝ) ≤ (x : ℝ) := by
      calc
        ((⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ ^ s : ℕ) : ℝ) =
            (⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ : ℝ) ^ s := by push_cast; rfl
        _ ≤ ((x : ℝ) ^ ((1 : ℝ) / (s : ℝ))) ^ s :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) s
        _ = (x : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
            one_div_mul_cancel hs_pos.ne', Real.rpow_one]
    have h2 : (x : ℝ) ≤ (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := hx_rpow_ge.trans (Nat.le_ceil _)
    exact_mod_cast h1.trans h2
  have hy_pos : (0 : ℝ) < (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := by
    have : (1 : ℝ) ≤ (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) :=
      hx_ge1.trans (hx_rpow_ge.trans (Nat.le_ceil _))
    linarith
  have hlow := hZ₀ _ hz_ge_Z₀ _ hzs_le_y a
  have hbuch : (((Icc 1 ⌈(x : ℝ) ^ (1 + ε)⌉₊).filter fun m =>
        ∀ p ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) =
      (((Icc 1 ⌈(x : ℝ) ^ (1 + ε)⌉₊).filter fun m =>
        ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) +
      ∑ q ∈ (Ioc ⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ x).filter Nat.Prime,
        (((Icc 1 ⌈(x : ℝ) ^ (1 + ε)⌉₊).filter fun m =>
          m ≡ a q [MOD q] ∧ ∀ p < q, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) := by
    exact_mod_cast OMA.R_Erdos687_erdos_687_parts_iii_R1.buchstab_identity _ x _ hzx a
  have herr : ((c / (2 * (8 * Real.exp 5))) / (s : ℝ) ^ 3) *
      (∏ p ∈ (range (⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ + 1)).filter Nat.Prime,
        (1 - (p : ℝ)⁻¹)) ≤
      (c / 2) * (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) := by
    have hfac_nn : 0 ≤ (c / (2 * (8 * Real.exp 5))) / (s : ℝ) ^ 3 := by positivity
    calc
      _ ≤ ((c / (2 * (8 * Real.exp 5))) / (s : ℝ) ^ 3) * ((8 * Real.exp 5) * (s : ℝ) ^ 3 *
            (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))) :=
        mul_le_mul_of_nonneg_left hRatio hfac_nn
      _ = _ := by
        have hs3_ne : (s : ℝ) ^ 3 ≠ 0 := by positivity
        field_simp
  have hmul := mul_le_mul_of_nonneg_left herr hy_pos.le
  have h1 : (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) *
      (∏ p ∈ (range (⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ + 1)).filter Nat.Prime,
        (1 - (p : ℝ)⁻¹)) -
      (c / 2) * (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) *
        (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) ≤
      (1 - (c / (2 * (8 * Real.exp 5))) / (s : ℝ) ^ 3) * (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) *
        (∏ p ∈ (range (⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊ + 1)).filter Nat.Prime,
          (1 - (p : ℝ)⁻¹)) := by
    linarith
  linarith

/-- Step `R1.H2` of part iii (Buchstab large-prime tail bound) is false. -/
theorem not_R1_H2 : ¬ OMA.R_Erdos687_erdos_687_parts_iii_R1.H2 := by
  rintro ⟨c, hc, s₀, _, hTail⟩
  obtain ⟨c₀, hc₀, hMert⟩ := OMA.Mertens687.mertens_lower
  obtain ⟨s, hs_ge, hs2, hFund⟩ := r1_H1 (c / (2 * (8 * Real.exp 5))) (by positivity) s₀
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp hFund
  obtain ⟨ε, hε0, _, hev⟩ := eventually_exists_shift (c / 2 * c₀) (by positivity)
  have hall : ∀ᶠ x : ℕ in atTop, False := by
    filter_upwards [eventually_ge_atTop (max 2 (max (10 ^ s) (Z₀ ^ s))),
      OMA.R_Erdos687_erdos_687_parts_iii_R1.chebyshev_eulerProd_ratio s hs2,
      hTail s hs_ge ε hε0, hev] with x hx hRatio hTailx hshift
    obtain ⟨M, hM⟩ := hshift
    have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
    have hx' : max 1 (max (10 ^ s) (Z₀ ^ s)) ≤ x :=
      max_le (by omega) (le_trans (le_max_right _ _) hx)
    have hlow := surv_lower_of_tail c ε hc hε0 s Z₀ x hs2 hZ₀ hx' hRatio
      (fun p => p - M % p) (hTailx _)
    rw [residue_card_eq_shift x _ M (fun p => p - M % p) (fun _ => rfl)] at hlow
    have hlx : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx2)
    have hV := hMert x hx2
    have hy0 : (0 : ℝ) ≤ (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := Nat.cast_nonneg _
    have h3 : c / 2 * c₀ * (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) / Real.log x ≤
        (c / 2) * (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) *
          (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) := by
      have h4 : c / 2 * c₀ * (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) / Real.log x =
          (c / 2) * (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) * (c₀ / Real.log x) := by ring
      rw [h4]
      exact mul_le_mul_of_nonneg_left hV (by positivity)
    linarith
  obtain ⟨x, hx⟩ := hall.exists
  exact hx

end E687Rankin

theorem OMA.disproof : ¬ OMA.R_Erdos687_erdos_687_parts_iii_R1.H2 :=
  E687Rankin.not_R1_H2
