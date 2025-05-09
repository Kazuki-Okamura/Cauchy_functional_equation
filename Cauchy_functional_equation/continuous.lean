import Mathlib

open Function
open Set

theorem Cauchy_functional_equation_continuous {f : ℝ → ℝ} (hf : Continuous f) (hceq : ∀(x y : ℝ), f (x+y) = f x + f y) : ∃(c : ℝ), ∀ (x : ℝ), f (x) = c * x := by
  have h1 : f (0:ℕ) = 0 := by
    have h1_1 : f ((0:ℕ)+(0:ℕ)) = f (0:ℕ) + f (0:ℕ) := by
      rw [← hceq (0:ℕ) (0:ℕ)]
    have h1_2 : f (0:ℕ) = f ((0:ℕ)+(0:ℕ)) := by
      simp
    have h1_3 : f (0:ℕ) = f (0:ℕ) + f (0:ℕ) := by
      rw [← h1_1]
      exact h1_2
    linarith
  have h2 : ∀(x : ℝ), f (x+1) = f x + f 1 := by
    exact fun x => hceq x 1
  have h2_1 : ∀(x : ℕ), f (x+ 1) = f x + f 1 := by
    exact fun x => hceq (↑x) 1
  have h3 : ∀(x : ℕ), f x = (f 1)*x := by
    intro x
    induction x with
    | zero =>
    rw [h1]
    ring
    | succ x ih =>
    have h3_1 :  (f 1)*(x+1) =  (f 1)*x + f 1 := by
      ring
    have h3_2 : f (x + 1) = f x + f 1 := by
      apply h2
    have h3_3 : f (x + 1) = (f 1)*x + f 1 := by
      rw [← ih]
      exact h3_2
    have h3_4 : f (x + 1) = (f 1)*(x+1) := by
      rw [h3_3]
      symm at h3_1
      exact h3_1
    rw [Nat.cast_add]
    simp
    exact h3_4
  have h4 : ∀(x : ℤ), f x = (f 1)*x := by
    intro x
    have h4_1 : f (- x) = - f x := by
      have h4_1_1 : f (-x) + f x = f ((-x)+x) := by
        rw [← hceq (-x) (x)]
      have h4_1_2 : f (-x) + f x = f (0:ℕ)  := by
        rw [h4_1_1]
        simp
      have h4_1_3 : f (-x) + f x = 0 := by
        rw [h4_1_2]
        apply h1
      linarith
    cases x with
    | ofNat n =>
      exact h3 n
    | negSucc n =>
      have h4_2 : f (-(n+1)) = - f (n+1) := by
        simp [Int.negSucc_eq] at h4_1
        symm at h4_1
        simp
        linarith
      have h4_3 : - f (n+1) = - (f 1) * (n+1) := by
        simp
        exact_mod_cast h3 (n+1)
      have h4_4 : f (-(n+1)) = - (f 1) * (n+1) := by
        apply Eq.trans h4_2 h4_3
      have h4_5 : -(n + 1) = (Int.negSucc n) := by
        exact rfl
      have h4_6 : f (-(n+1)) = f ( Int.negSucc n) := by
        rw [← h4_5]
        simp
      have h4_7 : - (f 1) * (n+1) = (f 1) * (-(n+1)) := by
        linarith
      have h4_8 : f (-(n+1)) = (f 1) * (-(n+1)) := by
        apply Eq.trans h4_4 h4_7
      have h4_9 : (f 1) * (-(n+1)) = (f 1) * ↑(Int.negSucc n) := by
        rw [← h4_5]
        simp
      have h4_10 : f (-(n+1)) = (f 1) * ↑(Int.negSucc n) := by
        apply Eq.trans h4_8 h4_9
      apply Eq.trans (symm h4_6) h4_10

  have h5 : ∀(m : PNat), ∀(n : ℕ), n * f (1/m) = f (n/m) := by
    intro m n
    induction n with
    | zero =>
      simp
      norm_cast at h1
      exact symm h1
    | succ n ih =>
      have h5_1 : (n+1) * f (1/m) = n * f (1/m) + f (1/m) := by
        ring
      have h5_2 : n * f (1/m) + f (1/m) = f (n/m) + f (1/m) := by
        rw [ih]
      have h5_3 : f (n/m) + f (1/m) = f (n/m + 1/m) := by
        rw [← hceq (n /m) (1 /m)]
      have h5_4 :  f (n/m + 1/m) = f ( (n+1)/m ) := by
        field_simp
      have h5_5 : (n+1) * f (1/m) = f (n/m) + f (1/m) := by
        apply Eq.trans h5_1 h5_2
      have h5_6 : f (n/m) + f (1/m) = f ( (n+1)/m ) := by
        apply Eq.trans h5_3 h5_4
      have h5_7 : (n+1) * f (1/m) = f ( (n+1)/m ) := by
        apply Eq.trans h5_5 h5_6
      norm_cast at h5_7
  have h6 : ∀(m : PNat), m * f (1/m) = f 1 := by
    intro m
    have h6_1 :  m * f (1/m) = f (m/m) := by
      exact h5 m m.1
    have hpos : m.1 ≠ 0 := Nat.pos_iff_ne_zero.mp m.property
    have hnz : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos
    have h6_2 : (m:ℝ) / m = 1 := by
      exact div_self hnz
    have h6_3 : f (m/m) = f 1 := by
      exact congrArg f h6_2
    apply Eq.trans h6_1 h6_3

  have h7 : ∀(m : PNat), ∀(n : ℕ), f (n/m) = (f 1) * (n/m) := by
    intro m n
    have h7_1 : f (n/m) = n * f (1/m) := by
      exact Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h5 m n)))
    have h7_2 : m * f (1/m) =  (f 1) := by
      exact h6 m
    have h7_3 : f (1/m) = (f 1) * (1/m) := by
      field_simp
      rw [mul_comm]
      exact h7_2
    have h7_4 : n * f (1/m) = n * ((f 1) * (1/m)) := by
      rw [← h7_3]
    have h7_5 : n * ((f 1) * (1/m)) = (f 1) * (n/m) := by
      field_simp
      rw [mul_comm]
    have h7_6 : n * f (1/m) = (f 1) * (n/m) := by
      apply Eq.trans h7_4 h7_5
    apply Eq.trans h7_1 h7_6

  have h8 : ∀(m : PNat), ∀(n : ℤ), f ( - (n/m) ) = - f (n/m) := by
    intros m n
    have h8_1 : f (-(n/m)) + f (n/m) = f ((-(n/m))+(n/m)) := by
      rw [← hceq (-(n/m)) (n/m)]
    have h8_2 : f (-(n/m)) + f (n/m) = f (0:ℕ)  := by
      rw [h8_1]
      simp
    have h8_3 : f (-(n/m)) + f (n/m) = 0 := by
      rw [h8_2]
      apply h1
    linarith

  have h9 : ∀(m : PNat), ∀(n : ℤ), f (n/m) = (f 1) * (n/m) := by
    intro m n
    cases n with
    | ofNat n =>
      exact h7 m n
    | negSucc n =>
      have h9_1 : f (((- (n+1))/m)) = - f ( (n+1)/m ) := by
        rw [neg_div]
        norm_cast
        exact h8 m (n+1)
      have h9_2 : - f ( (n+1)/m ) = - (f 1) * ((n+1)/m) := by
        simp
        norm_cast
        exact h7 m (n+1)
      have h9_3 : f (((- (n+1))/m)) = - (f 1) * ((n+1)/m) := by
        apply Eq.trans h9_1 h9_2
      simp [Int.negSucc_eq, neg_div] at h9_3
      simp
      rw [h9_3]
      ring

  have h10 :  ∀(x : ℚ), ∃(m: PNat), ∃(n : ℤ), x = n/m := by
    intro x
    use ⟨x.den, x.pos⟩, x.num
    simp
    exact Eq.symm (Rat.num_div_den x)

  have hq : ∀(x : ℚ), f x = (f 1) * x := by
    intro x
    have hq_1 : ∃(m: PNat), ∃(n : ℤ), x = n/m := by
      apply h10
    rcases hq_1 with ⟨m,n,eq⟩
    rw [eq]
    simp
    exact h9 m n

  have h_final : ∀(x : ℝ), f x = (f 1) * x := by
    let c := (f 1)
    intro x
    have hε : ∀ ε > 0, |f x - c * x| < ε := by
      intro ε εpos
      have εpos2 : ε/2 > 0 := by
        linarith
      have hfaε : ∀ a, ∀ ε > 0, ∃ δ > 0, ∀ y, dist y a < δ → dist (f y) (f a) < ε := by
        rw [← Metric.continuous_iff]
        exact hf
      obtain ⟨δ₁, δ₁pos, hδ₁⟩ := hfaε x (ε/2) εpos2
      have hcont_lin_x : ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → dist (c*y) (c*x) < ε := by
        intro ε εpos
        use ε / (|c|+1)
        have εpos3 : ε/ (|c|+1) > 0 := by
          field_simp
          positivity
        have hcont_lin_x_delta : ∀ y, dist y x < ε/ (|c|+1) → dist (c*y) (c*x) < ε := by
          intro y
          intro hass
          have ceq : dist (c*y) (c*x) = |c| * (dist y x) := by
            have ceq1 : dist (c*y) (c*x) = |c*y - c*x| := by
              exact rfl
            have ceq2 : |c*y - c*x| = |c*(y - x)| := by
              rw [abs_eq_abs]
              have ceq3 : c * y - c * x = c * (y - x) := by
                ring
              apply Or.inl ceq3
            have ceq4 : |c*(y - x)| = |c| * |y-x| := by
              exact abs_mul c (y - x)
            have ceq5 : |c| * |y-x| = |c| * (dist (y) (x)) := by
              exact rfl
            have ceq6 : dist (c*y) (c*x) =  |c*(y - x)| := by
              apply Eq.trans ceq1 ceq2
            have ceq7 : |c*(y - x)| = |c| * (dist (y) (x)) := by
              apply Eq.trans ceq4 ceq5
            apply Eq.trans ceq6 ceq7
          have cineq1 :  |c| * (dist (y) (x)) ≤ |c| * (ε / (|c|+1)) := by
            apply mul_le_mul_of_nonneg_left (le_of_lt hass) (abs_nonneg c)
          have cineq2 : |c| * (ε / (|c|+1)) < ε := by
            have cineq2_1 : |c| * (ε / (|c|+1)) = ε * (|c|/(|c|+1)) := by
              exact mul_div_left_comm |c| ε (|c| + 1)
            rw [cineq2_1]
            have cineq2_3 : ε - ε * (|c| / (|c| + 1)) = ε / (|c|+1) := by
              field_simp
              ring
            have cineq2_4 : ε - ε * (|c| / (|c| + 1))  > 0 := by
              rw [cineq2_3]
              exact εpos3
            nlinarith
          have cineq3 : |c| * (dist (y) (x))  < ε := by
            exact lt_of_le_of_lt cineq1 cineq2
          exact lt_of_eq_of_lt ceq cineq3
        apply And.intro εpos3 hcont_lin_x_delta
      obtain ⟨δ₂, δ₂pos, hδ₂⟩ := hcont_lin_x (ε/2) εpos2
      let δ := min δ₁ δ₂
      have δpos : δ > 0 := by
        exact lt_min δ₁pos δ₂pos
      have hxd : x - δ < x + δ := by
        linarith [δpos]
      obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hxd
      have qdist : |(q : ℝ) - x| < δ := by
        have qdist1 : (x - δ < q) ∧ (q < x + δ) := by
          apply And.intro hq₁ hq₂
        apply abs_lt.mpr
        rcases qdist1 with ⟨h1, h2⟩
        have hl : -δ < q - x := by
          exact lt_tsub_iff_left.mpr hq₁
        have hr : q - x < δ := by
          exact sub_left_lt_of_lt_add hq₂
        apply And.intro hl hr

      have eq3 : |f x - c * x| = |(f x - f (q : ℝ)) + (f (q : ℝ) - c * (q : ℝ)) + (c * (q : ℝ) - c * x)| := by
        have eq3_1 : f x - c * x = (f x - f (q : ℝ)) + (f (q : ℝ) - c * (q : ℝ)) + (c * (q : ℝ) - c * x) := by
          ring
        exact congrArg abs eq3_1

      have triineq1 : |(f x - f (q : ℝ)) + (f (q : ℝ) - c * (q : ℝ)) + (c * (q : ℝ) - c * x)| ≤ |f x - f (q : ℝ)| + |f (q : ℝ) - c * (q : ℝ)| + |c * (q : ℝ) - c * x| := by
        exact abs_add_three (f x - f ↑q) (f ↑q - c * ↑q) (c * ↑q - c * x)

      have triineq2 : |f x - f (q : ℝ)| + |f (q : ℝ) - c * (q : ℝ)| + |c * (q : ℝ) - c * x| = |f x - f (q : ℝ)| + |c * (q : ℝ) - c * x| := by
        have triineq2_1 : f (q : ℝ) = c * (q : ℝ)  := by
          apply hq q
        have triineq2_2 : f (q : ℝ) - c * (q : ℝ) = 0 := by
          linarith
        have triineq2_3 : |f (q : ℝ) - c * (q : ℝ)| = 0 := by
          rw[triineq2_2]
          exact abs_zero
        rw [triineq2_3]
        simp

      have triineq3 : |f (q : ℝ) - f x| < ε/2 := by
        have hδ₁_1 : dist (q : ℝ) x < δ₁ → dist (f (q : ℝ)) (f x) < ε / 2 := by
          exact hδ₁ q
        have hδ₁_2 : dist (q : ℝ) x < δ := by
          exact qdist
        have hδ₁_3 : δ ≤ δ₁ := by
          exact min_le_left δ₁ δ₂
        have hδ₁_4 : dist (q : ℝ) x < δ₁ := by
          exact gt_of_ge_of_gt hδ₁_3 qdist
        have hδ₁_5 : dist (f (q : ℝ)) (f x) < ε / 2 := by
          exact hδ₁ (↑q) hδ₁_4
        exact hδ₁_5

      have triineq3_1 : |f x  - f (q : ℝ)| < ε/2 := by
        have triineq3_1_1 : |f x  - f (q : ℝ)| =  |f (q : ℝ) - f x| := by
          exact abs_sub_comm (f x) (f ↑q)
        exact lt_of_eq_of_lt triineq3_1_1 triineq3

      have triineq4 : |c * (q : ℝ) - c * x| < ε/2 := by
        have hδ₂_1 : dist (q : ℝ) x < δ₂ → dist (c * (q : ℝ)) (c * x) < ε / 2 := by
          exact hδ₂ q
        have hδ₂_2 : dist (q : ℝ) x < δ := by
          exact qdist
        have hδ₂_3 : δ ≤ δ₂ := by
          exact min_le_right δ₁ δ₂
        have hδ₂_4 : dist (q : ℝ) x < δ₂ := by
          exact gt_of_ge_of_gt hδ₂_3 qdist
        have hδ₂_5 : dist (c * (q : ℝ)) (c * x) < ε / 2 := by
          exact hδ₂ (↑q) hδ₂_4
        exact hδ₂_5

      have triineq5 : |(f x - f (q : ℝ)) + (f (q : ℝ) - c * (q : ℝ)) + (c * (q : ℝ) - c * x)| ≤ |f x - f (q : ℝ)| + |c * (q : ℝ) - c * x| := by
        exact le_of_le_of_eq triineq1 triineq2

      have triineq6 : |f x  - f (q : ℝ)| + |c * (q : ℝ) - c * x| < ε/2 + ε/2 := by
        exact add_lt_add triineq3_1 triineq4

      have triineq7 : |(f x - f (q : ℝ)) + (f (q : ℝ) - c * (q : ℝ)) + (c * (q : ℝ) - c * x)| < ε/2 + ε/2 := by
        exact lt_of_le_of_lt triineq5 triineq6

      have triineq8 : |f x - c * x| < ε/2 + ε/2 := by
        exact lt_of_eq_of_lt eq3 triineq7

      simp at triineq8
      exact triineq8

    have final : f x - c * x = 0 := by
      by_contra ha
      have ha_pos : 0 < |f x - c * x| := abs_pos.2 ha
      have contra : |f x - c * x| < |f x - c * x| := hε |f x - c * x| ha_pos
      exact lt_irrefl _ contra

    have final2 : f x = c * x := by
      linarith
    exact final2
  use f 1
