import tactic
import analysis.special_functions.trigonometric
import measure_theory.interval_integral
import topology.basic
import data.finset
import .integrals

noncomputable theory
open_locale classical
open_locale big_operators
open interval_integral
open filter
open real

open_locale topological_space

/-!
#### The proof of Euler summation : ∑ 1/n^2 = π^2/6

## Strategy

1. Define sequences

  Aₙ = ∫ x in 0..π/2 (cos x)^(2*n) and
  Bₙ = ∫ x in 0..π/2 x^2 * (cos x)^(2*n).

2. Use integration by parts to prove recurrence formulas

  Aₙ₊₁ = (2 * n + 1) * (n+1) * Bₙ - 2*(n+1)^2 * Bₙ₊₁
    and
  Aₙ₊₁ = (2*n + 1) * (Aₙ - Aₙ₊₁)

3. Express 1/((n+1)^2) in terms of two consecutive ratios:

  1 / ((n +1)^2 = 2 * (Bₙ) / (Aₙ) - 2 * Bₙ₊₁ / Aₙ₊₁

4. The partial sums telescope and yield

  ∑ k=0..(n-1) 1 / ((k+1)^2 =  2 * B₀ / A₀ - 2 * Bₙ/Aₙ = π^2 / 6 - 2 * Bₙ/Aₙ

5.  Bound the error term using the fact that

  2/π * x ≤ sin x.

## References

Daniel Daners,
A short elementary proof of ...
Mathematics Magazine 85 (2012), 361-364. (MR 3007217, Zbl 1274.97037)

* <http://talus.maths.usyd.edu.au/u/daners/publ/abstracts/zeta2/>

## Tags

euler summation, number theory, reciprocals

-/

def A : ℕ → ℝ := λ n, ∫ x in 0..real.pi/2, (cos x)^(2*n)
def B : ℕ → ℝ := λ n, ∫ x in 0..real.pi/2, x^2 * (cos x)^(2*n)

/-
Evaluate A 0 and B 0, which will be useful later
-/
lemma eval_A0 : A 0 = real.pi / (2 : ℝ) :=
begin
  unfold A,
  simp only [mul_zero, pow_zero],
  suffices : ∫ (x : ℝ) in 0..real.pi / 2, (1:ℝ) = (real.pi / 2 - 0) • 1,
  {
    rw this,
    simp only [mul_one, algebra.id.smul_eq_mul, sub_zero],
  },
  apply interval_integral.integral_const,
end

lemma has_deriv_at_congr {f : ℝ → ℝ} {f' g' : ℝ} (x : ℝ) (h: f' = g') :
has_deriv_at f f' x → has_deriv_at f g' x :=
(iff_of_eq (congr_fun (congr_arg (has_deriv_at f) h) x)).1

lemma eval_B0 : B 0 = real.pi^3 / (24 : ℝ) :=
begin
  unfold B,
  simp only [mul_one, mul_zero, pow_zero],
  have h : ∀ x ∈ set.interval 0 (real.pi/2), has_deriv_at (λ (x:ℝ), x^3/3) (x^2) x,
  {
    intros x hx,
    have hh : (3⁻¹ * (3 * x ^ 2)) = x^2 := by discrete_field,
    suffices : has_deriv_at (λ (x : ℝ), x ^ 3 / 3) (3⁻¹ * (3 * x ^ 2)) x, by exact has_deriv_at_congr x hh this,
    simp [div_eq_mul_inv, mul_comm],
    apply has_deriv_at.const_mul,
    apply_mod_cast (has_deriv_at_pow 3 x),
  },
  rw integral_eq_sub_of_has_deriv_at h,
  { simp only [div_pow],
    ring },
  { show_continuous },
end

/-
Show that B n is positive for all n. A similar proof works to show that A n is positive,
but we decided to prove the latter one by induction, which we will do once we have
an explicit recursive formula for A n.

For B n, the proof just uses that the integrand is the square of a nonzero function.
-/
lemma B_pos {n : ℕ} : 0 < B n :=
begin
  unfold B,
  have pi_pos := pi_pos,
  simp only [mul_comm, pow_mul, ←mul_pow],
  apply int_pos_of_square (real.pi/3) pi_div_two_pos,
  { show_continuous },
  { -- Show here that the integrand is nonzero at π/3
    repeat {split},
    repeat {linarith},
    rw cos_pi_div_three,
    field_simp [pi_ne_zero],
  }
end

lemma first_lemma' (n : ℕ) : A (n + 1)= (2*(n:ℝ)+1) * ∫ x in 0..real.pi/2, ((sin x)^2 * (cos x)^(2*n)) :=
begin
  calc
  A (n + 1) = ∫ x in 0..real.pi/2, (cos x)^(2*(n+1)) : by {unfold A}
  ... =  ∫ x in 0..real.pi/2, (cos x)^(2*n+1) * (deriv sin x) :
  begin
    congr, ext1,
    rw real.deriv_sin,
    ring_nf,
  end
  ... = ∫ x in 0..real.pi/2, (2*n+1) * (sin x)^2 * (cos x)^(2*n) :
  begin
    rw int_by_parts,
    {
    suffices : ∫ x in 0..real.pi / 2,
    sin x * ((2*n + 1) * (cos x ^ (2 * n) * sin x)) =
    ∫ x in 0..real.pi / 2, (2*n + 1) * sin x^2 * cos x^(2 * n), by simpa,
      congr, ext1,
      ring,
    },
    { apply differentiable.pow,
      apply differentiable.cos,
      exact differentiable_id },
    { exact differentiable_sin },
    { exact continuous_deriv_cospow (2*n) },
    { rw real.deriv_sin,
      exact continuous_cos },
  end
  ... = ∫ x in 0..real.pi/2, (2*(n:ℝ)+1) * ((sin x)^2 * (cos x)^(2*n)) : by {congr, ext1, ring}
  ... = (2*(n:ℝ)+1) * ∫ x in 0..real.pi/2, ((sin x)^2 * (cos x)^(2*n)) : by {simp [my_integral_smul]}
end

lemma first_lemma (n : ℕ) : A (n + 1)  = (2*n + 1) * (A (n) - A (n+1)) :=
begin
  calc
  A (n + 1) = (2*(n:ℝ)+1) * ∫ x in 0..real.pi/2, ((sin x)^2 * (cos x)^(2*n)) : first_lemma' n
  ... = (2*(n:ℝ)+1) * ∫ x in 0..real.pi/2, (1- (cos x)^2) * (cos x)^(2*n) :
  begin
    congr, ext1,
    suffices : sin x^2 = 1 - cos x^2, rw this,
    simp only [eq_sub_iff_add_eq, sin_sq_add_cos_sq],
  end
  ... = (2*(n:ℝ)+1) * (A (n) - A (n+1)) :-- by {rw f5}
  begin
    unfold A,
    rw ←integral_sub,
    { congr, discrete_field },
    all_goals {
      apply integrable_of_cont,
      apply continuous.pow continuous_cos,
    },
  end
end

lemma first_lemma_cor (n : ℕ) : A (n+1) = (2 * n + 1) / (2 * n + 2) * A n :=
begin
  have h := first_lemma n,
  have h1 : 2 * (n : ℝ) + 1 ≠ 0 := by show_nonzero,
  have h2 : 2 * (n : ℝ) + 2 ≠ 0 := by show_nonzero,
  have h3 : 2 * (n : ℝ) + 2 = (2 * n + 1) + 1 := by ring,
  field_simp [h1, h2],
  rw [h3, mul_add, mul_one],
  nth_rewrite_lhs 1 h,
  ring,
end

/-
The recurrence formula for A n directly gives positivity by induction.
-/
lemma A_pos {n : ℕ} : 0 < A n :=
begin
  induction n with d hd,
  { rw eval_A0,
    exact pi_div_two_pos },
  { rw_mod_cast first_lemma_cor d,
    show_pos },
end
/-
-/
lemma display4 (n : ℕ) :
  A (n+1) = (2 * n + 1) * (n+1) * B n - 2*(n+1)^2 * B (n+1) :=
begin
  calc
  A (n + 1) = ∫ x in 0..real.pi/2, (cos x)^(2*(n+1)) : by {unfold A}
  ... = ∫ x in 0..real.pi/2, (cos x)^(2*n+2) * ((deriv id) x) : by {discrete_field}
-- Integrate by parts
  ... = -∫ x in 0..real.pi/2, x * (2*n+2) * (cos x)^(2*n+1) * (deriv cos) x :
  begin
    rw int_by_parts_zero_ends,
    { congr,
      discrete_field },
    all_goals
    {
      discrete_field,
      try {show_continuous}
    },
  end
  ... = ((n:ℝ)+1) * ∫ x in 0..real.pi/2, (2*x) * sin x * (cos x)^(2*n+1) :
  begin
    rw [←my_integral_smul, ←integral_neg],
    congr,
    discrete_field,
  end
  ... = (n+1) * ∫ x in 0..real.pi/2, sin x * (cos x)^(2*n+1) * deriv (λ x, x^2) x :
  begin
    congr, ext,
    simp only [mul_one, differentiable_at_id', deriv_pow'',
      nat.cast_bit0, deriv_id'', pow_one, nat.cast_one],
    linarith,
  end
-- Integrate by parts a second time
  ... = (n+1) * -∫ x in 0..real.pi/2, x^2 * (deriv (λ x, sin x * (cos x)^(2*n+1))) x :
  begin
    rw int_by_parts_zero_ends,
    { show_differentiable },
    { exact differentiable_pow },
    {
      rw deriv_sin_cos,
      apply continuous.sub;
      exact continuous_cospow',
    },
    all_goals {
      simp only [algebra.id.smul_eq_mul, pow_one,
      nat.cast_one, power_rule'', continuous_mul_left,
      sin_zero, zero_mul,
      cos_pi_div_two, zero_mul, add_eq_zero_iff, ne.def, not_false_iff,
      one_ne_zero, mul_zero, and_false, zero_pow'],
    },
  end
  ... = (n+1) * -∫ x in 0..real.pi/2,
    x^2 * ((cos x)^(2*n+2) - (2*n+1) * (1 - cos x^2) * (cos x)^(2*n)) :
  begin
    congr, ext, congr,
    discrete_field,
  end
  ... = (n+1) * ((2 *n + 1) * B n - 2*(n+1) * B (n+1)) :
  begin
    congr,
    unfold B,
    rw ←integral_neg,
    repeat {rw_mod_cast ←my_integral_smul,},
    rw ←integral_sub,
    {
      congr, ext,
      simp only [nat.cast_bit0, nat.cast_add, nat.cast_one, nat.cast_mul],
      ring_exp,
    },
    all_goals {
      apply integrable_of_cont,
      show_continuous,
    },
  end
  ... = (2 * n + 1) * (n+1) * B n - 2*(n+1)^2 * B (n+1) : by {ring}
end

lemma summand_expression (n : ℕ) :
  1 / ((n : ℝ) + 1)^2 = 2 * (B n) / (A n) - 2 * B (n+1) / A (n+1) :=
begin
  have A_nonzero : ∀ (m:ℕ), A m ≠ 0,
  {
    intro m,
    apply norm_num.ne_zero_of_pos,
    exact A_pos,
  },
  have nplusone_nonzero : (n:ℝ)+1 ≠ 0 := nat.cast_add_one_ne_zero n,
  have twonplusone_nonzero : 2*(n:ℝ)+1 ≠ 0,
    show_nonzero,
  have h_first_lemma := first_lemma n,
  calc
  1 / ((n : ℝ) + 1)^2 = (A (n+1)) / (A (n+1) * ((n : ℝ) + 1)^2) :
  begin
    rw div_mul_right,
    exact A_nonzero (n+1),
  end
  ... = ((2 * n + 1) * (n+1) * (B n) - 2*(n+1)^2 * (B (n+1))) / (A (n+1) * ((n : ℝ) + 1)^2) : 
    by {nth_rewrite 0 display4,}
  ... = ((2 * n + 1) * (n+1) * (B n)) / (A (n+1) * ((n : ℝ) + 1)^2) -
    (2*(n+1)^2 * (B (n+1))) / (A (n+1) * ((n : ℝ) + 1)^2) :
    by {rw sub_div}
  ... = ((2 * n + 1) * (B n)) / (A (n+1) * ((n : ℝ) + 1)) -
    2 * (B (n+1)) / (A (n+1)) : by {field_simp *, ring}
  ... = 2 * (B n) / (A n) - 2 * B (n+1) / A (n+1) :
  begin
    have : (A (n+1) * ((n:ℝ) + 1)) = (2*n + 1) / 2 * (A n) := by discrete_field,
    rw this,
    discrete_field,
  end
end

lemma telescoping (n : ℕ) : ∑ k in (finset.range n), (1 : ℝ) / ((k+1)^2) = 2 * B 0 / A 0 - 2 * B n / A n :=
begin
  simp only [summand_expression],
  exact finset.sum_range_sub' (λ k, 2 * (B k) / (A k)) n,
end

/-
The sin function is concave on the interval [0..pi/2].
-/
lemma sin_is_concave : concave_on (set.Icc 0 (real.pi/2)) sin :=
begin
  have h0 : -sin = λ y, -sin y := by refl,
  rw ←neg_convex_on_iff,
  apply convex_on_of_deriv2_nonneg (convex_Icc 0 (real.pi / 2)),
  { show_continuous },
  { show_differentiable },
  {
    simp only [h0],
    show_differentiable,
  },
  {
    intros x hx,
    replace hx : 0 ≤ x ∧ x ≤ real.pi / 2 := set.mem_Icc.mp (interior_subset hx),
    suffices : 0 ≤ deriv (deriv (-sin)) x, by simpa,
    simp only [h0],
    suffices : 0 ≤ sin x, by simpa,
    apply sin_nonneg_of_nonneg_of_le_pi;
    linarith,
  }
end

/-
Use concavity of sin on [0..pi/2] to bound it below.
-/
lemma bound_sin {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ real.pi / 2) : 2 / real.pi * x ≤ sin x :=
begin
  have h := sin_is_concave.2,
  dsimp at h,
  have pi_pos := pi_pos,
  have pi_nonzero := pi_ne_zero,
  have two_over_pi_pos : (0 :ℝ) < (2:ℝ) / real.pi := div_pos zero_lt_two pi_pos,
  have hzero : (0:ℝ) ∈ set.Icc 0 (real.pi / 2),
  {
    rw set.mem_Icc,
    split; linarith,
  },
  have hpi2 : real.pi / 2 ∈ set.Icc 0 (real.pi / 2),
  {
    rw set.mem_Icc,
    split; linarith,
  },
  replace h := h hzero hpi2,
  simp only [sin_zero, mul_one, zero_add, mul_zero, sin_pi_div_two] at h,
  have ha : 0 ≤ (1:ℝ) - 2 / real.pi * x,
  {
    simp only [sub_nonneg],
    refine (le_div_iff' two_over_pi_pos).mp _,
    simp only [one_div_div],
    exact hx2,
  },
  have hb : 0 ≤ 2 / real.pi * x := (zero_le_mul_left two_over_pi_pos).mpr hx1,
  replace h := h ha hb,
  simp only [forall_prop_of_true, sub_add_cancel] at h,
  suffices : 2 / real.pi * x * (real.pi / 2) = x,
  {
    rw this at h,
    exact h,
  },
  discrete_field,
end

lemma key_inequality {n : ℕ} {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ real.pi /2) :
  x ^ 2 * cos x ^ (2 * n) ≤ (real.pi ^ 2 / 4) • (sin x ^ 2 * cos x ^ (2 * n)) :=
begin
  have key := bound_sin hx1 hx2,
  have cospos : (cos x)^(2*n) ≥ 0,
  {
    rw [mul_comm, pow_mul],
    apply pow_two_nonneg,
  },
  have h : x^2 ≤ real.pi^2 / 4 * (sin x)^2,
  {
    rw [div_mul_eq_mul_div, div_le_iff pi_pos] at key,
    nlinarith,
  },
  dsimp,
  nlinarith,
end

lemma BA_aux {n : ℕ} :
  ∫ (x : ℝ) in 0..real.pi / 2, x ^ 2 * cos x ^ (2 * n) <
  ∫ (x : ℝ) in
    0..real.pi / 2,
    (real.pi ^ 2 / 4) * (sin x ^ 2 * cos x ^ (2 * n)) :=
begin
  have hsq2' : sqrt 2^2 = 2 := sq_sqrt zero_le_two,
  have hsq2 : sqrt 2 ^(2*n) = 2^n := by simp only [pow_mul, hsq2'],
  have pisqpos : 0 < real.pi^2 := pow_pos pi_pos 2,
  apply integral_strictly_monotone_of_cont,
  { show_continuous },
  { show_continuous },
  { exact pi_div_two_pos },
  { apply key_inequality },
  {
    use real.pi/4,
    repeat {split},
    all_goals { try { linarith [pi_pos]}},
    {
      simp only [cos_pi_div_four, sin_pi_div_four, hsq2, hsq2',
        algebra.id.smul_eq_mul, div_pow],
      rw [←mul_assoc, mul_lt_mul_right],
      all_goals {discrete_field},
    },
  }
end

lemma B_in_terms_of_A (n : ℕ) : B n < real.pi^2 / (8 * (n + 1)) * A n :=
begin      
  have hh := first_lemma_cor n,
  calc
  B n = ∫ x in 0..(real.pi/2), x^2 * (cos x)^(2*n) : by {refl}
  ... < ∫ x in 0..(real.pi/2), (real.pi^2/ 4) • ((sin x)^2 * (cos x)^(2*n)) : by {exact BA_aux}
  ... = (real.pi^2/4) * (A (n+1) / (2*n + 1)) : by {rw [interval_integral.integral_smul,first_lemma'], discrete_field }
  ... = (real.pi^2) / (8 * (n+1)) * (A n) : by {discrete_field}
end

lemma B_in_terms_of_A' (n : ℕ) : 2 * B n / A n < real.pi ^ 2 / (4 *(n + 1)) :=
begin
  have h2 : 0 < (2:ℝ) := zero_lt_two,
  calc
  2 * B n / A n = 2 * (B n / A n) : by {exact mul_div_assoc,}
  ... < 2 * (real.pi ^ 2 / (8 * (n + 1))) :
    by {simp only [mul_lt_mul_left h2, div_lt_iff A_pos, B_in_terms_of_A n]}
  ... = real.pi ^ 2 / (4 *(n + 1)) :  by {discrete_field}
end

/-
Bound the partial sums by a harmonic sequence.
-/
lemma error_estimate {n : ℕ}:
  (-real.pi^2/4/(n+1) + real.pi^2/6) ≤ (∑ k in finset.range n, ((1:ℝ)/ (k+1)^2))
    ∧
  (∑ k in finset.range n, ((1:ℝ)/ (k+1)^2)) ≤ real.pi^2/4/(n+1) + real.pi^2/6 :=
begin
  rw [telescoping n, eval_A0, eval_B0],
  have quo_pos : 0 < 2 * B n / A n,
  {
    rw mul_div_assoc,
    exact mul_pos zero_lt_two (div_pos B_pos A_pos),
  },
  have h := B_in_terms_of_A' n,
  have pi_ne_zero := pi_ne_zero,
  have : 2 * (real.pi ^ 3 / 24) / (real.pi / 2) = real.pi^2 / 6 := by {discrete_field},
  rw this,
  field_simp *,
  split,
  all_goals {apply le_of_lt},
  {
    calc (-(real.pi ^ 2 * 6) / (4 * (↑n + 1)) + real.pi ^ 2) / 6
      = -(real.pi^2 / (4*((n:ℝ) + 1))) + real.pi^2 / 6 : by {discrete_field}
    ... < -(2 * B n / A n) + real.pi^2 / 6 : by {linarith [h]}
    ... = (real.pi ^ 2 - 6 * (2 * B n) / A n) / 6 : by {ring_exp}
  },
  {
    calc (real.pi ^ 2 - 6 * (2 * B n) / A n) / 6
      =  real.pi ^ 2/ 6- (2 * B n / A n): by {discrete_field}
    ... <  real.pi ^ 2 / (4 * (↑n + 1)) + real.pi ^ 2 / 6 : by {nlinarith}
    ... = (real.pi ^ 2 * 6 / (4 * (↑n + 1)) + real.pi ^ 2) / 6 : by {discrete_field}
  }
end

lemma tendsto_const_div_add_at_top_nhds_0_nat {C : ℝ} :
  tendsto (λ n : ℕ, (C / ((n : ℝ) + 1))) at_top (𝓝 0) :=
suffices tendsto (λ n : ℕ, C / (↑(n + 1) : ℝ)) at_top (𝓝 0), by simpa,
(tendsto_add_at_top_iff_nat 1).2 (tendsto_const_div_at_top_nhds_0_nat C)

lemma limit_below : tendsto (λ (n:ℕ),-real.pi^2/4/(n+1) + real.pi^2/6) at_top (𝓝 (real.pi^2/6)) :=
begin
  nth_rewrite 0 ←zero_add (real.pi^2/6),
  apply tendsto.add_const,
  apply tendsto_const_div_add_at_top_nhds_0_nat,
end

lemma limit_above : tendsto (λ (n:ℕ), real.pi^2/4/(n+1) + real.pi^2/6) at_top (𝓝 (real.pi^2/6)) :=
begin
  nth_rewrite 0 ←zero_add (real.pi^2/6),
  apply tendsto.add_const,
  apply tendsto_const_div_add_at_top_nhds_0_nat,
end


theorem euler_summation : tendsto (λ (n:ℕ), (∑ k in finset.range n, ((1:ℝ)/ (k+1)^2))) at_top (nhds (real.pi^2 / 6)) :=
begin
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le limit_below limit_above,
  all_goals {rw pi.le_def, intro n},
  exact error_estimate.1,
  exact error_estimate.2,
end