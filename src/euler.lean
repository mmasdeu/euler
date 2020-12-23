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
open real
open filter
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
A short elementary proof of  ,
Mathematics Magazine 85 (2012), 361-364. (MR 3007217, Zbl 1274.97037)

* <http://talus.maths.usyd.edu.au/u/daners/publ/abstracts/zeta2/>

## Tags

euler summation, number theory, reciprocals

-/

def A : ℕ → ℝ := λ n, ∫ x in 0..pi/2, (cos x)^(2*n)
def B : ℕ → ℝ := λ n, ∫ x in 0..pi/2, x^2 * (cos x)^(2*n)

lemma eval_A0 : A 0 = pi / (2 : ℝ) :=
begin
    unfold A,
    simp only [mul_zero, pow_zero],
    suffices : ∫ (x : ℝ) in 0..pi / 2, (1:ℝ) = (pi / 2 - 0) • 1,
    {
        rw this,
        simp only [mul_one, algebra.id.smul_eq_mul, sub_zero],
    },
    apply interval_integral.integral_const,
end

lemma eval_B0 : B 0 = pi^3 / (24 : ℝ) :=
begin
    unfold B,
    simp only [mul_one, mul_zero, pow_zero],
    have hprim : (λ (x : ℝ), x^2) = deriv (λ (x:ℝ), x^3 /3),
    {
        ext,
        rw derivative_cube,
    },
    simp [hprim],
    rw ftc2,
        ring,
    {
        show_differentiable,
    },
    {
        rw ←hprim,
        exact continuous_pow 2,
    },
    {
        exact le_of_lt pi_div_two_pos,
    }
end

lemma B_pos {n : ℕ} : 0 < B n :=
begin
    unfold B,
    have pi_pos := pi_pos,
    simp only [mul_comm, pow_mul, ←mul_pow],
    apply int_pos_of_square,
        show_continuous,
        exact pi_div_two_pos,
    use pi / 4,
    repeat{split},
    repeat {linarith},
    have sqrt2_pos : 0 < sqrt 2,
    {
        rw sqrt_pos,
        exact zero_lt_two,
    },
    rw cos_pi_div_four,
    push_neg,
    split,
    {
        linarith,
    },
    {
        apply pow_ne_zero,
        linarith,
    }
end

lemma eval_first_term : 2 * B 0 / A 0 = pi^2 / 6 :=
begin
    rw [eval_A0, eval_B0],
    have hpi : pi ≠ 0 := pi_ne_zero,
    discrete_field,
end

lemma f1 (n : ℕ) : A (n+1) = ∫ x in 0..pi/2, (cos x)^(2*n+1) * (deriv sin x) :=
begin
    unfold A,
    congr,
    ext1,
    rw real.deriv_sin,
    ring,
end

lemma f2 (n : ℕ) : ∫ x in 0..pi/2, (cos x)^(2*n+1) * (deriv sin x) =
     ∫ x in 0..pi/2, (2*n+1) * (sin x)^2 * (cos x)^(2*n) :=
begin
    rw int_by_parts,
    {
        simp,
        congr,
        ext1,
        ring,
    },
    {
        exact le_of_lt pi_div_two_pos,
    },
    finish,
    exact differentiable_sin,
    exact continuous_deriv_cospow (2*n),
    {
        rw real.deriv_sin,
        exact continuous_cos,
    },
end

lemma f3aux {f : ℝ → ℝ} (c : ℝ) (hf : continuous f) : ∫ x in 0..pi/2, (c * f x) =
    c * ∫ x in 0..pi/2, f x :=
begin
    norm_num,
    refine integral_smul c,
end

lemma f3 (n : ℕ) : ∫ x in 0..pi/2, ((2*(n:ℝ)+1) * (sin x)^2 * (cos x)^(2*n)) =
    (2*(n:ℝ)+1) * ∫ x in 0..pi/2, ((sin x)^2 * (cos x)^(2*n)) :=
begin
    rw ←f3aux (2*(n:ℝ) + 1),
    {
        congr,
        ext1,
        ring,
    },
    exact (continuous_sin.pow 2).mul (continuous_cos.pow (2 * n)),
end

lemma f4 (n : ℕ) :  ∫ x in 0..pi/2, ((sin x)^2 * (cos x)^(2*n)) =
      ∫ x in 0..pi/2, ((1-(cos x)^2) * (cos x)^(2*n)) :=
begin
    congr,
    ext1,
    rw sin_to_cos,
end

lemma f5 (n : ℕ) : ∫ x in 0..pi/2, (1- (cos x)^2) * (cos x)^(2*n) = A(n) - A(n+1) :=
begin
    unfold A,
    rw ←integral_sub,
    {
        congr,
        ext1,
        discrete_field,
    },
    all_goals {
        apply integrable_of_cont,
        apply continuous.pow continuous_cos,
    },
end

lemma first_lemma' (n : ℕ) : A (n + 1)= (2*(n:ℝ)+1) * ∫ x in 0..pi/2, ((sin x)^2 * (cos x)^(2*n)) :=
begin
    calc
    A (n+1) = ∫ x in 0..pi/2, (cos x)^(2*n+1) * (deriv sin x) :  by {exact f1 n}
    ... = ∫ x in 0..pi/2, (2*n+1) * (sin x)^2 * (cos x)^(2*n): by {exact f2 n}
    ... = (2*(n:ℝ)+1) * ∫ x in 0..pi/2, ((sin x)^2 * (cos x)^(2*n)) : by {exact f3 n}
end

lemma first_lemma (n : ℕ) : A (n + 1)  = (2*n + 1) * (A (n) - A (n+1)) :=
begin
    calc
    A (n + 1) = (2*(n:ℝ)+1) * ∫ x in 0..pi/2, ((sin x)^2 * (cos x)^(2*n)) : first_lemma' n
    ... = (2*(n:ℝ)+1) * ∫ x in 0..pi/2, (1- (cos x)^2) * (cos x)^(2*n) : by {rw f4 n}
    ... = (2*(n:ℝ)+1) * (A (n) - A (n+1)) : by {rw f5 n}
end


lemma display3bis (n : ℕ) : (A (n+1) * ((n:ℝ) + 1)) = (2*n + 1) / 2 * (A n) :=
begin
    have h := first_lemma n,
    field_simp *,
    linarith,
end

lemma A_pos {n : ℕ} : 0 < A n :=
begin
    induction n with d hd,
    {
        rw eval_A0,
        exact pi_div_two_pos,
    },
    {
        have H := display3bis d,
        have hd1 : 0 < (d:ℝ) + 1,
        {
            norm_cast,
            exact nat.succ_pos d,
        },
        have hd2 : 0 < 2*(d:ℝ) + 1,
        {
            norm_cast,
            exact (2 * d).succ_pos,
        },
        nlinarith,
    },
end

lemma first_by_parts (n : ℕ) :
    A (n+1) = (n+1) * ∫ x in 0..pi/2, (2*x) * sin x * (cos x)^(2*n+1) :=
begin
    calc
    A (n+1) = ∫ x in 0..pi/2, (cos x)^(2*n+2) * 1 :
    begin
        unfold A,
        congr,
        ext,
        rw mul_one,
        congr,
    end
    ... = ∫ x in 0..pi/2, (cos x)^(2*n+2) * ((deriv id) x) : -- by {sorry}
    begin
        congr,
        ext,
        congr,
        rw deriv_id',
    end
    ... = -∫ x in 0..pi/2, x * (2*n+2) * (cos x)^(2*n+1) * (deriv cos) x : --by {sorry}
    begin
        rw int_by_parts_zero_ends,
        {
            congr, ext,
            suffices : x * ((2 * ↑n + 2) * cos x^(2 * n + 1) * sin x) =
                x * (2*↑n + 2) * cos x^(2 * n + 1) * sin x, by simpa,
            linarith,
        },
        {
            exact le_of_lt pi_div_two_pos,
        },
        {
            apply differentiable_cospow,
        },
        {
            exact differentiable_id,
        },
        {
            apply continuous_deriv_cospow,
        },
        {
            rw deriv_id',
            exact continuous_const,
        },
        all_goals {
            simp only [id.def, mul_zero, nat.succ_pos', cos_pi_div_two, true_or,
                zero_pow_eq_zero, mul_eq_zero],
        }
    end
    ... = ∫ x in 0..pi/2, -x * (2*n+2) * (cos x)^(2*n+1) * (deriv cos) x : by {discrete_field}
    ... = ((n:ℝ)+1) • ∫ x in 0..pi/2, (2*x) * sin x * (cos x)^(2*n+1) :
    begin
        rw_mod_cast ←my_integral_smul,
        congr,
        ext,
        discrete_field,
    end
    ... = (n+1) * ∫ x in 0..pi/2, (2*x) * sin x * (cos x)^(2*n+1) :
    begin
        simp only [algebra.id.smul_eq_mul],
    end
end

lemma display4 (n : ℕ) :
    A (n+1) = (2 * n + 1) * (n+1) * B n - 2*(n+1)^2 * B (n+1) :=
begin
    calc
    A (n+1) =  (n+1) * ∫ x in 0..pi/2, (2*x) * sin x * (cos x)^(2*n+1) : by {rw first_by_parts}
    ... = (n+1) * ∫ x in 0..pi/2, sin x * (cos x)^(2*n+1) * deriv (λ x, x^2) x : -- by {sorry}
    begin
        congr, ext,
        simp only [mul_one, differentiable_at_id', deriv_pow'',
            nat.cast_bit0, deriv_id'', pow_one, nat.cast_one],
        linarith,
    end
    ... = (n+1) * -∫ x in 0..pi/2, x^2 * (deriv (λ x, sin x * (cos x)^(2*n+1))) x : --by {sorry}
    begin
        rw int_by_parts_zero_ends,
        {
            exact le_of_lt pi_div_two_pos,
        },
        {
            show_differentiable,
        },
        {
            exact differentiable_pow,
        },
        {
            rw deriv_sin_cos',
            apply continuous.sub;
            exact continuous_cospow',
        },
        {
            rw_mod_cast derivative_square,
            exact continuous_mul_left 2,
        },
        {
            simp only [sin_zero, zero_mul],
        },
        {
            simp only [cos_pi_div_two, zero_mul, add_eq_zero_iff, ne.def, not_false_iff,
            one_ne_zero, mul_zero, and_false, zero_pow'],
        },
    end
    ... = (n+1) * -∫ x in 0..pi/2,
        x^2 * ((cos x)^(2*n+2) - (2*n+1) * (1 - cos x^2) * (cos x)^(2*n)) :
    begin
        congr, ext, congr,
        rw deriv_sin_cos',
        discrete_field,
    end
    ... = (n+1) * ((2 *n + 1) * B n - 2*(n+1) * B (n+1)) :
    begin
        congr,
        unfold B,
        rw ←integral_neg,
        repeat {rw_mod_cast ←my_integral_smul',},
        rw ←integral_sub,
        {
            congr, ext,
            generalize : cos x = C,
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
    have An_nonzero : A n ≠ 0,
    {
        apply norm_num.ne_zero_of_pos,
        exact A_pos,
    },
    have An1_nonzero : A (n+1) ≠ 0,
    {
        apply norm_num.ne_zero_of_pos,
        exact A_pos,       
    },
    have nplusone_nonzero : (n:ℝ)+1 ≠ 0,
    {
        exact nat.cast_add_one_ne_zero n,
    },
    have twonplusone_nonzero : 2*(n:ℝ)+1 ≠ 0,
        show_nonzero,
    have h_first_lemma := first_lemma n,
    calc
    1 / ((n : ℝ) + 1)^2 = (A (n+1)) / (A (n+1) * ((n : ℝ) + 1)^2) : --by {library_search,}
    begin
        rw div_mul_right,
        exact An1_nonzero,
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
        suffices : (A (n+1) * ((n:ℝ) + 1)) = (2*n + 1) / 2 * (A n),
        {
            rw this, discrete_field,
        },
        field_simp *,
        linarith,
    end
end

lemma telescoping (n : ℕ) : ∑ k in (finset.range n), (1 : ℝ) / ((k+1)^2) = 2 * B 0 / A 0 - 2 * B n / A n :=
begin
    simp only [summand_expression],
    exact finset.sum_range_sub' (λ k, 2 * (B k) / (A k)) n,
end


lemma sin_is_concave : concave_on (set.Icc 0 (pi/2)) sin :=
begin
    have h : deriv (- sin) = - cos,
    {
        rw ←real.deriv_sin,
        ext1,
        apply deriv.neg,
    },
    have h' : deriv (- cos) = sin,
    {
        funext,
        rw ←neg_neg sin,
        suffices : deriv (-cos) x = -(-sin x), by simp only [neg_neg, this],
        rw ←real.deriv_cos,
        apply deriv.neg,
    },
    rw ←neg_convex_on_iff,
    apply convex_on_of_deriv2_nonneg (convex_Icc 0 (pi / 2)),
    {
        show_continuous,
    },
    {
        show_differentiable,
    },
    {
        rw h,
        show_differentiable,
    },
    {
        intros x hx,
        suffices : 0 ≤ deriv (deriv (-sin)) x, by simpa,
        rw [h, h'],
        replace hx : 0 ≤ x ∧ x ≤ pi / 2 := set.mem_Icc.mp (interior_subset hx),
        apply sin_nonneg_of_nonneg_of_le_pi; linarith,
    }
end

lemma key_inequality {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ pi / 2) : 2 / pi * x ≤ sin x :=
begin
    have h := sin_is_concave.2,
    dsimp at h,
    have pi_pos := pi_pos,
    have pi_nonzero := pi_ne_zero,
    have two_over_pi_pos : (0 :ℝ) < (2:ℝ) / pi := div_pos zero_lt_two pi_pos,
    have hzero : (0:ℝ) ∈ set.Icc 0 (pi / 2),
    {
        rw set.mem_Icc,
        split; linarith,
    },
    have hpi2 : pi / 2 ∈ set.Icc 0 (pi / 2),
    {
        rw set.mem_Icc,
        split; linarith,
    },
    replace h := h hzero hpi2,
    simp only [sin_zero, mul_one, zero_add, mul_zero, sin_pi_div_two] at h,
    have ha : 0 ≤ (1:ℝ) - 2 / pi * x,
    {
        simp only [sub_nonneg],
        refine (le_div_iff' two_over_pi_pos).mp _,
        simp only [one_div_div],
        exact hx2,
    },
    have hb : 0 ≤ 2 / pi * x := (zero_le_mul_left two_over_pi_pos).mpr hx1,
    replace h := h ha hb,
    simp only [forall_prop_of_true, sub_add_cancel] at h,
    suffices : 2 / pi * x * (pi / 2) = x,
    {
        rw this at h,
        exact h,
    },
    discrete_field,
end

lemma B_in_terms_of_A (n : ℕ) : B n < pi^2 / (8 * (n + 1)) * A n :=
begin          
    have h : 2 * (n : ℝ) + 1 ≠ 0, show_nonzero,
    have h2 : 2 * (n : ℝ) + 2 ≠ 0, show_nonzero,
    have pi_pos := pi_pos,
    have pisqpos : 0 < pi^2 := pow_pos pi_pos 2,
    have hsq2' : sqrt 2^2 = 2 := sqr_sqrt zero_le_two,
    have hsq2 : sqrt 2 ^(2*n) = 2^n,
    {
        rw pow_mul,
        rw hsq2',
    },
    calc
    B n = ∫ x in 0..(pi/2), x^2 * (cos x)^(2*n) : by {refl,}
    ... < ∫ x in 0..(pi/2), (pi^2/ 4) • ((sin x)^2 * (cos x)^(2*n)) :
    begin

        apply integral_strictly_monotone_of_cont,
        {
            show_continuous,
        },
        {
            show_continuous,
        },
        {
            exact pi_div_two_pos,
        },
        {
            intros x hx1 hx2,
            have key := key_inequality hx1 hx2,
            have cospos : (cos x)^(2*n) ≥ 0,
            {
                rw [mul_comm, pow_mul],
                apply pow_two_nonneg,
            },
            have h : x^2 ≤ pi^2 / 4 * (sin x)^2,
            {
                rw [div_mul_eq_mul_div, div_le_iff pi_pos] at key,
                nlinarith,
            },
            dsimp,
            nlinarith,
        },
        {
            use pi/4,
            repeat {split},
            {
                linarith [pi_pos],
            },
            {
                linarith [pi_pos],
            },
            {
                simp [cos_pi_div_four,sin_pi_div_four],
                repeat {rw hsq2 n},
                rw hsq2',
                rw ←mul_assoc,
                rw mul_lt_mul_right,
                {
                    discrete_field,
                    linarith [pisqpos],
                },
                {
                    discrete_field,
                    norm_num,
                    rw mul_comm,
                    rw pow_mul,
                    rw hsq2',
                    norm_num,
                },
            },
        }
    end
    ... = (pi^2/4) • ∫ x in 0..(pi/2), (sin x)^2 * (cos x)^(2*n) : by {rw interval_integral.integral_smul}
    ... = (pi^2/4) • (A (n+1) / (2*n + 1)) :
    begin
        rw first_lemma',
        discrete_field,
    end
    ... = (pi^2/4) • ((A n) / (2*n + 2)) :
    begin
        have hh := first_lemma n,
        simp only [nat.succ_pos', div_eq_zero_iff, algebra.id.smul_eq_mul,
            mul_eq_mul_left_iff, pow_eq_zero_iff],
        left,
        field_simp *,
        linarith,
    end
    ... = (pi^2) / (8 * (n+1)) * (A n) :
    begin
        field_simp,
        suffices : ((2 * n + 2) * 4) = 8 * (n+1),
        {
            rw_mod_cast this,
            discrete_field,
            linarith,
        },
        discrete_field,
    end
end

example {n:ℕ} : 0 < (pi ^ 2 * 6 / (4 * (n + 1)) + pi ^ 2) / 6 :=
begin
    have pi_pos := pi_pos,
    have h : 0 < 4*((n:ℝ)+1),
    {norm_cast, linarith,},
    have h6 : 0 < 6 := by norm_num,
    have pi2 : 0 < pi^2 * 6,
    {
        nlinarith,
    },
    have H : 0 < pi ^ 2 * 6 / (4 * (↑n + 1)),
    {
        apply div_pos,
        {
            linarith,
        },
        {
            exact h,
        },
    },
    linarith,
end

lemma error_estimate {n : ℕ}:
    (-pi^2/4/(n+1) + pi^2/6) ≤ (∑ k in finset.range n, ((1:ℝ)/ (k+1)^2))
        ∧
    (∑ k in finset.range n, ((1:ℝ)/ (k+1)^2)) ≤ pi^2/4/(n+1) + pi^2/6 :=
begin
    rw [telescoping n, eval_A0, eval_B0],
    have  h := B_in_terms_of_A n,
    have hpos : 0 < (n:ℝ) + 1,
    {
        norm_cast,
        exact nat.succ_pos n,
    },
    
    have quo_pos : 0 < 2 * B n / A n,
    {
        rw mul_div_assoc,
        exact mul_pos zero_lt_two (div_pos B_pos A_pos),
    },
    replace h : B n / A n < pi ^ 2 / (8 * (↑n + 1)),
        exact (div_lt_iff A_pos).mpr h,
    replace h : 2 * B n / A n < pi ^ 2/(4*(↑n + 1)),
    {
        have h2 : 0 ≤ (2:ℝ) := zero_le_two,
        calc
        2 * B n / A n = 2 * (B n / A n) : by {exact mul_div_assoc,}
        ... < 2 * (pi ^ 2 / (8 * (↑n + 1))) : by {linarith}
        ... = pi ^ 2 / (4 *(↑n + 1)) :  by {discrete_field}
    },
    have pi_ne_zero := pi_ne_zero,
    have pi_ne_zero' : 24 * pi ≠ 0, show_nonzero,
    have : 2 * (pi ^ 3 / 24) / (pi / 2) = pi^2 / 6, by discrete_field,
    rw this,
    have pi_pos := pi_pos,
    have hhh : 0<4 * ((n:ℝ) + 1),
    {
        norm_cast,
        linarith,
    },
    field_simp *,
    split,
    {
        apply le_of_lt,
        calc
        (-(pi ^ 2 * 6) / (4 * (↑n + 1)) + pi ^ 2) / 6
            = -(pi^2 / (4*((n:ℝ) + 1))) + pi^2 / 6 : by {discrete_field}
        ... < -(2 * B n / A n) + pi^2 / 6 : by {linarith [h]}
        ... = (pi ^ 2 - 6 * (2 * B n) / A n) / 6 : by {ring_exp}
    },
    {
       apply le_of_lt,
       calc
       (pi ^ 2 - 6 * (2 * B n) / A n) / 6 =
        pi ^ 2/ 6- (2 * B n / A n): by {discrete_field}
       ... < pi^2/6 : by {linarith}
       ... <  pi ^ 2 / (4 * (↑n + 1)) + pi ^ 2 / 6 : by {nlinarith}
       ... = (pi ^ 2 * 6 / (4 * (↑n + 1)) + pi ^ 2) / 6 :
        by {discrete_field,}
    }
end

lemma tendsto_const_div_add_at_top_nhds_0_nat {C : ℝ} :
  tendsto (λ n : ℕ, (C / ((n : ℝ) + 1))) at_top (𝓝 0) :=
suffices tendsto (λ n : ℕ, C / (↑(n + 1) : ℝ)) at_top (𝓝 0), by simpa,
(tendsto_add_at_top_iff_nat 1).2 (tendsto_const_div_at_top_nhds_0_nat C)

lemma limit_below : tendsto (λ (n:ℕ),-pi^2/4/(n+1) + pi^2/6) at_top (𝓝 (pi^2/6)) :=
begin
    nth_rewrite 0 ←zero_add (pi^2/6),
    apply tendsto.add_const,
    apply tendsto_const_div_add_at_top_nhds_0_nat,
end

lemma limit_above : tendsto (λ (n:ℕ), pi^2/4/(n+1) + pi^2/6) at_top (𝓝 (pi^2/6)) :=
begin
    nth_rewrite 0 ←zero_add (pi^2/6),
    apply tendsto.add_const,
    apply tendsto_const_div_add_at_top_nhds_0_nat,
end


theorem euler_summation : tendsto (λ (n:ℕ), (∑ k in finset.range n, ((1:ℝ)/ (k+1)^2))) at_top (nhds (pi^2 / 6)) :=
begin
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le limit_below limit_above,
    all_goals {rw pi.le_def, intro n},
    exact error_estimate.1,
    exact error_estimate.2,
end