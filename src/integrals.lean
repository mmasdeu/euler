import tactic
import measure_theory.interval_integral
import measure_theory.lebesgue_measure
import measure_theory.set_integral
import analysis.calculus.deriv
import analysis.special_functions.exp_log
import analysis.special_functions.trigonometric
import data.finset

noncomputable theory
open_locale classical
open_locale big_operators
open measure_theory
open interval_integral
open set
open real

namespace tactic.interactive

meta def show_continuous := `[
  apply_rules [
    continuous_on.neg,
    continuous.continuous_on,
    continuous.neg,
    continuous_id,
    continuous_sin,
    continuous_cos,
    continuous_const,
    continuous.pow,
    continuous.mul,
    continuous.smul,
    continuous.sub,
    continuous.add
    ] 5,
  all_goals {try {norm_num}}
]

meta def show_differentiable := `[
  apply_rules [
    differentiable.differentiable_on,
    differentiable.neg,
    differentiable.smul,
    differentiable.cos,
    differentiable.sin,
    differentiable_const,
    differentiable_id,
    differentiable.mul,
    differentiable_fpow
    ] 10,
  all_goals {try {norm_num}}
]

meta def show_nonzero := `[
  apply_rules [
    mul_ne_zero,
    sub_ne_zero.2,
    ne_of_gt,
    ne_of_lt
    ] 20,
  all_goals {try {norm_cast}, try {norm_num}}
]

meta def clear_denoms := `[
  try {rw div_eq_div_iff},
  try {rw eq_div_iff},
  try {symmetry, rw eq_div_iff},
  try { ring_exp },
  all_goals {show_nonzero}
]

meta def discrete_field := `[
  try {field_simp},
  try {clear_denoms},
  try {ring_exp}
]

end tactic.interactive

lemma integrable_of_cont {f : ℝ → ℝ} (a b : ℝ) (h : continuous f):
    interval_integrable f measure_theory.measure_space.volume a b :=
begin
    have hmeas : measurable f := continuous.measurable h,
    have hconton : continuous_on f (interval a b) := continuous.continuous_on h,
    apply continuous_on.interval_integrable hconton hmeas,
    exact real.locally_finite_volume,
end

/-
This lemma was taken directly from <https://github.com/jjaassoonn/transcendental>
-/
lemma ftc1 (f : ℝ -> ℝ) {hf : measurable f} {hf2 : continuous f}
(a b : ℝ) (h : a ≤ b)
{hf3 : measure_theory.integrable_on f (Icc a b)}
(x0 : ℝ) (hx0 : x0 ∈ Icc a b) : 
  has_deriv_at (λ (b : ℝ), ∫ (x : ℝ) in a..b, f x) (f x0) x0 :=
begin
  apply integral_has_deriv_at_of_tendsto_ae_right,
  {
    exact integrable_of_cont a x0 hf2,
  },
  {
      apply filter.tendsto_inf_left,
      exact continuous.tendsto hf2 x0,
  },
end

theorem ftc2 (F : ℝ → ℝ) {hF : differentiable ℝ F} 
 {hf1 : continuous (deriv F)}
(a b : ℝ) (h : a ≤ b) : (∫ x in a..b, deriv F x) = F b - F a :=
begin
  have hf := continuous.measurable hf1,
  by_cases hab : (a = b),
  rw hab, simp only [interval_integral.integral_same, sub_self],

  set G := (λ x, (∫ t in a..x, deriv F t)) with hG,
  have prop := ftc1 (deriv F) a b h,
  rw ←hG at prop,
  have hG1 : differentiable_on ℝ G (Icc a b),
  {
    intros x hx,
    have prop2 := ftc1 (deriv F) a b h x hx,
    refine differentiable_at.differentiable_within_at _,
    rw hG,
    exact has_deriv_at.differentiable_at prop2,
    {
        exact hf,
    },
    {
        exact hf1,
    },
    apply continuous.integrable_on_compact compact_Icc hf1,
    exact real.locally_finite_volume,
  },
  have H : (Icc a b).indicator (deriv G) = (Icc a b).indicator (deriv F),
  {
    apply indicator_congr,
    intros x0 hx0,
    replace prop := prop x0 hx0,
    exact has_deriv_at.deriv prop,
  },

  replace H : ∀ y ∈ Icc a b, (deriv (F - G)) y = 0,
  {
    intros y hy,
    change deriv (λ t, F t - G t) y = 0,
    rw deriv_sub, rw sub_eq_zero,

    have eq1 : (Icc a b).indicator (deriv F) y = deriv F y,
    exact if_pos hy, rw <-eq1,
    have eq2 : (Icc a b).indicator (deriv G) y = deriv G y,
    exact if_pos hy, rw <-eq2, exact congr_fun H.symm y,

    dsimp only [],
    exact hF y,

    dsimp only [],
    exact has_deriv_at.differentiable_at (prop y hy),
  },

  have key : ∀ y ∈ Ioc a b, (F - G) y = (F - G) a,
  {
    intros y hy,
    have ineq : a < y, simp only [mem_Ioc] at hy, exact hy.1,
    have key := exists_deriv_eq_slope (F - G) ineq _ _,
    rcases key with ⟨c, hc, hc2⟩,
    have hc' : c ∈ Icc a b, 
      simp only [mem_Icc, mem_Ioc, mem_Ioo] at hy ⊢ hc,
      split, linarith, linarith,
    rw H c hc' at hc2,
    replace hc2 := eq.symm hc2,
    rw div_eq_zero_iff at hc2,
    cases hc2, exact sub_eq_zero.mp hc2,
    simp only [mem_Icc, mem_Ioc, mem_Ioo] at hy ⊢ hc, linarith,

    apply continuous_on.sub,
    simp only [], apply continuous.continuous_on,
    apply differentiable.continuous hF,

    have hG1' : continuous_on G (Icc a b),
      apply differentiable_on.continuous_on hG1,
    simp only [], apply continuous_on.mono hG1',
    apply Icc_subset_Icc, exact le_refl a, exact hy.2,

    apply differentiable_on.sub,
    simp only [], exact differentiable.differentiable_on hF,
    simp only [], apply differentiable_on.mono hG1,
    intros z hz, 
    simp only [mem_Icc, mem_Ioc, mem_Ioo] at *,
    split, linarith, linarith,
  },
  have G_a : G a = 0, by simp only [hG, interval_integral.integral_same],
  have G_b : G b = ∫ x in a .. b, (deriv F) x, by rw hG,
  rw ←G_b,
  have eq : G b = G b - 0, rw sub_zero, rw eq, rw <-G_a,
  rw sub_eq_sub_iff_sub_eq_sub,
  suffices : F b - G b = F a - G a, linarith,
  replace key := key b _,
  simp only [pi.sub_apply] at key ⊢, exact key,
  simp only [mem_Icc, mem_Ioc, mem_Ioo] at *,
  split, exact lt_of_le_of_ne h hab, exact le_refl b,

  exact hf, exact hf1,
  apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) hf1),
  exact subset.rfl,
  exact real.locally_finite_volume,
end


lemma self_mem_ae_restrict
  {s : set ℝ} (hs : is_measurable s):
  s ∈ (measure.restrict measure_space.volume s).ae :=
begin
  rw ae_restrict_eq hs,
  simp only [exists_prop, filter.mem_principal_sets, filter.mem_inf_sets],
  exact ⟨univ, filter.univ_mem_sets, s, by simp⟩,
end

lemma nonempty_inter_of_nonempty_inter_closure {α : Type*} [topological_space α] {s t : set α}
  (hs : is_open s) (h : (s ∩ closure t).nonempty) : (s ∩ t).nonempty :=
let ⟨x, xs, xt⟩ := h in _root_.mem_closure_iff.1 xt s hs xs

lemma real.volume_pos_of_is_open_of_nonempty {s : set ℝ} (h : is_open s) (h' : s.nonempty) :
  0 < volume s :=
begin
  rcases h' with ⟨x, hx⟩,
  have : ∀ᶠ (y : ℝ) in nhds x, y ∈ s := filter.eventually_of_mem (mem_nhds_sets h hx) (λ y H, H),
  exact filter.eventually.volume_pos_of_nhds_real this,
end

theorem integral_strictly_pos_of_cont (f : ℝ → ℝ) (a b : ℝ)
    (hf : continuous f)
    (hab : a < b)
    (h : ∀ (x : ℝ), a ≤ x → x ≤ b → 0 ≤ f x)
    (hneq: ∃ x, a ≤ x ∧ x ≤ b ∧ 0 < f x) :
    0 < ∫ x in a..b, f x :=
begin
  rw integral_pos_iff_support_of_nonneg_ae',
  { refine ⟨hab, _⟩,
    let s := {b : ℝ | 0 < f b},
    have s_open : is_open s := is_open_lt continuous_const hf,
    have : (s ∩ closure (Ioo a b)).nonempty,
    { rw closure_Ioo hab,
      rcases hneq with ⟨x, ax, xb, fxpos⟩,
      have : x ∈ s ∩ Icc a b := ⟨fxpos, ax, xb⟩,
      exact nonempty_of_mem this },
    have : (s ∩ Ioo a b).nonempty := nonempty_inter_of_nonempty_inter_closure s_open this,
    have : 0 < volume (s ∩ Ioo a b) :=
      real.volume_pos_of_is_open_of_nonempty (is_open_inter s_open is_open_Ioo) this,
    refine this.trans_le (measure_mono (λ x hx, _)),
    split,
    { exact ne_of_gt (show 0 < f x, from hx.1) },
    { exact ⟨hx.2.1, hx.2.2.le⟩ } },
  { have : Ioc b a = ∅ := Ioc_eq_empty hab.le,
    simp only [this, union_empty],
    exact filter.eventually_of_mem
      (self_mem_ae_restrict is_measurable_Ioc) (λ x hx, h x hx.1.le hx.2) },
  { exact integrable_of_cont a b hf }
end


theorem integral_strictly_monotone_of_cont (f g : ℝ → ℝ) (a b : ℝ)
    (hf : continuous f) (hg : continuous g)
    (hab : a < b)    
    (h : ∀ (x : ℝ), a ≤ x → x ≤ b → f x ≤ g x)
    (hneq: ∃ x, a ≤ x ∧ x ≤ b ∧ f x < g x) :
    ∫ x in a..b, f x < ∫ x in a..b, g x := 
begin
    suffices : 0 < ∫ x in a..b, (g - f) x,
    {
        simp at this,
        rw interval_integral.integral_sub at this,
        {
            rw sub_pos at this,
            apply this,
        },
        exact integrable_of_cont a b hg,
        exact integrable_of_cont a b hf,
    },
    apply integral_strictly_pos_of_cont (g-f),
    {
        exact continuous.sub hg hf,
    },
    {
        exact hab,
    },
    {
        simp [sub_pos],
        exact h,
    },
    {
        simp [sub_pos],
        exact hneq,
    },
end

lemma int_pos_of_pos_function (f : ℝ → ℝ) {a b : ℝ} (hf : continuous f)
(hab : a < b)
(hnonneg : ∀ x, a ≤ x → x ≤ b → 0 ≤ f x) :
    (∃ x, a ≤ x ∧ x ≤ b ∧ 0 < f x) → 0 < ∫ x in a..b, f x :=
begin
    intro hx,
    have hg : ∫ x in a..b, (0:ℝ) = 0 := integral_zero,
    rw ←hg,
    have hgcont : continuous (λ (x:ℝ), (0:ℝ)) := continuous_const,
    apply integral_strictly_monotone_of_cont (λ x, (0:ℝ)) f a b hgcont hf hab hnonneg hx,
end

lemma int_pos_of_square (f : ℝ → ℝ) (hf : continuous f) {a b : ℝ}
    (hab : a < b) :
    (∃ x, a ≤ x ∧ x ≤ b ∧ f x ≠ 0) → 0 < ∫ x in a..b, (f x)^2 :=
begin
    intro h,
    cases h with x hx,
    apply int_pos_of_pos_function,
    {
        show_continuous,
    },
    {
        exact hab,
    },
    {
        intros x hx1 hx2,
        exact pow_two_nonneg (f x),
    },
    {
        use x,
        have hy := pow_two_pos_of_ne_zero (f x) hx.2.2,
        exact ⟨hx.1, hx.2.1, hy⟩,
    }
end

theorem my_integral_smul (f : ℝ → ℝ) (a b c : ℝ) :
    ∫ x in a..b, c • (f x) = c • ∫ x in a..b, f x :=
begin
    rw_mod_cast interval_integral.integral_smul,
end

theorem my_integral_smul' (f : ℝ → ℝ) (a b c : ℝ) :
    ∫ x in a..b, c * (f x) = c * ∫ x in a..b, f x :=
begin
    dsimp,
    apply my_integral_smul,
end


theorem product_rule {f g : ℝ → ℝ} (hdf : differentiable ℝ f) (hdg : differentiable ℝ g) :
    deriv (f * g) = (deriv f) * g + f * deriv g :=
begin
    ext,
    have hdf0 : differentiable_at ℝ f x := hdf x,
    have hdg0 : differentiable_at ℝ g x := hdg x,
    apply deriv_mul hdf0 hdg0,
end

theorem differentiable_mul {f g : ℝ → ℝ} (hf : differentiable ℝ f) (hg : differentiable ℝ g) :
    differentiable ℝ (f * g) :=  differentiable.mul hf hg

theorem differentiable_fpow {f : ℝ → ℝ} {n : ℕ} :
    differentiable ℝ f → differentiable ℝ (f^n) :=
begin
    induction n with d hd,
    {
        intro h,
        simp only [pow_zero],
        exact differentiable_const 1,
    },
    {
        intro h,
        specialize hd h,
        rw pow_succ,
        apply differentiable_mul,
        repeat {assumption},
    }
end

theorem power_rule {f : ℝ → ℝ} {n : ℕ} (hfd : differentiable ℝ f):
    deriv (f^(n+1)) = ((n : ℝ) + 1) • f^n * (deriv f) := 
begin
    induction n with d hd, by norm_num,
    have H : f^(d+1) = f^d * f := pow_succ' f d,
    calc
        deriv (f^(d.succ+1)) = deriv (f^(d.succ) * f) : by {rw pow_succ' f (d.succ),}
        ... = (deriv (f^(d.succ))) * f + f^(d+1) * (deriv f) :
        begin
            rw product_rule,
            exact differentiable_fpow hfd,
            exact hfd,
        end
        ... = ((d:ℝ) + 1) • f^d * deriv f * f + f^d.succ * deriv f : by {rw hd}
        ... = ((d:ℝ) + 1) • (f^(d.succ)) * deriv f + f^(d.succ) * deriv f :
        begin
            simp only [add_left_inj, H],
            norm_num,
            rw mul_assoc,
            nth_rewrite_lhs 1 mul_comm,
            rw ←mul_assoc,
        end
        ... = ((d.succ:ℝ) + 1) • (f^(d.succ)) * deriv f :
        begin
            simp only [nat.cast_succ, algebra.smul_mul_assoc],
            nth_rewrite 1 add_smul,
            rw one_smul,
        end
end

lemma pow_fun_def {f : ℝ → ℝ} {n : ℕ} : f^n = λ x, (f x)^n :=
begin
    induction n with d hd,
    all_goals {
        try {rw [pow_succ, hd]},
        refl,
    }
end

lemma pow_deriv_fun_def {f : ℝ → ℝ} {n : ℕ} : ((n : ℝ) + 1) • f^n * (deriv f) =
    λ (x : ℝ), ((n : ℝ) + 1) • ((f x)^n * deriv f x) :=
begin
    rw pow_fun_def,
    simp only [algebra.id.smul_eq_mul, algebra.smul_mul_assoc],
    refl,
end

theorem power_rule'  {f : ℝ → ℝ} (n : ℕ) (hfd : differentiable ℝ f):
    deriv (λ (x : ℝ), (f x)^(n + 1)) = λ (x : ℝ), ((n : ℝ) + 1) • ((f x)^n * deriv f x) :=
begin
    rw [←pow_fun_def, ←pow_deriv_fun_def],
    exact power_rule hfd,
end

theorem power_rule'' (n : ℕ) :
    deriv (λ (x : ℝ), x^(n + 1)) = λ (x : ℝ), ((n : ℝ) + 1) • (x^n) :=
begin
    have hfd : differentiable ℝ (λ (x:ℝ), (x:ℝ)) := differentiable_id',
    have deriv_id_my : deriv (λ x, x) = λ (x : ℝ), (1:ℝ) := deriv_id',
    have H := power_rule' n hfd,
    rw deriv_id_my at H,
    rw H,
    simp only [mul_one, algebra.id.smul_eq_mul],
end

lemma derivative_square : deriv (λ (x : ℝ), x^2 ) = λ x, 2 * x :=
begin
    rw power_rule'' 1,
    dsimp,
    norm_num,
end

lemma derivative_cube (x : ℝ) : deriv (λ (x : ℝ), x^3 / 3) x = x^2 :=
begin
    rw deriv_div_const differentiable_at_pow,
    rw power_rule'' 2,
    dsimp,
    ring,
end

theorem int_by_parts (u v : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (hu : differentiable ℝ u)
    (hv : differentiable ℝ v) (hcu : continuous(deriv u)) (hcv : continuous(deriv v)) :
∫ x in a..b, u x * deriv v x =
    u b * v b - u a * v a - ∫ x in a..b,  v x * deriv u x := 
begin
    
    have huv : deriv (u * v) = (deriv u) * v + u * deriv v := product_rule hu hv,
    have H : ∫ x in  a..b, ((deriv u) x) * (v x)  + (u x) * ((deriv v) x) = ∫ x in a..b, (deriv (u*v)) x,
    {
        congr,
        solve_by_elim,
    },
    have duv_cont : continuous (deriv (u * v)),
    {
        rw product_rule hu hv,
        apply continuous.add,
        rw mul_comm,
        all_goals {
            apply continuous.mul,
            work_on_goal 0
            {
                apply @differentiable.continuous ℝ _ _ _ _ _ _ _,
            },
            repeat {assumption},
        },
    },
    have H2 : ∫ x in a..b, deriv (u*v) x = u b * v b - u a * v a,
    {
        rw ftc2, refl,
        exact differentiable.mul hu hv,
        repeat {assumption},
    },
    rw [←H2, ←interval_integral.integral_sub],
    {
        congr,
        ext,
        rw huv,
        simp only [pi.add_apply, pi.mul_apply],
        rw mul_comm (v x) (deriv u x),
        ring,
    },
    { 
        apply integrable_of_cont,
        assumption,
    },
    apply integrable_of_cont,
    apply continuous.mul,
    apply @differentiable.continuous ℝ _ _ _ _ _ _ _,
    repeat {assumption},
end

lemma int_by_parts_zero_ends (u v : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (hu : differentiable ℝ u)
    (hv : differentiable ℝ v) (hcu : continuous(deriv u)) (hcv : continuous(deriv v)) 
    (ha : u a * v a = 0) (hb : u b * v b = 0)
    :
∫ x in a..b, u x * deriv v x = - ∫ x in a..b,  v x * deriv u x := 
begin
    rw int_by_parts,
    repeat {assumption},
    rw [ha, hb],
    norm_num,
end

@[simp] lemma pow_ext (f : ℝ → ℝ) (n : ℕ) : f^n = λ x, (f x)^n :=
begin
    induction n with d hd,
    {
        norm_num,
        refl,
    },
    {
        change f^(d+1) = λ x, (f x)^(d+1),
        rw [pow_add, hd, pow_one],
        ext,
        norm_num,
        ring,
    }
end

lemma differentiable_cospow_at (n: ℕ) {x : ℝ} : differentiable_at ℝ (cos^(n+1)) x:=
begin
    have hcos : differentiable ℝ cos,
    {
        apply differentiable.cos,
        exact differentiable_id',
    },
    apply differentiable_fpow hcos,
end

lemma deriv_cospow (n: ℕ) : deriv (λ (x : ℝ), cos x ^ (n+1)) = λ x, -((n : ℝ)+1) * (cos x)^n * sin x :=
begin
    have hcos : differentiable ℝ cos,
    {
        apply differentiable.cos,
        exact differentiable_id',
    },
    rw power_rule' n hcos,
    dsimp,
    ext,
    rw real.deriv_cos,
    ring,
end

lemma continuous_cospow {n: ℕ} : continuous (λ (x : ℝ), (cos x)^n) :=
begin
    exact continuous.pow continuous_cos n,
end

lemma continuous_cospow' {c : ℝ} {m : ℕ}  :
  continuous
    (λ (x : ℝ), c * cos x ^m) :=
begin
    apply continuous.mul,
    {
        exact continuous_const,
    },
    {
        exact continuous_cospow,
    },
end

lemma differentiable_cospow {n: ℕ} : differentiable ℝ (λ (x : ℝ), (cos x)^n) :=
begin
    simp only [differentiable_id', differentiable.pow, differentiable.cos],
end

lemma continuous_deriv_cospow (n: ℕ) : continuous (deriv (λ (x : ℝ), cos x ^ (n+1))) :=
begin
    rw deriv_cospow,
    apply continuous.mul,
    {
        exact continuous_cospow',
    },
    {
        exact continuous_sin,
    }
end

lemma sin_to_cos {x : ℝ} : (sin x)^2 = 1 - (cos x)^2 :=
begin
    rw ←sin_sq_add_cos_sq x,
    ring,
end

lemma cos_to_sin {x : ℝ} : (cos x)^2 = 1 - (sin x)^2:=
begin
    rw ←sin_sq_add_cos_sq x,
    ring,
end

lemma deriv_sin_times_cos {x:ℝ} : deriv(sin * cos) x =
    (cos^2 - sin^2) x:=
begin
    have H := deriv_mul differentiable_at_sin differentiable_at_cos,
    have h0 : sin * cos = λ y, sin y * cos y, by refl,
    rw [h0, H, real.deriv_sin, real.deriv_cos],
    ring,
end

lemma deriv_sin_cos  {m : ℕ} {x : ℝ} : deriv(sin * cos^(m+1)) x =
    (m+2) * (cos x)^(m+2) - (m+1) * (cos x)^m:=
begin
    have h0 : sin * cos^(m+1) = λ y, sin y * (cos y)^(m+1),
    {
        simp only [pow_ext],
        refl,
    },
    induction m with d hd,
    {
        simp,
        rw deriv_sin_times_cos,
        simp only [pow_ext, pi.sub_apply],
        rw sin_to_cos,
        ring,
    },
    {
        simp,
        have H := deriv_mul (@differentiable_at_sin x)
            (differentiable_cospow_at d.succ),
        repeat {rw pow_succ,},
        have h2 : (λ (y : ℝ), sin y * (cos ^ (d.succ + 1)) y) x = sin x * (cos ^ (d.succ + 1)) x,
        {
            dsimp,
            refl,
        },
        have hsin : sin * (λ (x : ℝ), cos x ^ (d.succ + 1)) =
            (λ x, sin x * cos x ^ (d.succ + 1)),
        {
            have hsin' : sin = (λ (x:ℝ), sin x), refl,
            rw hsin',
            refl,
        },
        rw hsin,
        clear hsin,
        have hhd : (sin * cos ^ (d + 1) = λ (y : ℝ), sin y * cos y ^ (d + 1)),
        {
            finish,
        },
        specialize hd hhd,
        clear hhd,
        simp [h0],
        clear h0,
        ring_exp,
        rw sin_to_cos,
        generalize : cos x = C,
        discrete_field,
    },
end

lemma deriv_sin_cos' {m : ℕ} : deriv (λ x, sin x * cos x^(m+1)) =
    λ x, (m+2) * cos x^(m+2) - (m+1) * cos x^m :=
begin
    ext,
    have h := @deriv_sin_cos m x,
    have h0 : sin * cos^(m+1) = λ y, sin y * (cos y)^(m+1),
    {
        simp only [pow_ext],
        refl,
    },
    rw h0 at h,
    rw h,
end
