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
  all_goals {try {simp}},
  apply_rules [
    continuous_on.neg,
    continuous.continuous_on,
    differentiable.continuous,
    differentiable_on.continuous_on,
    continuous.Icc_extend,
    continuous_on.mono,
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
    ] 10,
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
    sub_ne_zero_of_ne,
    pow_ne_zero,
    ne_of_gt,
    ne_of_lt
    ] 10,
  all_goals {try {norm_cast}, try {norm_num}}
]

meta def show_pos := `[
  apply_rules [
    nat.succ_pos,
    mul_pos,
    div_pos,
    inv_pos.mpr,
    pow_pos
    ] 10,
  all_goals {try {norm_cast}, try {norm_num}, try {nlinarith}}
]


meta def clear_denoms := `[
  try {rw div_eq_div_iff},
  try {rw eq_div_iff},
  try {symmetry, rw eq_div_iff},
  try { ring_exp },
  all_goals {show_nonzero}
]

meta def discrete_field := `[
  try {ext},
  try {field_simp *},
  try {clear_denoms},
  try {ring_exp},
  try {norm_num},
  try {linarith}
]

end tactic.interactive

lemma integrable_of_cont {f : ℝ → ℝ} (a b : ℝ) (h : continuous f):
    interval_integrable f measure_theory.measure_space.volume a b :=
begin
    have hmeas : measurable f := continuous.measurable h,
    have hconton : continuous_on f (interval a b) := continuous.continuous_on h,
    exact continuous_on.interval_integrable hconton hmeas, 
end

lemma ftc1 {f : ℝ -> ℝ} (hf2 : continuous f) (a : ℝ) (x : ℝ) :
  has_deriv_at (λ (b : ℝ), ∫ (t : ℝ) in a..b, f t) (f x) x :=
interval_integral.integral_has_deriv_at_right (hf2.interval_integrable _ _) hf2.continuous_at

theorem ftc2 (F f : ℝ → ℝ) {hF : differentiable ℝ F}
 (hFf : deriv F = f)
 {hf1 : continuous f}
(a b : ℝ) (h : a ≤ b) : (∫ x in a..b, f x) = F b - F a :=
begin
  subst hFf,
  by_cases hab : (a = b),
    simp only [hab, interval_integral.integral_same, sub_self],
  replace h : a < b,
  {
      rw le_iff_lt_or_eq at h,
      tauto,
  },
  have Fcont := differentiable.continuous hF,
  have hf := continuous.measurable hf1,

  set G := (λ x, (∫ t in a..x, deriv F t)) with hG,
  have prop := ftc1 hf1 a,
  have hb : b ∈ Ioc a b := right_mem_Ioc.mpr h,
    have Gdiff : ∀ y ∈ Ioc a b, differentiable_on ℝ G (Icc a y),
    {
        rintro y hy z hz,
        apply differentiable_at.differentiable_within_at,
        exact has_deriv_at.differentiable_at (prop z),
    },

    have Gcont : ∀ y ∈ Ioc a b, continuous_on G (Icc a y),
    {
        intros y hy,
        apply differentiable_on.continuous_on (Gdiff y hy),
    },
    have sub_cont : continuous_on (F - G) (Icc a b),
    {
        exact continuous_on.sub (continuous.continuous_on Fcont) (Gcont b hb),
    },
    have sub_diff : differentiable_on ℝ (F - G) (Ioo a b),
    {
      exact differentiable_on.sub
        (differentiable.differentiable_on hF)
        (differentiable_on.mono (Gdiff b hb) Ioo_subset_Icc_self),
    },
  have H : ∀ y ∈ Icc a b, (deriv (F - G)) y = 0,
  {
    intros y hy,
    change deriv (λ t, F t - G t) y = 0,
    rw deriv_sub (hF y) (has_deriv_at.differentiable_at (prop y)),
    rw sub_eq_zero,
    apply eq.symm,
    apply has_deriv_at.deriv (prop y),
  },

 have key : (F - G) b = (F - G) a,
  {
    rcases (exists_deriv_eq_slope (F - G) h sub_cont sub_diff) with ⟨c, hc, hc2⟩,
    have hc' : c ∈ Icc a b := mem_Icc_of_Ioo hc,
    rw H c hc' at hc2,
    replace hc2 := eq.symm hc2,
    rw div_eq_zero_iff at hc2,
    cases hc2,
    work_on_goal 1 {congr},
    all_goals {exact sub_eq_zero.mp hc2},
  },
  have G_a : G a = 0, by simp only [hG, interval_integral.integral_same],
  suffices : F b - G b = F a - G a, linarith,
  simp only [pi.sub_apply] at key ⊢, exact key,
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
    have H : 0 < ∫ x in a..b, (g x - f x),
    {
        apply integral_strictly_pos_of_cont
        (g-f) a b (continuous.sub hg hf) hab,
        all_goals {
            simp [sub_pos],
            assumption,
        },
    },
    rw ←sub_pos,
    rw ←interval_integral.integral_sub
        (integrable_of_cont a b hg)
        (integrable_of_cont a b hf),
    exact H,
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
    rintro ⟨x, hx⟩,
    apply int_pos_of_pos_function,
    { show_continuous },
    { exact hab },
    { exact λ x hx1 hx2, pow_two_nonneg (f x) },
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

@[simp] lemma power_rule'  {f : ℝ → ℝ} (n : ℕ) (hfd : differentiable ℝ f):
    deriv (λ (x : ℝ), (f x)^(n + 1)) = λ (x : ℝ), ((n : ℝ) + 1) • ((f x)^n * deriv f x) :=
begin
    rw [←pow_fun_def, ←pow_deriv_fun_def],
    exact power_rule hfd,
end

@[simp] lemma power_rule'' (n : ℕ) :
    deriv (λ (x : ℝ), x^(n + 1)) = λ (x : ℝ), ((n : ℝ) + 1) • (x^n) :=
begin
    have hfd : differentiable ℝ (λ (x:ℝ), (x:ℝ)) := differentiable_id',
    have deriv_id_my : deriv (λ x, x) = λ (x : ℝ), (1:ℝ) := deriv_id',
    have H := power_rule' n hfd,
    rw deriv_id_my at H,
    rw H,
    simp only [mul_one, algebra.id.smul_eq_mul],
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
        rw ftc2,-- refl,
        exact differentiable.mul hu hv,
        repeat {assumption},
        congr,
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
    apply continuous.mul continuous_cospow' continuous_sin,
end

@[simp] lemma deriv_sin_times_cos {x : ℝ} : deriv(sin * cos) x =
    2 * cos x ^ 2 - 1 :=
begin
    have H : deriv (λ (y : ℝ), sin y * cos y) x =
        deriv sin x * cos x + sin x * deriv cos x
        := deriv_mul differentiable_at_sin differentiable_at_cos,
    have h0 : sin * cos = λ y, sin y * cos y, by refl,
    have hsin : sin x^2 = 1 - cos x^2,
    {
        rw eq_sub_iff_add_eq,
        exact sin_sq_add_cos_sq x,
    },
    rw [h0, H, real.deriv_sin, real.deriv_cos],
    ring,
    rw hsin,
    ring,
end

@[simp] lemma deriv_sin_cos {m : ℕ} : deriv (λ x, sin x * cos x^(m+1)) =
    λ x, (m+2) * cos x^(m+2) - (m+1) * cos x^m :=
begin
    ext,
    suffices : deriv(sin * cos^(m+1)) x =
    (m+2) * (cos x)^(m+2) - (m+1) * (cos x)^m,
    {
        rw pow_ext at this,
        exact this,
    },
    induction m with d hd,
    {
        simp only [mul_one, nat.cast_zero, pow_one, zero_add, pow_zero],
        exact deriv_sin_times_cos,
    },
    {
        simp,
        have H := deriv_mul (@differentiable_at_sin x)
            (differentiable_cospow_at d.succ),
        repeat {rw pow_succ,},
        have h2 : (λ (y : ℝ), sin y * (cos ^ (d.succ + 1)) y) x =
            sin x * (cos ^ (d.succ + 1)) x, by tauto,
        have hsin : sin * (λ (x : ℝ), cos x ^ (d.succ + 1)) =
            (λ x, sin x * cos x ^ (d.succ + 1)), by tauto,
        rw hsin,
        have hhd : (sin * cos ^ (d + 1) = λ (y : ℝ), sin y * cos y ^ (d + 1)),
        {
            ext,
            simp only [pi.mul_apply, pow_ext],
        },
        simp [pow_ext],
        ring_exp,
        have sin_to_cos : sin x^2 = 1 - cos x^2,
        {
            rw eq_sub_iff_add_eq,
            exact sin_sq_add_cos_sq x,
        },
        rw sin_to_cos,
        discrete_field,
    },
end