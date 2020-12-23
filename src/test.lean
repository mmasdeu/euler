import tactic
import measure_theory.interval_integral
import measure_theory.lebesgue_measure
import measure_theory.set_integral
import analysis.calculus.deriv
import data.finset

noncomputable theory
open_locale classical
open_locale big_operators
open interval_integral
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

lemma my_integral_pos_lemma {f : ℝ → ℝ} {a b : ℝ}
  (hab : a ≤ b)
  (hf : 0 ≤ᵐ[measure_theory.measure_space.volume.restrict (set.Ioc a b)] f)
  (hfi : measure_theory.integrable_on f (set.Ioc a b) measure_theory.measure_space.volume)
  :
  0 < measure_theory.measure_space.volume (function.support f ∩ set.Ioc a b)
  → 0 < ∫ x in a..b, f x :=
begin
    simp only [integral_of_le hab, set.Ioc_eq_empty hab, set.union_empty] at hf ⊢,
    simp [measure_theory.set_integral_pos_iff_support_of_nonneg_ae hf hfi],
end

theorem integral_nonneg_of_cont (f : ℝ → ℝ) (a b : ℝ)
    (hf : continuous f)
    (hab : a ≤ b)
    (h : ∀ (x : ℝ), a ≤ x → x ≤ b → 0 ≤ f x) :
    0 ≤ ∫ x in a..b, f x := 
begin
    have h' : ∀ (x : ℝ), x ∈ set.Icc a b → 0 ≤ f x,
    {
      sorry
    },
    rw integral_of_le hab,

    apply my_integral_pos_lemma hab,
    {
        simp only,
        
        sorry
    },
    {
      --exact integrable_of_cont a b hf,
      sorry
    },
    {

      sorry
    },
end

theorem integral_strictly_pos_of_cont (f : ℝ → ℝ) (a b : ℝ)
    (hf : continuous f)
    (hab : a ≤ b)
    (h : ∀ (x : ℝ), a ≤ x → x ≤ b → 0 ≤ f x)
    (hneq: ∃ x, a ≤ x ∧ x ≤ b ∧ 0 < f x) :
    0 < ∫ x in a..b, f x := 
begin
    have h' : ∀ (x : ℝ), x ∈ set.Icc a b → 0 ≤ f x,
    {
      sorry
    },
    apply my_integral_pos_lemma hab,
    {
        simp only,
        
        sorry
    },
    {
      --exact integrable_of_cont a b hf,
      sorry
    },
    {

      sorry
    },
end