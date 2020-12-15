import data.real.basic
import data.set.basic
import tactic

namespace mth1001

/-
We'll only deal with real-valued sequences. Such a sequence is merely a function from `ℕ` to `ℝ`
We'll use the Lean built-in real number type rather than the type we've constructed.
-/

section convergence

-- `convergesto f a` means
def convergesto (f : ℕ → ℝ) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (f n - a) < ε

/-
We'll prove that the sequence `f₁ : ℕ → R` given by `f₁(n) = 5` converges to `5`.
-/

def f₁ : ℕ → ℝ := λ n, (5 : ℝ)

example : convergesto f₁ 5 :=
begin
  assume ε : ℝ,
  assume εpos : ε > 0, -- It suffices to prove `∃ N, ∀ n ≥ N, abs (f₁ n - 5) < ε`.
  use 1, -- Take `N := 1`.
  assume n : ℕ,
  assume hn : n ≥ 1,
  unfold f₁, -- By unfolding, it suffices to show `abs (5 - 5) < ε`.
  norm_num, -- That is, to prove `abs 0 < ε`.
  linarith, -- This is proven by the `linarith` tactic.
end

/-
More generally, we'll show a constant sequence converges.
-/

-- Exercise 075:
lemma convergesto_const (c : ℝ) : convergesto (λ n, c) c :=
begin
  assume ε : ℝ,
  assume εpos : ε > 0,
  sorry  
end

end convergence

section uniqueness_of_limits

variables {f : ℕ → ℝ} {a b : ℝ}

lemma convergesto_unique (h₁ : convergesto f a) (h₂ : convergesto f b) : a = b :=
begin
  sorry
end


end uniqueness_of_limits

section algebra_of_limits

variables (f g : ℕ → ℝ) -- `f` and `g` are sequences
variables (a b c : ℝ)

-- The following result will often come in handy!
lemma div_abs_pos_of_pos_of_non_zero {ε c : ℝ} (εpos : ε > 0) (h : c ≠ 0) : ε / abs c > 0 :=
begin
  have h₂ : 0 < abs c, from  abs_pos_iff.mpr h,
  have h₃ : 0 < (abs c)⁻¹, from inv_pos.mpr h₂,
  exact mul_pos εpos h₃,
end

example (a b c : ℝ) (h₁ : a < b / c) (h₂ : 0 < c): a * c < b := (lt_div_iff h₂).mp h₁

example (a b : ℝ) : abs (a*b) = abs a * abs b := abs_mul a b

example (x y : ℝ) : x ≤ max x y := le_max_left x y

example (x y : ℝ) : y ≤ max x y := le_max_right x y

-- Exercise 076:
theorem convergesto_scalar_mul (h : convergesto f a) : convergesto (λ n, c * (f n)) (c * a) :=
begin
  by_cases h₂ : c = 0,
  { sorry, }, 
  { sorry, }, 
end

-- Here is the triangle inequality in Lean.
example (x y : ℝ) : abs (x + y) ≤ abs x + abs y := abs_add x y

-- Exercise 077:
theorem convergesto_add (h₁ : convergesto f a) (h₂ : convergesto g b )
: convergesto (λ n, f n + g n) (a + b) :=
begin
  sorry  
end

-- Exercise 078:
-- The same proof can be written more briefly using `congr'` and by giving arguments to `linarith`.
example (h₁ : convergesto f a) (h₂ : convergesto g b ) : convergesto (λ n, f n + g n) (a + b) :=
begin
  sorry    
end


end algebra_of_limits

section specific_example

/-
In Lean, it's often harder to work with particular examples than with general theorems.
Here, we show convergence of a particular sequence.

We'll need the corollorary to the Archimedean property. In Lean,this is `exists_nat_one_div_lt`.
Note the use of `↑n` to indicate the embedding (or coercion) of the natural number `n`
as a real number.
-/

example (ε : ℝ) (h : 0 < ε) : ∃ n : ℕ, 1/(↑n + 1) < ε := exists_nat_one_div_lt h

example (x : ℝ) (h : x > 0) : abs x = x := abs_of_pos h

example (x : ℝ) (h : 0 < x) : 0 < x⁻¹ := by {rwa inv_pos}

example (x : ℝ) (h : 0 < x) : x⁻¹ = (1 : ℝ) / x := inv_eq_one_div x

-- Now we'll show the sequence given by `λ n, 3 + 1/n` converges to `3`.
example : convergesto (λ n, 3 + 1/n) 3 :=
begin
  unfold convergesto,
  assume ε εpos,
  have h : ∃ N : ℕ, 1/(↑N + 1) < ε, from exists_nat_one_div_lt εpos,
  cases h with N hN, -- By `∃` elim. on `h`, STP the goal assuming `N : ℕ` and `hN : 1/(↑N+1) < ε`.
  use N + 1, -- By `∃` intro on `N + 1`, it suffices to prove
  -- `∀ n ≥ N + 1, n ≥ N + 1 → abs (3 + 1/↑n - 3) < ε`.
  assume n hn, -- assume `n : ℕ` and `hn : n ≥ N`.
  have h₂ : abs ((3 : ℝ) + 1 / ↑n - 3)  = abs (↑n)⁻¹, ring,
  rw h₂,
  have : N + 1 > 0, linarith,
  have : n > 0, linarith,
  have :  (0 : ℝ) < ↑n, { rwa nat.cast_pos },
  have : (0 : ℝ) < N + 1, {change (0 : ℝ) < ↑(N + 1), rw nat.cast_pos, linarith, },
  have : (0 : ℝ) < (↑n)⁻¹, { rwa inv_pos },
  rw abs_of_pos this,
  have : (↑n)⁻¹ ≤ (↑N + (1 : ℝ))⁻¹,
  { rw inv_le_inv, 
    change ↑(N + 1) ≤ ↑n,
    rwa nat.cast_le,
    repeat { assumption }, },
  apply lt_of_le_of_lt,
  { assumption, },
  { rwa inv_eq_one_div, },
end

end specific_example

end mth1001
