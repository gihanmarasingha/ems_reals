import ..library.src_field
import tactic

namespace mth1001

namespace myreal

section grouplaws

variables {R : Type} [comm_group R]

/-
The following six lemmas are 'user-friendly' variants of the first four axioms of the real number
system. I have split each of the additive identity and additive inverse axioms into two lemmas.begin

For example, `zero_add` and `add_zero` together constitute the additive identity axiom.
-/

lemma add_comm (x y : R) : x + y = y + x := comm_group.add_comm x y
lemma add_assoc (x y z : R) : (x + y) + z = x + (y + z) := comm_group.add_assoc x y z
lemma add_zero (x : R) : x + 0 = x := comm_group.add_zero x
lemma zero_add (x : R) : 0 + x = x := by {rw [add_comm, add_zero]}
lemma add_neg (x : R) : x + (-x) = 0 := comm_group.add_inv x
lemma neg_add (x : R) : (-x) + x = 0 := by {rw [add_comm, add_neg]}

-- We define what it means for `u` to be an additive identity.
def add_identity (u : R) := ∀ x : R, (x + u = x) ∧ (u + x = x)

-- `0` is an additive identity.
example : add_identity (0 : R) :=
begin
  intro x,
  exact and.intro (add_zero x) (zero_add x),
end

-- The additive identity is unique.
theorem add_identity_unique {a b : R} (h₁ : add_identity a) (h₂ : add_identity b)
  : a = b :=
begin
  specialize h₁ b, -- `h₁ : (b + a = b) ∧ (a + b = b)`
  specialize h₂ a, -- `h₂ : (a + b = a) ∧ (b + a = a)`
  calc  a = a + b : h₂.left.symm -- If `h : x = y`, then `h.symm : y = x`.
      ... = b     : h₁.right
end

-- Definition of additive inverse.
def add_inverse (y x : R) := (x + y = 0) ∧ (y + x = 0)

-- Every real number has an additive inverse.
lemma has_add_inverse : ∀ a : R, ∃ b : R, add_inverse b a :=
begin
  intro a,
  use (-a),
  exact and.intro (add_neg a) (neg_add a)
end

-- The additive inverse is unique.
theorem add_inverse_unique {a b x : R} (h₁ : add_inverse a x) (h₂ : add_inverse b x)
  : a = b :=
calc  a = a + 0        : (add_zero a).symm
    ... = a + (x + b)  : by rw h₂.left
    ... = (a + x) + b  : by rw add_assoc
    ... = 0 + b        : by rw h₁.right
    ... = b            : zero_add b


-- Exercise 001:
-- Complete the following with a `calc` style proof.
lemma add_left_eq_self_mp {x a : R} : x + a = a → x = 0 :=
begin
  intro h,
  sorry  
end

-- Exercise 002:
lemma add_left_eq_self_mpr {x a : R} : x = 0 → x + a = a :=
begin
  sorry  
end

-- Exercise 003:
theorem add_left_eq_self (x a : R) : x + a = a ↔ x = 0:=
begin
  split,
  { exact add_left_eq_self_mp, },
  { sorry, }, 
end

-- Exercise 004:
-- Use `split` as above.
theorem add_left_inj (x a b : R) : a + x = b + x ↔ a = b :=
begin
  sorry    
end

lemma sub_eq_add_neg (x y : R) : x - y = x + (-y) := rfl 

-- Exercise 005:
-- You can do the following with two rewrites. Use `add_zero` and `neg_add`
lemma neg_zero : -(0 : R) = 0 :=
sorry 

-- Exercise 006:
lemma sub_zero (a : R) : a - 0 = a :=
sorry  

-- Exercise 007:
-- The following can be proved in one line as a sequences of rewrites.
theorem sub_eq_zero_iff_eq (x y : R) : x - y = 0 ↔ x = y :=
sorry 

-- Exercise 008:
-- The following can be proved in one line as a sequences of rewrites.
theorem neg_neg (x : R) : - - x = x :=
sorry 

-- Exercise 009:
-- Do the following using proof by calculation.
lemma neg_add_eq_neg_add_neg (x y : R) : -(x + y) = -y + - x :=
sorry 

end grouplaws

section fieldlaws

variables {R : Type} [myfield R]

/-
The following lemmas encapsulate the remaining algebraic axioms of the real number type.
-/
lemma mul_comm (x y : R) : x * y = y * x := myfield.mul_comm x y
lemma mul_assoc (x y z : R) : (x * y) * z = x * (y * z) := myfield.mul_assoc x y z
lemma mul_one (x : R) : x * 1 = x := myfield.mul_one x
lemma one_mul (x : R) : 1 * x = x := by { rw [mul_comm, mul_one] }
lemma mul_inv (x : R) : x ≠ 0 → x * x⁻¹  = 1 := myfield.mul_inv x
lemma inv_mul (x : R) : x ≠ 0 → x⁻¹ * x = 1 := by {intro h, rw [mul_comm, mul_inv x h], }
lemma mul_add (x y z : R) : x * (y + z) = x * y + x * z := myfield.mul_add x y z
lemma zero_ne_one : (0 : R) ≠ (1 : R) := myfield.zero_ne_one

def mul_identity (u : R) := ∀ x : R, (x * u = x) ∧ (u * x = x)

-- Exercise 010:
-- Use `add_mul` and `add_comm` to prove the following.
theorem add_mul (x y z : R) : (x + y) * z = x * z + y * z :=
begin
  sorry    
end

-- Exercise 011:
theorem mul_identity_unique {a b : R} (h₁ : mul_identity a) (h₂ : mul_identity b) 
  : a = b :=
begin
  sorry  
end

def mul_inverse (y x : R) := (x * y = 1) ∧ (y * x = 1)

-- Exercise 012:
theorem mul_inverse_unique {a b x : R} (h₁ : mul_inverse a x) (h₂ : mul_inverse b x)
  : a = b :=
sorry 

-- Exercise 013:
-- This exercise is somewhat challenging.
theorem mul_zero {x : R} : x * (0 : R) = (0 : R) :=
begin
  have h₁ : x * 0 = x * 0 + x * 0,
    calc x * 0
          = x * (0 + 0)   : by rw add_zero (0 : R)
      ... = x * 0 + x * 0 : by rw mul_add,
  sorry  
end

-- Exercise 014:
-- Whereas the next result is a simple consequence of the previous result.
theorem zero_mul {x : R} : (0 : R) * x = (0 : R) :=
begin
  sorry  
end

-- Exercise 015:
theorem neg_one_mul (x : R) : (-1) * x = -x :=
begin
  sorry  
end

-- Exercise 016:
-- Use the result above to prove this lemma.
lemma neg_one_mul_neg_one : (-(1 : R)) * (-1) = 1 :=
sorry 

-- Exercise 017:
lemma neg_mul_eq_mul_neg (x y : R) : -(x * y) = x * (-y) :=
sorry 

lemma neg_mul_neg_self (x : R) : (-x)*(-x) = x * x :=
by rw [←neg_one_mul, mul_assoc, mul_comm x _, ←mul_assoc, ←mul_assoc, neg_one_mul_neg_one, one_mul]

-- Exercise 018:
lemma neg_mul_neg (x y : R) : (-x) * (-y) = x * y :=
begin
  sorry  
end

-- Exercise 019:
lemma one_inv : (1 : R)⁻¹ = (1 : R) :=
sorry 
-- Exercise 020:
theorem mul_sub (x y z : R) : x * (y - z) = x * y - x * z :=
begin
  sorry  
end

-- Exercise 021:
theorem mul_left_inj' (x a b : R) (h₁ : x ≠ 0): a * x = b * x ↔ a = b :=
begin
  sorry    
end

open_locale classical

-- Exercise 022:
-- This is a challenging exercise.
-- Hint 1. Do a `by_cases` proof, depending on whether `x = 0` or not.
-- Hint 2. Use the fact that a non-zero real number has a multiplicative inverse.
lemma eq_zero_of_not_eq_zero_of_mul_not_eq_zero (x b : R) (h₁ : b ≠ 0) (h₂ : x * b = 0) : x = 0 :=
begin
  sorry  
end

-- Exercise 023:
-- The following is a corollary of the result above.
lemma eq_zero_or_eq_zero_of_mul_eq_zero (x y : R) (h : x * y = 0) : x = 0 ∨ y = 0 :=
begin
  sorry  
end

-- Exercise 024:
lemma mul_inv' (x y : R) (h₁ : x ≠ 0) (h₂ : y ≠ 0) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
begin
  have h : x * y ≠ 0,
  { sorry, }, 
  rw ←(mul_left_inj' _ _ _ h₁),
  sorry  
end

-- Exercise 025:
theorem inv_ne_zero {a : R} : a ≠ 0 → a⁻¹ ≠ 0 :=
begin
  sorry  
end

-- Exercise 026:
theorem inv_inv' (a : R) (h : a ≠ 0 ) : (a⁻¹)⁻¹ = a :=
begin
  sorry  end

end fieldlaws

section powers

variables {R : Type} [myfield R]

-- The following lemma is essentially the definition of exponentiation.
lemma pow_succ (x : R) (n : ℕ) : x^(n+1) = x * x^n := rfl

-- We have a couple of fundamental results.
lemma pow_zero (x : R) : x ^ 0 = 1 := rfl
lemma pow_one (x : R) : x ^ 1 = x := by rw [pow_succ, pow_zero, mul_one]
lemma pow_succ' (x : R) (n : ℕ) : x^(n+1) = x^n * x := by rw [pow_succ, mul_comm]

-- Exercise 027:
-- Rewrite using the above lemmas to prove this result.
lemma pow_two (x : R) : x ^ 2 = x * x :=
begin
  sorry    
end

-- Exercise 028:
-- Prove the following by induction on `n`.
theorem pow_ne_zero {x : R} (n : ℕ) (h : x ≠ 0) : x ^ n ≠ 0 :=
begin
  sorry  
end

-- Exercise 029:
-- Use induction. Make use of `nat.add_zero` and `nat.add_succ`
theorem pow_add (x : R) (m n : ℕ) : x ^ (m + n) = (x ^ m) * (x ^ n) :=
begin
  sorry  
end

-- Exercise 030:
-- Use induction. Make use of `nat.mul_zero`, `nat.succ_eq_add_one`, and `nat.mul_one`.
-- You'll need `left_distrib`, a synonym of `mul_add` for `ℕ`.
theorem pow_mul (x : R) (m n : ℕ) : x ^ (m*n) = (x ^ m) ^ n :=
begin
  sorry  
end

example (m n : ℕ) (h : m ≤ n) : n - m + m = n := nat.sub_add_cancel h

-- Exercise 031:
-- Use `nat.sub_add_cancel` (as demonstrated above).
theorem pow_sub_mul_pow (x : R) {m n : ℕ} (h : m ≤ n) : x ^ (n - m) * x ^ m = x ^ n :=
begin
  rw [←pow_add, nat.sub_add_cancel h],
end

-- Exercise 032:
theorem pow_sub' (x : R) (m n : ℕ) (h : m ≤ n) (ne0 : x ≠ 0) : x ^ (n - m) = (x ^ n) * (x ^ m)⁻¹ :=
begin
  sorry  
end
 
end powers

end myreal

end mth1001
