namespace mth1001

namespace myreal

section comm_group

class comm_group (R : Type*) :=
(add : R → R → R)
(zero : R)
(neg : R → R)
(add_comm : ∀ a b : R, add a b = add b a)
(add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c))
(add_zero : ∀ a : R, add a zero = a)
(add_inv : ∀ a : R, add a (neg a) = zero)

variables {R : Type*} [comm_group R]

instance : has_add R := ⟨comm_group.add⟩
instance : has_zero R := ⟨comm_group.zero⟩
instance : has_neg R := ⟨comm_group.neg⟩

def sub (x y : R) := x + (-y)

instance : has_sub R := ⟨sub⟩

end comm_group

class myfield (R : Type*) extends comm_group R:=
(mul : R → R → R)
(mul_comm : ∀ a b : R, mul a b = mul b a)
(mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c))
(one : R)
(mul_one : ∀ a : R, mul a one = a)
(inv : R → R)
(mul_inv : ∀ a : R, a ≠ 0 → mul a (inv a) = one)
(mul_add : ∀ a b c : R, mul a (b + c) = mul a  b + mul a c)
(zero_ne_one : (0 : R) ≠ (one : R))

variables {R : Type} [myfield R]

instance : has_mul R := ⟨myfield.mul⟩
instance : has_one R := ⟨myfield.one⟩
instance : has_inv R := ⟨myfield.inv⟩

def of_nat : ℕ → R
| 0            := (0 : R)
| (nat.succ x) := (of_nat x) + 1

instance : has_coe ℕ R := ⟨of_nat⟩

lemma coe_nat_succ (n : ℕ) : ((nat.succ n) : R) = (n : R) + (1 : R) := rfl

def pow1 : R → ℕ → R
| x 0            := (1 : R)
| x (nat.succ n) := x * (pow1 x n)  -- `nat.succ` is the Lean version of our function `S`

instance : has_pow R ℕ := ⟨pow1⟩

def pow2 (x : R) (m : ℤ) := ite (m ≥ 0) (pow1 x (int.to_nat m)) (pow1 x (int.to_nat (-m)))

-- instance : has_pow R ℤ := ⟨pow2⟩

end myreal

end mth1001