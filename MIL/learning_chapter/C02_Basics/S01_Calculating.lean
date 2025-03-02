import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

--rw: rewrite，重写
--mul_comm: 乘法交换律
--mul_assoc: 乘法结合律
--by: 一步到位的证明

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

--sorry: 用于占位，表示证明尚未完成

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
--使用假设条件证明

--practice
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry

--多个重写命令可以通过单个命令执行，通过在方括号内用逗号分隔相关标识符来实现。
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

--另一个技巧是，我们可以在一个例子或定理之外一次性声明变量。Lean 随后会自动包含它们。
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

--通过以下方式，确定各种定理的用法，以及变量的类型
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

--calc结构化证明，可以看到每一步的推理过程，不需要写by
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]


--practice
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry
--上边的证明使用下边的这些定理
#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

--请看下边的例子
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

--exact: 用于证明目标和假设相等的情况

--当我们导入 Mathlib.Data.Real.Basic 时， ring 策略间接导入，但在下一节中我们将看到它可以用作对除了实数以外的结构进行计算。它可以通过命令 import Mathlib.Tactic 显式导入。我们将看到还有其他类似策略用于其他常见类型的代数结构。
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

--存在一种名为 rw 的变体，称为 nth_rw ，它允许您仅替换目标中表达式的特定实例。可能的匹配从 1 开始枚举，因此，在以下示例中， nth_rw 2 [h] 替换了 a + b 的第二个出现为 c 。
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
