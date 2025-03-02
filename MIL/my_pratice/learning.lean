import MIL.Common
import Mathlib.Data.Real.Basic

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

--基本组成：example 定义域: 命题 := (by或者calc)证明
--rw: rewrite，重写
--mul_comm: 乘法交换律
--mul_assoc: 乘法结合律
--mul_add: 乘法加法分配律
--add_mul: 加法乘法分配律
--add_assoc: 加法结合律
--two_mul: 2倍乘法
--calc结构化证明，可以看到每一步的推理过程
--by和calc的区别是calc是结构化的证明，可以看到每一步的推理过程，而by是一步到位的证明
-- 请注意，证明 不 以 by 开头：以 calc 开头的表达式是一个 证明项。 calc 表达式也可以在策略证明中使用， 但 Lean 把它解释为使用结果证明项来解决目标的指令。 calc 语法很挑剔：下划线和论证必须按照上面指示的格式。 Lean 使用缩进来确定诸如策略块或 calc 块的起始和结束位置；尝试更改上面证明中的缩进以观察会发生什么。

section
variable (a b c:ℝ  )
#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
 end
