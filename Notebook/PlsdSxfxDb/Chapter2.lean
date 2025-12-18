import VersoManual

-- import Mathlib.Tactic.TacticAnalysis
import Mathlib.Data.Real.Basic

example : 1 = 1 := rfl

#doc (Verso.Genre.Manual) "基础数学与逻辑" =>

%%%
htmlSplit := .never
%%%


# 一些符号

∀: Forall, 对于所有的、对于每一个、只要

∃: Exists, 存在、存在某个


Σ: 求和，例如$`\Sigma_{i=1}^{n}i`表示“从`i=1`一直到`i=n`，所有`i`的和”


ℕ: Natural number, 全体自然数的集合

ℤ: Zahlen, 全体整数的集合

ℚ: Quotient, 全体有理数

ℝ: Real number, 全体实数

# 形式逻辑

→: 蕴含

↔: 当且仅当


假设有命题A → B:
* 逆命题: B → A. (逆命题 → 原命题) → False
* 否命题: ¬A → ¬B. (否命题 → 原命题) → False
* 逆否命题: ¬B → ¬A. 逆否命题 ↔ 原命题


命题1. ¬(∀x, x具有性质A)

命题2. ∃x满足¬(x具有性质A)

证明命题1 ↔ 命题2:
```Verso.Genre.Manual.InlineLean.lean
variable (α : Type) (A : α → Prop)

def prop1 : Prop := ¬∀ x : α, A x
def prop2 : Prop := ∃ x : α, ¬A x

example : prop1 α A ↔ prop2 α A := by
  apply Iff.intro
  · show (¬∀ x : α, A x) → (∃ x : α, ¬A x)
    intro h
    apply Classical.byContradiction
    intro h'
    apply h
    intro m
    apply Classical.byContradiction
    intro hnA
    apply h'
    apply Exists.intro m
    exact hnA
  · show (∃ x : α, ¬A x) → (¬∀ x : α, A x)
    intro h h'
    apply h.elim
    intro (m : α)
    intro (hn : ¬A m)
    apply hn
    exact h' m

```

命题3. ¬(∃x满足x具有性质A)

命题4. ∀x, ¬(x具有性质A)

证明命题3 ↔ 命题4:

```Verso.Genre.Manual.InlineLean.lean

variable (α : Type) (A : α → Prop)

def prop3 : Prop := ¬∃ x : α, A x
def prop4 : Prop := ∀ x : α, ¬A x

example : prop3 α A ↔ prop4 α A := by
  apply Iff.intro
  · show (¬∃ x : α, A x) → (∀ x : α, ¬A x)
    intro h m hA
    apply h
    apply Exists.intro m
    exact hA
  · show (∀ x : α, ¬A x) → (¬∃ x : α, A x)
    intro h h'
    apply h'.elim
    intro m hA
    have hnA : ¬A m := h m
    exact hnA hA

```

# 证明的技巧

1. 举反例证明
2. 证明逆否命题
3. 反证法
4. 归纳证明
5. 分两步直接证明

例2.1 举反例证明

命题: 并非每个连续函数都是可微的

证:
1. 反例: $`f(x) = |x|`
2. 然后证: $`f(x) = |x|`连续. TODO
3. 然后证: $`f(x) = |x|`可微. TODO


例2.2 证明逆否命题

命题: 对于任意2个数$`x`和$`y`, 当且仅当$`∀ε > 0, |x - y| < ε`时$`x = y`. 这个命
题断言如果2个数可以任意接近(这意味着我们可以选择任意小的距离$`ε`, 并且这2个数之
间的距离比$`ε`还要小), 那么它们就是相等的.

