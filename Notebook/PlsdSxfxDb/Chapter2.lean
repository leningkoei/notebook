import VersoManual

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Verso.Genre.Manual.InlineLean

#doc (Verso.Genre.Manual) "基础数学与逻辑" =>

%%%
htmlSplit := .never
%%%


# 一些符号
%%%
tag := "yixiefuhao"
%%%

: ∀

  Forall, 对于所有的、对于每一个、只要

: ∃

  Exists, 存在、存在某个

: Σ

  求和，例如$`\sum_{i=1}^{n}i`表示“从`i=1`一直到`i=n`，所有`i`的和”
  ```lean
  #eval List.range' 1 10 1
  def sum (n : Nat) : Nat := (List.range' 1 n 1).sum

  ```

: ℕ

  Natural number, 全体自然数的集合

: ℤ

  Zahlen, 全体整数的集合

: ℚ

  Quotient, 全体有理数

: ℝ

  Real number, 全体实数

# 形式逻辑
%%%
tag := "xingshiluoji"
%%%

: →

  蕴含

: ↔

  当且仅当


: 假设有命题A → B

  : 逆命题

    B → A. (逆命题 → 原命题) → False

  : 否命题

    ¬A → ¬B. (否命题 → 原命题) → False

  : 逆否命题

    ¬B → ¬A. 逆否命题 ↔ 原命题

    *逆否命题 ↔ 原命题*需要用到经典逻辑


命题1. ¬(∀x, x具有性质A)

命题2. ∃x满足¬(x具有性质A)

: 证明命题1 ↔ 命题2
  ```lean
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
      intro m hn
      apply hn
      exact h' m

  ```

命题3. ¬(∃x满足x具有性质A)

命题4. ∀x, ¬(x具有性质A)

: 证明命题3 ↔ 命题4
  ```lean

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
%%%
tag := "zhengmingdejiqiao"
%%%

1. 举反例证明
2. 证明逆否命题 (经典逻辑)
3. 反证法 (经典逻辑)
4. 归纳证明
5. 分两步直接证明

例2.1 举反例证明

命题: 并非每个连续函数都是可微的
: 证:
  1. 反例: $`f(x) = |x|`
  2. 然后证: $`f(x) = |x|`连续. TODO
  3. 然后证: $`f(x) = |x|`可微. TODO

例2.2 证明逆否命题

命题: 对于任意2个数$`x`和$`y`, 当且仅当$`∀ξ > 0, |x - y| < ξ`时$`x = y`. 这个命
题断言如果2个数可以任意接近(这意味着我们可以选择任意小的距离$`ξ`, 并且这2个数之
间的距离比$`ξ`还要小), 那么它们就是相等的.
: 证:
  ```lean
  variable (x y : ℝ)

  example : (∀ ξ > 0, |x - y| < ξ) ↔ x = y := by
    constructor
    · show (∀ ξ > 0, |x - y| < ξ) → x = y
      contrapose -- 将证明目标转化为证明原目标的逆否命题
      --↑ 相比`contrapose`, `contrapose!`会对转化后的目标进一步化简
      intro hne
      show ¬(∀ ξ, ξ > 0 → |x - y| < ξ)
      apply Classical.not_forall.mpr
      show ∃ ξ, ¬(ξ > 0 → |x - y| < ξ)
      push_neg
      show ∃ ξ, ξ > 0 ∧ ξ ≤ |x - y|
      show ∃ ξ > 0, ξ ≤ |x - y|
      apply Exists.intro (|x - y| / 2)
      --↑ Alternatively, use `use |x - y| / 2`.
      constructor
      · show |x - y| / 2 > 0
        have : x - y ≠ 0 := sub_ne_zero.mpr hne
        have : |x - y| > 0 := abs_pos.mpr this
        exact half_pos this
      · show |x - y| / 2 ≤ |x - y|
        apply half_le_self_iff.mpr
        exact abs_nonneg $ x - y
    · show x = y → ∀ ε > 0, |x - y| < ε
      intro h _ξ hξ
      rw [h]
      rw [sub_self]
      rw [abs_zero]
      exact hξ

  ```

例2.3反证法

: 事实1

  任何有理数$`\frac{n}{m}`都可以化简成$`m`和$`n`不同时为偶数的形式. (如果有$`m`和$`n`都是
  偶数, 那么只要让分子和分母同时除以2, 我们就可以得到该有理数的更简单的形式.)

: 事实2

  对于某些整数$`a`和$`b`, 如果$`a = 2b`, 那么$`a`一定是偶数, 因为它可以被2整除.

: 事实3

  如果数$`a`是奇数, 那么$`a^2`也是奇数, 因为$`a^2`是一个奇数自加了奇数次.

命题: $`\sqrt{2}`不是有理数.
: 证:
  ```lean
  /--
  事实3
  -/
  axiom two_dvd_sqr_iff_two_dvd : ∀ a : ℤ, 2 ∣ a^2 ↔ 2 ∣ a

  #check Real.sq_sqrt
  /--
  不存在任何一个有理数`q`, 它的值是√2
  -/
  example : ¬∃ q : ℚ, q = √2 := by
    intro h
    apply h.elim; intro q hq
    --↑ alternatively, use `rcases h with ⟨q, hq⟩`
    have : (q : ℝ) ^ 2 = 2 := by
      rw [hq]
      rw [Real.sq_sqrt (show 0 ≤ 2 by simp)]
    have hq : q ^ 2 = 2 := by exact_mod_cast this
    --↑ 有了假设`h`: 存在有理数`q`, 该有理数的平方是2.
    rw [← Rat.num_div_den q] at hq
    --↑ 把`q`拆分成分数的形式`(q.num / q.den)`
    rw [div_pow] at hq
    --↑ 根据乘方分配率，把`^2`分配进除法
    have : q.den ≠ 0 := by simp
    have : q.den ^ 2 ≠ (0 : ℚ) := by simp
    rw [div_eq_iff this] at hq
    --↑ 把等式左侧的分母移动至等式右侧作为乘数
    have : 2 ∣ q.num ^ 2 := by --← 事实2
      show ∃ b, q.num ^ 2 = 2 * b
      apply Exists.intro ((q.den : ℤ)^2)
      --↑ 整除一定要在整数域讨论, 不要引入实数域!!!!!
      exact_mod_cast hq
    have q_num_is_even : 2 ∣ q.num := by
      rw [← two_dvd_sqr_iff_two_dvd]
      exact this
    have : ∃ b : ℤ, q.num = 2 * b := q_num_is_even
    --↑ 整除一定要在整数域讨论, 不要引入实数域!!!!!!!!!!!!!!
    --↑ 因为`∃ b : ℚ, q.num = 2 * b`永远成立!!!!!!!!!!!!
    rcases this with ⟨b, hb⟩
    --↑ 实际上整除↔存在, `rcases`↔`Exists.elim`
    rw [hb] at hq
    --↑ 使用`2*b`替换`q.num`
    rw_mod_cast [mul_pow] at hq
    have hq : 2 * 2 * b ^ 2 = 2 * q.den ^ 2 := hq
    rw [mul_assoc] at hq
    simp at hq
    have : 2 ∣ (q.den : ℤ) ^ 2 := by
      use b ^ 2
      exact hq.symm
    have q_den_is_even : 2 ∣ (q.den : ℤ) := by
      rw [← two_dvd_sqr_iff_two_dvd]
      exact this
    have q_num_abs_is_even : 2 ∣ (q.num.natAbs : ℤ) := by
      rw [Int.dvd_natAbs]
      exact q_num_is_even
    have q_den_is_even : 2 ∣ q.den := by
      exact_mod_cast q_den_is_even
    have q_num_coprime_den : Nat.Coprime q.num.natAbs q.den :=
      q.reduced
    --↑ 因为`q`是最简分数, 得出分子分母互质(coprime).
    --↓ 因为分子分母都可以被2整除, 得出分子分母的最大公因数(gcd)可以被2整除.
    have q_num_commdiv_den : 2 ∣ Nat.gcd q.num.natAbs q.den
    := by
      apply Nat.dvd_gcd
      · show 2 ∣ q.num.natAbs
        exact_mod_cast q_num_abs_is_even
      · show 2 ∣ q.den
        exact_mod_cast q_den_is_even
    rw [q_num_coprime_den.gcd_eq_one] at q_num_commdiv_den
    --↑ 把 `q_num_coprime_den.gcd_eq_one :`
    --↑ `Nat.Coprime q.num.natAbs q.den = 1`
    --↑ 带入`q_num_commdiv_den :`
    --↑ `2 | Nat.Coprime q.num.natAbs q.den`
    --↑ 引出矛盾: 2可以整除1`q_num_commdiv_den : 2 | 1`.
    simp at q_num_commdiv_den --← 直接`simp`.

  ```
