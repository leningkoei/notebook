import VersoManual


#doc (Verso.Genre.Manual) "基础数学与逻辑" =>

%%%
htmlSplit := .never
%%%


# 一些符号

* `∀`: Forall, 对于所有的、对于每一个、只要
* `∃`: Exists, 存在、存在某个

* `Σ`: 求和，例如$`\Sigma_{i=1}^{n}i`表示“从`i=1`一直到`i=n`，所有`i`的和”

* `ℕ`: Natural number, 全体自然数的集合
* `ℤ`: Zahlen, 全体整数的集合
* `ℚ`: Quotient, 全体有理数
* `ℝ`: Real number, 全体实数

# 形式逻辑

* `→`: 蕴含

* `↔`: 当且仅当

* 有命题`A → B`:
  * 逆命题: `B → A`, `∃ h : B → A, ¬(A → B)`
  * 否命题: `¬A → ¬B`, `∃ h : ¬A → ¬B, ¬(A → B)`
  * 逆否命题: `¬B → ¬A`, `¬B → ¬A ↔ A → B`

```Verso.Genre.Manual.InlineLean.lean

variable (α : Type) (A : α → Prop)

def prop1 : Prop := ¬∀ x : α, A x
def prop2 : Prop := ∃ x : α, ¬A x

```

