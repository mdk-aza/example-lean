/-
Peano 自然数と、その加算・乗算の定義
本の P-ZERO / P-SUCC / T-ZERO / T-SUCC の規則に対応する Lean コード
-/

/-- Peano 自然数 -/
inductive NatP where
  | Z  : NatP        -- 0 を表す
  | S  : NatP → NatP -- 後者 S(n)（n+1）
deriving Repr, DecidableEq

open NatP

/-
-------------------------------------------------------
  加算の定義（本の P-ZERO / P-SUCC に対応）
    P-ZERO:  Z plus n is n
    P-SUCC:  S(n1) plus n2 is S(n1 plus n2)
-------------------------------------------------------
-/
def add : NatP → NatP → NatP
  | Z,     n => n                -- P-ZERO 「0 + n = n」
  | S m, n => S (add m n)        -- P-SUCC 「(m+1) + n = S(m + n)」

/-
-------------------------------------------------------
  乗算の定義（本の T-ZERO / T-SUCC に対応）
    T-ZERO: Z times n is Z
    T-SUCC: S(n1) times n2 is n2 plus (n1 times n2)
-------------------------------------------------------
-/
def mul : NatP → NatP → NatP
  | Z,     _ => Z                -- T-ZERO 「0 × n = 0」
  | S m, n => add n (mul m n)    -- T-SUCC 「(m+1)×n = n + (m×n)」

/-- 中置記号（他の記号と衝突しない安全なバージョン） -/
infixl:65 " +ₙ " => add
infixl:70 " *ₙ " => mul

/-- 便利な定数 -/
def zero  : NatP := Z
def one   : NatP := S zero
def two   : NatP := S one
def three : NatP := S two
def four  : NatP := S three

/-
=======================================
  以下、本の例題に対応する証明たち
=======================================
-/

/-- 0 + 2 = 2 （P-ZERO） -/
theorem add_zero_two : zero +ₙ two = two := by
  -- add の定義を展開すれば rfl で証明できる

  -- refl（reflexivity）＝定義を展開したら左右同じになっている証明
  -- “定義を展開して左右が同じ形になれば rfl で証明できる”
  -- 1段階の “定義展開 + 反射律” が成立するときだけ使える
  rfl

theorem add_zero_two_manual : zero +ₙ two = two := by
  -- unfold は simp の代わりに「定義を自力で展開」
  unfold add
  -- unfold した結果は「Z, two => two」なので目標は two = two
  rfl

theorem add_zero_two_manual2 : zero +ₙ two = two := by
  unfold add
  -- ゴールは two = two になる
  apply Eq.refl

/-- 1 + 2 = 3 （P-SUCC）-/
theorem add_one_two : one +ₙ two = three := by
  rfl

theorem add_one_two_manual : one +ₙ two = three := by
  unfold add   -- unfold して「S Z + two = S (add Z two)」
  unfold add   -- add Z two = two を unfold
  -- ここでゴールは S two = three
  rfl

theorem add_one_two_manual2 : one +ₙ two = three := by
  -- one = S Z、two = S (S Z) を展開
  change add (S Z) (S (S Z)) = S (S (S Z))

  -- simp を使わないならこう
  unfold add

  unfold add   -- 2回展開すると「S (S (S Z)) = S (S (S Z))」

  exact rfl

/-- 2 + 2 = 4 -/
theorem add_two_two : two +ₙ two = four := by
  rfl

/-- 2 × 2 = 4 （T-SUCC を2回使う形）-/
theorem mul_two_two : two *ₙ two = four := by
  -- `simp` で定義を展開して簡約させる
  -- simp = 定義・定理をたくさん展開し、式を最大限簡単にして証明してくれるツール
  -- 多段階の展開を自動で探索して簡約する
  simp [two, one, zero, three, four, mul, add]

/-- 実行用 main -/
def main : IO Unit := do
  IO.println "Peano proofs loaded!"
