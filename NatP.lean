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

-- 📘 4. Lean で T-SUCC を証明規則として書くことはできるか？
-- できるが、Lean では通常は 「推論規則」ではなく「再帰定義」で書く」 のが普通。
-- ただし、推論規則として書き直すことも可能です：

/-- 足し算の「関係」版（P-ZERO / P-SUCC に対応） -/
inductive AddRel : NatP → NatP → NatP → Prop where
  | P_ZERO (n) :
      -- 0 plus n is n
      AddRel Z n n
  | P_SUCC (n1 n2 n3) :
      -- if n1 plus n2 is n3, then (n1+1) plus n2 is (n3+1)
      AddRel n1 n2 n3 →
      AddRel (S n1) n2 (S n3)

/-- 掛け算の「関係」版（T-ZERO / T-SUCC に対応） -/
inductive TimesRel : NatP → NatP → NatP → Prop where
  | T_ZERO (n) :
      -- 0 times n is 0
      TimesRel Z n Z
  | T_SUCC (n1 n2 n3 n4) :
      -- if  n1 × n2 is n3  and  n2 + n3 is n4
      TimesRel n1 n2 n3 →
      AddRel   n2 n3 n4 →
      -- then (n1+1) × n2 is n4
      TimesRel (S n1) n2 n4

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


/-
=======================================
  以下、本の例題に対応する証明たちを推論規則バージョンで動かす
=======================================
-/
example : AddRel one two three := by
  -- ステップ1: 0 plus 2 is 2 （P-ZERO）
  have h0 : AddRel zero two two :=
    AddRel.P_ZERO two
  -- ステップ2: 1 plus 2 is 3 （P-SUCC）
  exact AddRel.P_SUCC zero two two h0

example : AddRel two two four := by
  -- 0 plus 2 is 2
  have h0 : AddRel zero two two :=
    AddRel.P_ZERO two
  -- 1 plus 2 is 3
  have h1 : AddRel one  two three :=
    AddRel.P_SUCC zero two two h0
  -- 2 plus 2 is 4
  have h2 : AddRel two  two four :=
    AddRel.P_SUCC one  two three h1
  exact h2

example : TimesRel two two four := by
  -- 0 × 2 is 0
  have h0 : TimesRel zero two zero :=
    TimesRel.T_ZERO two

  -- 2 plus 0 is 2（P-ZERO + P-SUCC ×2）
  have h_add_20 : AddRel two zero two := by
    have hz : AddRel zero zero zero :=
      AddRel.P_ZERO zero
    have h1 : AddRel one  zero one  :=
      AddRel.P_SUCC zero zero zero hz
    have h2 : AddRel two  zero two  :=
      AddRel.P_SUCC one  zero one  h1
    exact h2

  -- 1 × 2 is 2（T-SUCC, n1=0, n2=2, n3=0, n4=2）
  have h1_times : TimesRel one two two :=
    TimesRel.T_SUCC zero two zero two h0 h_add_20

  -- 2 plus 2 is 4（さっきの h2 を再利用）
  have h_add_22 : AddRel two two four := by
    have hz : AddRel zero two two :=
      AddRel.P_ZERO two
    have h1 : AddRel one  two three :=
      AddRel.P_SUCC zero two two hz
    have h2 : AddRel two  two four  :=
      AddRel.P_SUCC one  two three h1
    exact h2

  -- 2 × 2 is 4（T-SUCC, n1=1, n2=2, n3=2, n4=4）
  exact TimesRel.T_SUCC one two two four h1_times h_add_22


/-- 実行用 main -/
def main : IO Unit := do
  IO.println "Peano proofs loaded!"
