/-
POJ 3278 "Catch That Cow" —— 形式化与机器验证（Lean 4，仅用核心库，无需 Mathlib）

问题：农夫位于 n，牛位于 k（非负整数，0 ≤ n, k ≤ 100000）。
每步可执行三种移动之一：n → n+1，n → n−1（n > 0），n → 2n（n > 0）。
求到达 k 所需的最少步数。

本文件第一部分：
  * `Step` / `Reach`：移动规则与「s 步可达」的归纳定义；
  * `dist n k`：最少步数的严格定义（所有满足 Reach n k s 的 s 之最小值）；
  * `Bwd`：反向（自 k 倒推）路径关系，以及路径反转定理 `Reach n k s ↔ Bwd k n s`；
  * `f`：O(log k) 的递归解，主定理 `f_eq_dist : f n k = dist n k`，
    即 **f 的输出确实是可达的最少步数**。
-/

namespace Poj3278

/-! ## 〇、通用工具：强归纳与最小元 -/

theorem nat_strong_induction {P : Nat → Prop} (h : ∀ m, (∀ j, j < m → P j) → P m) :
    ∀ m, P m := by
  have key : ∀ m j, j ≤ m → P j := by
    intro m
    induction m with
    | zero =>
      intro j hj
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0
      exact h 0 (fun _ hi => absurd hi (Nat.not_lt_zero _))
    | succ m ihs =>
      intro j hj
      exact h j (fun i hi => ihs i (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hi hj)))
  intro m
  exact key m m (Nat.le_refl m)

/-- 任意可满足的 Nat 谓词存在最小元。 -/
theorem exists_min {P : Nat → Prop} : ∀ s, P s → ∃ m, P m ∧ ∀ j, P j → m ≤ j := by
  apply nat_strong_induction
  intro s ih hs
  by_cases hex : ∃ j, P j ∧ j < s
  · have ⟨j, hj, hjlt⟩ := hex
    exact ih j hjlt hj
  · refine ⟨s, hs, fun j hj => ?_⟩
    cases Nat.lt_or_ge j s with
    | inl hjlt => exact absurd ⟨j, hj, hjlt⟩ hex
    | inr hge => exact hge

/-! ## 一、移动规则与可达性 -/

/-- 前向一步移动。-1 与 ×2 要求起点 > 0（对应 BFS 里 `next >= 0` 的边界检查）。 -/
inductive Step : Nat → Nat → Prop
  | plus  (x : Nat) : Step x (x + 1)
  | minus (x : Nat) : Step (x + 1) x
  | dbl   (x : Nat) : Step (x + 1) (2 * (x + 1))

/-- `Reach n k s`：从 n 出发恰好 s 步到达 k。 -/
inductive Reach : Nat → Nat → Nat → Prop
  | refl (x : Nat) : Reach x x 0
  | step {x y z s : Nat} (h : Step x y) (r : Reach y z s) : Reach x z (s + 1)

theorem reach_zero {a b : Nat} (h : Reach a b 0) : a = b :=
  match h with | .refl _ => rfl

/-- 路径末尾追加一步。 -/
theorem reach_snoc {a c t b : Nat} (h : Reach a c t) (hs : Step c b) : Reach a b (t + 1) :=
  match h with
  | .refl _ => .step hs (.refl b)
  | .step hs' r => .step hs' (reach_snoc r hs)

theorem reach_trans {a b t : Nat} (h : Reach a b t) :
    ∀ {c u : Nat}, Reach b c u → Reach a c (t + u) := by
  induction h with
  | refl x => intro c u h2; rw [Nat.zero_add]; exact h2
  | @step x y z s hs r ih =>
    intro c u h2
    rw [show s + 1 + u = s + u + 1 from by omega]
    exact .step hs (ih h2)

/-- 一路 +1：n ≤ k 时 k − n 步可达。 -/
theorem reach_up : ∀ (k n : Nat), n ≤ k → Reach n k (k - n) := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have hn0 : n = 0 := Nat.le_zero.mp hn
    subst hn0
    exact .refl 0
  | succ m ih =>
    intro n hn
    by_cases h : n ≤ m
    · have he : m + 1 - n = (m - n) + 1 := by omega
      rw [he]
      exact reach_snoc (ih n h) (.plus m)
    · have hne : n = m + 1 := by omega
      subst hne
      rw [Nat.sub_self]
      exact .refl (m + 1)

/-- 一路 -1：k ≤ n 时 n − k 步可达。 -/
theorem reach_down : ∀ (n k : Nat), k ≤ n → Reach n k (n - k) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    exact .refl 0
  | succ m ih =>
    intro k hk
    by_cases h : k ≤ m
    · have he : m + 1 - k = (m - k) + 1 := by omega
      rw [he]
      exact .step (.minus m) (ih k h)
    · have hke : k = m + 1 := by omega
      subst hke
      rw [Nat.sub_self]
      exact .refl (m + 1)

/-- 关键下界：任何从 n 到 k 的 s 步路径都满足 n ≤ k + s。 -/
theorem reach_le : ∀ {n k s : Nat}, Reach n k s → n ≤ k + s := by
  intro n k s h
  induction h with
  | refl x => omega
  | step hs _ ih => cases hs <;> omega

theorem reach_exists (n k : Nat) : ∃ s, Reach n k s := by
  by_cases h : n ≤ k
  · exact ⟨k - n, reach_up k n h⟩
  · exact ⟨n - k, reach_down n k (by omega)⟩

theorem reach_min (n k : Nat) : ∃ m, Reach n k m ∧ ∀ j, Reach n k j → m ≤ j := by
  have ⟨s0, hs0⟩ := reach_exists n k
  exact exists_min s0 hs0

/-- **最少步数**：所有满足 `Reach n k s` 的 s 中的最小值。 -/
noncomputable def dist (n k : Nat) : Nat := Classical.choose (reach_min n k)

theorem dist_reach (n k : Nat) : Reach n k (dist n k) :=
  (Classical.choose_spec (reach_min n k)).1

theorem dist_le_of_reach {n k s : Nat} (h : Reach n k s) : dist n k ≤ s :=
  (Classical.choose_spec (reach_min n k)).2 s h

theorem dist_pos {n k : Nat} (h : n ≠ k) : 0 < dist n k := by
  cases Nat.eq_zero_or_pos (dist n k) with
  | inl he =>
    have hr := dist_reach n k
    rw [he] at hr
    exact absurd (reach_zero hr) h
  | inr hp => exact hp

/-- 目标在起点左边（k ≤ n）时，答案就是 n − k。 -/
theorem dist_eq_of_ge (n k : Nat) (hk : k ≤ n) : dist n k = n - k := by
  have h1 : dist n k ≤ n - k := dist_le_of_reach (reach_down n k hk)
  have h2 : n - k ≤ dist n k := by
    have hr := reach_le (dist_reach n k)
    omega
  omega

/-! ## 二、反向路径（自 k 倒推）与路径反转 -/

/-- 反向一步：x 倒推到 y ⟺ 正向存在移动 y → x。 -/
def BwdStep (x y : Nat) : Prop := Step y x

/-- `Bwd k n s`：从 k 沿反方向（k → k±1；偶数 k → k/2）恰好 s 步倒推到 n。 -/
inductive Bwd : Nat → Nat → Nat → Prop
  | refl (x : Nat) : Bwd x x 0
  | step {x y z s : Nat} (h : BwdStep x y) (r : Bwd y z s) : Bwd x z (s + 1)

theorem bwd_zero {a b : Nat} (h : Bwd a b 0) : a = b :=
  match h with | .refl _ => rfl

theorem bwd_snoc {a c t b : Nat} (h : Bwd a c t) (hs : BwdStep c b) : Bwd a b (t + 1) :=
  match h with
  | .refl _ => .step hs (.refl b)
  | .step hs' r => .step hs' (bwd_snoc r hs)

theorem bwd_trans {a b t : Nat} (h : Bwd a b t) :
    ∀ {c u : Nat}, Bwd b c u → Bwd a c (t + u) := by
  induction h with
  | refl x => intro c u h2; rw [Nat.zero_add]; exact h2
  | @step x y z s hs r ih =>
    intro c u h2
    rw [show s + 1 + u = s + u + 1 from by omega]
    exact .step hs (ih h2)

/-- **路径反转**：正向 n→k 的 s 步路径 ↔ 反向 k 倒推到 n 的 s 步路径。 -/
theorem bwd_of_reach {n k s : Nat} (h : Reach n k s) : Bwd k n s :=
  match h with
  | .refl _ => .refl _
  | .step hs r => bwd_snoc (bwd_of_reach r) hs

theorem reach_of_bwd {n k s : Nat} (h : Bwd k n s) : Reach n k s :=
  match h with
  | .refl _ => .refl _
  | .step hs r => reach_snoc (reach_of_bwd r) hs

theorem bwd_exists (k n : Nat) : ∃ s, Bwd k n s := by
  cases reach_exists n k with
  | intro s hs => exact ⟨s, bwd_of_reach hs⟩

theorem bwd_min (k n : Nat) : ∃ m, Bwd k n m ∧ ∀ j, Bwd k n j → m ≤ j := by
  have ⟨s0, hs0⟩ := bwd_exists k n
  exact exists_min s0 hs0

/-- 反向最少步数。 -/
noncomputable def bdist (k n : Nat) : Nat := Classical.choose (bwd_min k n)

theorem bdist_bwd (k n : Nat) : Bwd k n (bdist k n) :=
  (Classical.choose_spec (bwd_min k n)).1

theorem bdist_le_of_bwd {k n s : Nat} (h : Bwd k n s) : bdist k n ≤ s :=
  (Classical.choose_spec (bwd_min k n)).2 s h

/-- 反向最少步数 = 正向最少步数（路径反转的直接推论）。 -/
theorem dist_eq_bdist (n k : Nat) : dist n k = bdist k n := by
  have h1 : dist n k ≤ bdist k n := dist_le_of_reach (reach_of_bwd (bdist_bwd k n))
  have h2 : bdist k n ≤ dist n k := bdist_le_of_bwd (bwd_of_reach (dist_reach n k))
  omega

theorem bdist_pos {k n : Nat} (h : k ≠ n) : 0 < bdist k n := by
  have h0 := dist_pos (n := n) (k := k) (fun hc => h hc.symm)
  rwa [dist_eq_bdist n k] at h0

/-- BwdStep 的判别：反向一步 x → y 只有三种可能。 -/
theorem bwdStep_inv {x y : Nat} (h : BwdStep x y) :
    (y + 1 = x) ∨ (x + 1 = y) ∨ (0 < y ∧ 2 * y = x) := by
  unfold BwdStep at h
  cases h with
  | plus w => left; rfl
  | minus w => right; left; rfl
  | dbl w => right; right; exact ⟨by omega, rfl⟩

/-- 反向第一步的分解。 -/
theorem bwd_first {x z t : Nat} (h : Bwd x z (t + 1)) : ∃ y, BwdStep x y ∧ Bwd y z t :=
  match h with | .step hs r => ⟨_, hs, r⟩

/-- 从 a+d 一路下行到 a。 -/
theorem bwd_walk : ∀ (d a : Nat), Bwd (a + d) a d
  | 0, a => .refl a
  | d + 1, a => .step (Step.plus (a + d)) (bwd_walk d a)

/-- 从 a 一路上行到 a+d。 -/
theorem bwd_climb : ∀ (d a : Nat), Bwd a (a + d) d
  | 0, a => .refl a
  | d + 1, a => bwd_snoc (bwd_climb d a) (Step.minus (a + d))

/-- 单调性：bdist a n ≤ t + bdist b n，只要 a 可 t 步倒推到 b。 -/
theorem bdist_le_of_bwd_walk {a b t n : Nat} (h : Bwd a b t) : bdist a n ≤ t + bdist b n :=
  bdist_le_of_bwd (bwd_trans h (bdist_bwd b n))

theorem bdist_le_down (a b n : Nat) (h : b ≤ a) : bdist a n ≤ (a - b) + bdist b n := by
  have h2 := bwd_walk (a - b) b
  have hEq : b + (a - b) = a := by omega
  rw [hEq] at h2
  exact bdist_le_of_bwd_walk h2

theorem bdist_le_climb (a b n : Nat) (h : a ≤ b) : bdist a n ≤ (b - a) + bdist b n := by
  have h2 := bwd_climb (b - a) a
  have hEq : a + (b - a) = b := by omega
  rw [hEq] at h2
  exact bdist_le_of_bwd_walk h2

/-- 一步反向移动给出的上界。 -/
theorem bdist_step_le {x y n : Nat} (hs : BwdStep x y) : bdist x n ≤ 1 + bdist y n := by
  have h := Bwd.step hs (bdist_bwd y n)
  have hEq : bdist y n + 1 = 1 + bdist y n := by omega
  rw [hEq] at h
  exact bdist_le_of_bwd h

/-! ## 三、只用 ±1 的路径 与「首次减半」分解 -/

/-- `Bwd1 a b t`：从 a 只用 ±1 两类反向移动 t 步到 b。 -/
inductive Bwd1 : Nat → Nat → Nat → Prop
  | refl (x : Nat) : Bwd1 x x 0
  | down {x y z s : Nat} (h : y + 1 = x) (r : Bwd1 y z s) : Bwd1 x z (s + 1)
  | up {x y z s : Nat} (h : y = x + 1) (r : Bwd1 y z s) : Bwd1 x z (s + 1)

/-- ±1 路径的位移下界：|a − b| ≤ t。 -/
theorem bwd1_le : ∀ {a b t : Nat}, Bwd1 a b t → a ≤ b + t ∧ b ≤ a + t := by
  intro a b t h
  induction h with
  | refl x => omega
  | down h _ ih => omega
  | up h _ ih => omega

/-- **首次减半分解**：任何反向路径要么全程 ±1（则 k ≤ n + s），
要么形如：先 t 步 ±1 到达某个偶数 2q，再减半到 q，再 s' 步到 n。 -/
theorem bwd_split {k n s : Nat} (h : Bwd k n s) :
    k ≤ n + s ∨ ∃ q t s', t + 1 + s' ≤ s ∧ 0 < q ∧ Bwd1 k (2 * q) t ∧ Bwd q n s' := by
  induction h with
  | refl x => exact Or.inl (Nat.le_refl x)
  | @step x y z s hs r ih =>
    cases bwdStep_inv hs with
    | inl he => -- 反向一步 x → y 向下（y + 1 = x）
      cases ih with
      | inl hle => exact Or.inl (by omega)
      | inr hex =>
        have ⟨q, t, s', hle, hq, h1, h2⟩ := hex
        refine Or.inr ⟨q, t + 1, s', by omega, hq, ?_, h2⟩
        exact Bwd1.down (by omega) h1
    | inr h2 =>
      cases h2 with
      | inl he => -- 反向一步 x → y 向上（x + 1 = y）
        cases ih with
        | inl hle => exact Or.inl (by omega)
        | inr hex =>
          have ⟨q, t, s', hle, hq, h1, h2⟩ := hex
          refine Or.inr ⟨q, t + 1, s', by omega, hq, ?_, h2⟩
          exact Bwd1.up (by omega) h1
      | inr h3 => -- 反向一步 x → y 是减半（x = 2y, y > 0）
        have ⟨hq, hy2⟩ := h3
        rw [← hy2]
        exact Or.inr ⟨y, 0, s, by omega, hq, Bwd1.refl (2 * y), r⟩

/-! ## 四、bdist 的递推（贪心解的数学基础） -/

/-- **奇数情形**（n < 2m+1）：从奇数 2m+1 倒推，第一步只能是 2m 或 2m+2。 -/
theorem bdist_odd {n m : Nat} (hNK : n < 2 * m + 1) :
    bdist (2 * m + 1) n = 1 + min (bdist (2 * m) n) (bdist (2 * m + 2) n) := by
  have hle1 : bdist (2 * m + 1) n ≤ 1 + bdist (2 * m) n :=
    bdist_step_le (Step.plus (2 * m))
  have hle2 : bdist (2 * m + 1) n ≤ 1 + bdist (2 * m + 2) n :=
    bdist_step_le (Step.minus (2 * m + 1))
  have hge : 1 + min (bdist (2 * m) n) (bdist (2 * m + 2) n) ≤ bdist (2 * m + 1) n := by
    have hb := bdist_bwd (2 * m + 1) n
    cases hd : bdist (2 * m + 1) n with
    | zero =>
      rw [hd] at hb
      exact absurd (bwd_zero hb) (by omega)
    | succ t =>
      rw [hd] at hb
      have ⟨y, hs1, hs2⟩ := bwd_first hb
      have hlow : bdist y n ≤ t := bdist_le_of_bwd hs2
      cases bwdStep_inv hs1 with
      | inl he =>
        have hy : y = 2 * m := by omega
        subst hy
        omega
      | inr h2 =>
        cases h2 with
        | inl he =>
          have hy : y = 2 * m + 2 := by omega
          subst hy
          omega
        | inr h3 => omega -- 2y = 2m+1 不可能
  omega

/-- **偶数情形**（n < 2(w+1)）：最少步数 = min(差值, 1 + 从一半倒推)。 -/
theorem bdist_even {n w : Nat} (hNK : n < 2 * (w + 1)) :
    bdist (2 * (w + 1)) n = min (2 * (w + 1) - n) (1 + bdist (w + 1) n) := by
  have hle1 : bdist (2 * (w + 1)) n ≤ 2 * (w + 1) - n := by
    have h2 := bwd_walk (2 * (w + 1) - n) n
    have hEq : n + (2 * (w + 1) - n) = 2 * (w + 1) := by omega
    rw [hEq] at h2
    exact bdist_le_of_bwd h2
  have hle2 : bdist (2 * (w + 1)) n ≤ 1 + bdist (w + 1) n :=
    bdist_step_le (Step.dbl w)
  have hge : min (2 * (w + 1) - n) (1 + bdist (w + 1) n) ≤ bdist (2 * (w + 1)) n := by
    have hb := bdist_bwd (2 * (w + 1)) n
    cases hd : bdist (2 * (w + 1)) n with
    | zero =>
      rw [hd] at hb
      exact absurd (bwd_zero hb) (by omega)
    | succ t =>
      rw [hd] at hb
      have ⟨y, hs1, hs2⟩ := bwd_first hb
      have hlow : bdist y n ≤ t := bdist_le_of_bwd hs2
      cases bwdStep_inv hs1 with
      | inl he => -- 下行到 y = 2w+1
        cases bwd_split hs2 with
        | inl hle => omega
        | inr hex =>
          have ⟨q, t1, s', hle, hq, hb1, hb2⟩ := hex
          have hbq : bdist q n ≤ s' := bdist_le_of_bwd hb2
          have hb1' := bwd1_le hb1
          by_cases hqw : q ≤ w + 1
          · have hbnd := bdist_le_down (w + 1) q n hqw
            omega
          · have hbnd := bdist_le_climb (w + 1) q n (by omega)
            omega
      | inr h2 =>
        cases h2 with
        | inl he => -- 上行到 y = 2w+3
          cases bwd_split hs2 with
          | inl hle => omega
          | inr hex =>
            have ⟨q, t1, s', hle, hq, hb1, hb2⟩ := hex
            have hbq : bdist q n ≤ s' := bdist_le_of_bwd hb2
            have hb1' := bwd1_le hb1
            by_cases hqw : q ≤ w + 1
            · have hbnd := bdist_le_down (w + 1) q n hqw
              omega
            · have hbnd := bdist_le_climb (w + 1) q n (by omega)
              omega
        | inr h3 => -- 减半到 y = w+1
          have hy : y = w + 1 := by omega
          subst hy
          omega
  omega

/-! ## 五、O(log) 递归解 f 及其正确性 -/

/-- O(log k) 递归解：
  * k ≤ n：答案 n − k；
  * n < k ≤ 1：即 (0,1)，答案 1；
  * k 为偶数：min(k − n, 1 + f n (k/2))；
  * k 为奇数：1 + min(f n (k−1), min(k+1−n, 1 + f n ((k+1)/2)))。 -/
def f (n k : Nat) : Nat :=
  if k ≤ n then n - k
  else if h1 : k ≤ 1 then k - n
  else if h2 : k % 2 = 0 then min (k - n) (1 + f n (k / 2))
  else 1 + min (f n (k - 1)) (min (k + 1 - n) (1 + f n ((k + 1) / 2)))
termination_by k
decreasing_by
  all_goals omega

theorem f_eq : ∀ (k n : Nat), f n k = bdist k n := by
  apply nat_strong_induction
  intro k ih n
  rw [f]
  split
  · next hk1 =>
    exact (dist_eq_of_ge n k hk1).symm.trans (dist_eq_bdist n k)
  · next hk1 =>
    split
    · next hk2 =>
      have hk1' : k = 1 := by omega
      subst hk1'
      have hn0 : n = 0 := by omega
      subst hn0
      rw [Nat.sub_zero]
      have hle : bdist 1 0 ≤ 1 :=
        bdist_le_of_bwd (bwd_of_reach (Reach.step (Step.plus 0) (Reach.refl 1)))
      have hpos : 0 < bdist 1 0 := bdist_pos (by omega)
      omega
    · next hk2 =>
      split
      · next hpar =>
        -- 偶数：k = 2(w+1)
        have hkge2 : 2 ≤ k := by omega
        cases hd : k / 2 with
        | zero => exact absurd hd (by omega)
        | succ w =>
          have hkW : k = 2 * (w + 1) := by omega
          subst hkW
          have hih : f n (w + 1) = bdist (w + 1) n := ih (w + 1) (by omega) n
          rw [hih]
          exact (bdist_even (by omega)).symm
      · next hpar =>
        -- 奇数：k = 2w+1，w ≥ 1
        have hkge3 : 3 ≤ k := by omega
        cases hd : (k + 1) / 2 with
        | zero => exact absurd hd (by omega)
        | succ w =>
          have hkW : k = 2 * w + 1 := by omega
          subst hkW
          have hih1 : f n (2 * w) = bdist (2 * w) n := ih (2 * w) (by omega) n
          have hih2 : f n (w + 1) = bdist (w + 1) n := ih (w + 1) (by omega) n
          rw [show 2 * w + 1 - 1 = 2 * w from by omega,
              show 2 * w + 1 + 1 - n = 2 * w + 2 - n from by omega,
              hih1, hih2]
          have hE : bdist (2 * w + 2) n = min (2 * w + 2 - n) (1 + bdist (w + 1) n) :=
            bdist_even (by omega)
          have hO : bdist (2 * w + 1) n = 1 + min (bdist (2 * w) n) (bdist (2 * w + 2) n) :=
            bdist_odd (by omega)
          omega

/-- **主定理（第一部分）**：f n k = dist n k，即 f 的输出是最少步数。 -/
theorem f_eq_dist (n k : Nat) : f n k = dist n k := by
  rw [f_eq, dist_eq_bdist]

/-- **最少步数的完整刻画**：f n k 步确实可达，且任何路径步数都不小于它。 -/
theorem f_is_minimal (n k : Nat) :
    Reach n k (f n k) ∧ ∀ s, Reach n k s → f n k ≤ s := by
  rw [f_eq_dist]
  exact ⟨dist_reach n k, fun _ hs => dist_le_of_reach hs⟩

/-! ## 六、2 的幂的基本事实 -/

theorem two_pow_pos (d : Nat) : 0 < 2 ^ d := by
  induction d with
  | zero => decide
  | succ d ih => rw [Nat.pow_succ]; omega

theorem two_pow_ge (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := two_pow_pos n
    rw [Nat.pow_succ]
    omega

theorem two_pow_mono {d e : Nat} (h : d ≤ e) : 2 ^ d ≤ 2 ^ e :=
  Nat.pow_le_pow_right (by decide) h

/-- 绝对值（Nat 上的 |a − b|）。 -/
def absg (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-! ## 七、NAF 权重 nafW（对应 C++ 的 weight_naf） -/

/-- nafW n = 把 n 写成带符号 2 的幂（±2^e 之和）所需的最少项数。
这正是 C++ 代码 `weight_naf` 的数学内容。 -/
def nafW (n : Nat) : Nat :=
  if h0 : n ≤ 1 then n
  else if h1 : n % 2 = 0 then nafW (n / 2)
  else 1 + min (nafW ((n - 1) / 2)) (nafW ((n + 1) / 2))
termination_by n
decreasing_by
  all_goals omega

@[simp] theorem nafW_zero : nafW 0 = 0 := by
  rw [nafW]
  rfl

@[simp] theorem nafW_one : nafW 1 = 1 := by
  rw [nafW]
  rfl

theorem nafW_two_mul (m : Nat) : nafW (2 * m) = nafW m := by
  cases m with
  | zero => rfl
  | succ w =>
    rw [nafW, dite_eq_right (by omega : ¬(2 * (w + 1) ≤ 1)),
        dite_eq_left (by omega : (2 * (w + 1)) % 2 = 0),
        show 2 * (w + 1) / 2 = w + 1 from by omega]

theorem nafW_two_mul_add_one (m : Nat) :
    nafW (2 * m + 1) = 1 + min (nafW m) (nafW (m + 1)) := by
  cases m with
  | zero =>
    show nafW 1 = 1 + min (nafW 0) (nafW 1)
    rw [nafW_zero, nafW_one]
    omega
  | succ w =>
    rw [nafW, dite_eq_right (by omega : ¬(2 * (w + 1) + 1 ≤ 1)),
        dite_eq_right (by omega : ¬((2 * (w + 1) + 1) % 2 = 0)),
        show (2 * (w + 1) + 1 - 1) / 2 = w + 1 from by omega,
        show (2 * (w + 1) + 1 + 1) / 2 = w + 1 + 1 from by omega]

theorem nafW_pos (x : Nat) (hx : 0 < x) : 0 < nafW x := by
  induction x using nat_strong_induction with
  | _ x ih =>
    by_cases hx2 : x ≤ 1
    · have hx1 : x = 1 := by omega
      subst hx1
      rw [nafW_one]
      omega
    · have hpar : x % 2 = 0 ∨ x % 2 = 1 := by omega
      cases hpar with
      | inl h =>
        have hxm : x = 2 * (x / 2) := by omega
        rw [hxm, nafW_two_mul]
        exact ih (x / 2) (by omega) (by omega)
      | inr h =>
        have hxm : x = 2 * (x / 2) + 1 := by omega
        rw [hxm, nafW_two_mul_add_one]
        omega

theorem nafW_two_pow (d : Nat) : nafW (2 ^ d) = 1 := by
  induction d with
  | zero => exact nafW_one
  | succ d ih =>
    rw [Nat.pow_succ, show 2 ^ d * 2 = 2 * 2 ^ d from Nat.mul_comm _ _, nafW_two_mul, ih]

theorem nafW_two_pow_sub_one (d : Nat) : nafW (2 ^ d - 1) ≤ 2 := by
  induction d with
  | zero =>
    show nafW 0 ≤ 2
    have := nafW_zero
    omega
  | succ d ih =>
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1 := nafW_two_mul_add_one (2 ^ d - 1)
    have h2 := nafW_two_pow d
    have hPos : (1:Nat) ≤ 2 ^ d := two_pow_pos d
    have hCancel : 2 ^ d - 1 + 1 = 2 ^ d := by omega
    show nafW (2 ^ (d+1) - 1) ≤ 2
    rw [show 2 ^ (d + 1) - 1 = 2 * (2 ^ d - 1) + 1 from by omega, h1, hCancel]
    omega

/-! ## 八、带符号 2 的幂的表示 CR -/

/-- ipow e = 2^e（Int 版）。 -/
def ipow (e : Nat) : Int := ((2:Nat) ^ e : Int)

theorem ipow_pos (e : Nat) : 0 < ipow e := by
  have := two_pow_pos e
  unfold ipow
  omega

theorem ipow_succ (e : Nat) : ipow (e + 1) = 2 * ipow e := by
  show (((2:Nat) ^ (Nat.succ e) : Nat) : Int) = 2 * (((2:Nat) ^ e : Nat) : Int)
  rw [Nat.pow_succ]
  omega

theorem nat_cast_mul (m n : Nat) : ((m * n : Nat) : Int) = (m : Int) * (n : Int) := by omega

theorem cast_mul_pow (a d : Nat) : ((a * 2 ^ d : Nat) : Int) = (a : Int) * ipow d := by
  rw [nat_cast_mul]
  rfl

theorem two_mul_comm_int (a b : Int) : (2 * a) * b = a * (2 * b) := by
  have e1 : (2 * a) * b = 2 * (a * b) := Int.mul_assoc 2 a b
  have e2 : a * (2 * b) = (a * b) * 2 := by
    rw [Int.mul_comm 2 b, ← Int.mul_assoc]
  have e3 : 2 * (a * b) = (a * b) * 2 := Int.mul_comm 2 (a * b)
  omega

/-- `CR d v t`：整数 v 可以写成恰好 t 个带符号 2 的幂之和，指数均 ≤ d。 -/
inductive CR (d : Nat) : Int → Nat → Prop
  | zero : CR d 0 0
  | addT {v : Int} {t e : Nat} (h : e ≤ d) (r : CR d v t) : CR d (v + ipow e) (t + 1)
  | subT {v : Int} {t e : Nat} (h : e ≤ d) (r : CR d v t) : CR d (v - ipow e) (t + 1)

theorem CR_inv_zero {d : Nat} {v : Int} (h : CR d v 0) : v = 0 :=
  match h with | .zero => rfl

theorem CR_inv_succ {d : Nat} {v : Int} {t : Nat} (h : CR d v (t + 1)) :
    ∃ (e : Nat) (v' : Int), e ≤ d ∧ (v = v' + ipow e ∨ v = v' - ipow e) ∧ CR d v' t :=
  match h with
  | .addT he r => ⟨_, _, he, Or.inl rfl, r⟩
  | .subT he r => ⟨_, _, he, Or.inr rfl, r⟩

theorem CR_neg {d : Nat} {v : Int} {t : Nat} (h : CR d v t) : CR d (-v) t := by
  induction h with
  | zero => exact .zero
  | @addT v t e he r ih =>
    have hEq : -(v + ipow e) = -v - ipow e := by omega
    rw [hEq]
    exact .subT he ih
  | @subT v t e he r ih =>
    have hEq : -(v - ipow e) = -v + ipow e := by omega
    rw [hEq]
    exact .addT he ih

theorem CR_mono {d d' : Nat} (hdd : d ≤ d') : ∀ {v : Int} {t : Nat}, CR d v t → CR d' v t := by
  intro v t h
  induction h with
  | zero => exact .zero
  | @addT v t e he r ih => exact .addT (Nat.le_trans he hdd) ih
  | @subT v t e he r ih => exact .subT (Nat.le_trans he hdd) ih

theorem CR_join {d : Nat} : ∀ {a b : Int} {t1 t2 : Nat},
    CR d a t1 → CR d b t2 → CR d (a + b) (t1 + t2) := by
  intro a b t1 t2 h1 h2
  induction h1 with
  | zero =>
    rw [Int.zero_add, Nat.zero_add]
    exact h2
  | @addT a t e he r ih =>
    have hEq : a + ipow e + b = (a + b) + ipow e := by omega
    rw [hEq, show t + 1 + t2 = t + t2 + 1 from by omega]
    exact .addT he ih
  | @subT a t e he r ih =>
    have hEq : a - ipow e + b = (a + b) - ipow e := by omega
    rw [hEq, show t + 1 + t2 = t + t2 + 1 from by omega]
    exact .subT he ih

theorem CR_double {d : Nat} : ∀ {v : Int} {t : Nat}, CR d v t → CR (d + 1) (2 * v) t := by
  intro v t h
  induction h with
  | zero => exact .zero
  | @addT v t e he r ih =>
    have hEq : 2 * (v + ipow e) = 2 * v + ipow (e + 1) := by
      rw [ipow_succ]; omega
    rw [hEq]
    exact .addT (by omega) ih
  | @subT v t e he r ih =>
    have hEq : 2 * (v - ipow e) = 2 * v - ipow (e + 1) := by
      rw [ipow_succ]; omega
    rw [hEq]
    exact .subT (by omega) ih

/-- nafW 的构造性：r < 2^d 时，r 本身就有 nafW r 项、指数 ≤ d 的表示。 -/
theorem nafW_rep : ∀ (d r : Nat), r < 2 ^ d → CR d r (nafW r) := by
  intro d
  induction d with
  | zero =>
    intro r hr
    have hr0 : r = 0 := by omega
    subst hr0
    rw [nafW_zero]
    exact .zero
  | succ d ih =>
    intro r hr
    have hpar : r % 2 = 0 ∨ r % 2 = 1 := by omega
    cases hpar with
    | inl he =>
      have hrm : r = 2 * (r / 2) := by omega
      rw [hrm, nafW_two_mul]
      exact CR_double (ih (r / 2) (by omega))
    | inr ho =>
      have hrm : r = 2 * (r / 2) + 1 := by omega
      rw [hrm, nafW_two_mul_add_one]
      by_cases hmin : nafW (r / 2) ≤ nafW (r / 2 + 1)
      · -- 下行分支：先翻倍再 +1
        have hminEq : min (nafW (r / 2)) (nafW (r / 2 + 1)) = nafW (r / 2) := by omega
        have hcast : (((2 * (r / 2) + 1 : Nat)) : Int)
            = 2 * (((r / 2 : Nat) : Int)) + 1 := by omega
        rw [hcast, hminEq, show 1 + nafW (r / 2) = nafW (r / 2) + 1 from by omega]
        have h1 : CR (d + 1) (2 * (((r / 2 : Nat) : Int))) (nafW (r / 2)) :=
          CR_double (ih (r / 2) (by omega))
        exact CR.addT (Nat.zero_le _) h1
      · -- 上行分支：先翻倍 (r/2 + 1) 再 −1
        have hminEq : min (nafW (r / 2)) (nafW (r / 2 + 1)) = nafW (r / 2 + 1) := by omega
        rw [hminEq, show 1 + nafW (r / 2 + 1) = nafW (r / 2 + 1) + 1 from by omega]
        by_cases hEq2 : r / 2 + 1 = 2 ^ d
        · -- r = 2^{d+1} - 1：用 {2^{d+1}, -1} 两项表示，共 2 项
          have hp2 := nafW_two_pow d
          rw [← hEq2] at hp2
          have h1 : CR (d + 1) (ipow (d + 1)) 1 := by
            have h0 := CR.addT (Nat.le_refl (d + 1)) (CR.zero (d := d + 1))
            rw [Int.zero_add] at h0
            exact h0
          have h2 : CR (d + 1) (ipow (d + 1) - 1) 2 := CR.subT (Nat.zero_le _) h1
          have hE2 : (((2 * (r / 2) + 1 : Nat)) : Int) = ipow (d + 1) - 1 := by
            have hc : ((2 ^ d : Nat) : Int) = ipow d := rfl
            have hps := ipow_succ d
            omega
          rw [hE2, show nafW (r / 2 + 1) + 1 = 2 from by omega]
          exact h2
        · have h1 : CR (d + 1) (2 * (((r / 2 + 1 : Nat)) : Int)) (nafW (r / 2 + 1)) :=
            CR_double (ih (r / 2 + 1) (by omega))
          have h2 : CR (d + 1) (2 * (((r / 2 + 1 : Nat)) : Int) - 1) (nafW (r / 2 + 1) + 1) :=
            CR.subT (Nat.zero_le _) h1
          have hE : (((2 * (r / 2) + 1 : Nat)) : Int)
              = 2 * (((r / 2 + 1 : Nat)) : Int) - 1 := by omega
          rw [hE]
          exact h2

/-- 奇数的表示中必有一个 ±1 项，可以摘除。 -/
theorem CR_odd_ext {d : Nat} : ∀ {v : Int} {t : Nat}, CR d v t → (∃ w, v = 2 * w + 1) →
    ∃ (s : Int) (t' : Nat), (s = 1 ∨ s = -1) ∧ t' + 1 ≤ t ∧ CR d (v - s) t' := by
  intro v t h
  induction h with
  | zero =>
    intro hodd
    cases hodd with
    | intro w hw => omega
  | @addT v0 t0 e he r ih =>
    intro hodd
    cases e with
    | zero =>
      have hp0 : ipow 0 = 1 := rfl
      refine ⟨1, t0, Or.inl rfl, by omega, ?_⟩
      have hEq : v0 + ipow 0 - 1 = v0 := by omega
      rw [hEq]
      exact r
    | succ e' =>
      have hpe : ipow (e' + 1) = 2 * ipow e' := ipow_succ e'
      have hodd0 : ∃ w, v0 = 2 * w + 1 := by
        cases hodd with
        | intro w hw => exact ⟨w - ipow e', by omega⟩
      have ⟨s, t', hs, hle, hcr⟩ := ih hodd0
      refine ⟨s, t' + 1, hs, by omega, ?_⟩
      have hEq : v0 + ipow (e' + 1) - s = (v0 - s) + ipow (e' + 1) := by omega
      rw [hEq]
      exact CR.addT he hcr
  | @subT v0 t0 e he r ih =>
    intro hodd
    cases e with
    | zero =>
      have hp0 : ipow 0 = 1 := rfl
      refine ⟨-1, t0, Or.inr rfl, by omega, ?_⟩
      have hEq : v0 - ipow 0 - (-1) = v0 := by omega
      rw [hEq]
      exact r
    | succ e' =>
      have hpe : ipow (e' + 1) = 2 * ipow e' := ipow_succ e'
      have hodd0 : ∃ w, v0 = 2 * w + 1 := by
        cases hodd with
        | intro w hw => exact ⟨w + ipow e', by omega⟩
      have ⟨s, t', hs, hle, hcr⟩ := ih hodd0
      refine ⟨s, t' + 1, hs, by omega, ?_⟩
      have hEq : v0 - ipow (e' + 1) - s = (v0 - s) - ipow (e' + 1) := by omega
      rw [hEq]
      exact CR.subT he hcr

/-- 偶数（2 的倍数）的表示可以整体减半（项数不增）。 -/
theorem CR_pair (d : Nat) : ∀ (t : Nat) (w : Int), CR (d + 1) (2 * w) t →
    ∃ t', t' ≤ t ∧ CR d w t' := by
  intro t
  induction t using nat_strong_induction with
  | _ t ih =>
    cases t with
    | zero =>
      intro w h
      have hv : (2:Int) * w = 0 := CR_inv_zero h
      have hw : w = 0 := by omega
      subst hw
      exact ⟨0, Nat.le_refl 0, .zero⟩
    | succ t =>
      intro w h
      have ⟨e, v', he, hcase, hr⟩ := CR_inv_succ h
      cases e with
      | zero =>
        have hp0 : ipow 0 = 1 := rfl
        -- 2w = v' ± 1，v' 为奇数
        have hodd : ∃ w', v' = 2 * w' + 1 := by
          cases hcase with
          | inl hc => exact ⟨w - 1, by omega⟩
          | inr hc => exact ⟨w, by omega⟩
        have ⟨s, t₂, hs, hle, hcr⟩ := CR_odd_ext hr hodd
        -- v' - s 是偶数：= 2 * w''
        have hw'' : ∃ w'', v' - s = 2 * w'' := by
          cases hcase with
          | inl hc =>
              cases hs with
              | inl hs1 => exact ⟨w - 1, by omega⟩
              | inr hs1 => exact ⟨w, by omega⟩
          | inr hc =>
              cases hs with
              | inl hs1 => exact ⟨w, by omega⟩
              | inr hs1 => exact ⟨w + 1, by omega⟩
        cases hw'' with
        | intro w'' hw''e =>
          rw [hw''e] at hcr
          have ⟨t₃, ht₃, hcr₃⟩ := ih t₂ (by omega) w'' hcr
          -- w 与 w'' 的关系：相差 ±1
          have hrel : w = w'' + 1 ∨ w = w'' ∨ w = w'' - 1 := by
            cases hcase with
            | inl hc =>
                cases hs with
                | inl hs1 => exact Or.inl (by omega)
                | inr hs1 => exact Or.inr (Or.inl (by omega))
            | inr hc =>
                cases hs with
                | inl hs1 => exact Or.inr (Or.inl (by omega))
                | inr hs1 => exact Or.inr (Or.inr (by omega))
          cases hrel with
          | inl hw1 =>
            refine ⟨t₃ + 1, by omega, ?_⟩
            rw [hw1]
            exact CR.addT (Nat.zero_le _) hcr₃
          | inr h2 =>
            cases h2 with
            | inl hw1 =>
              rw [hw1]; exact ⟨t₃, by omega, hcr₃⟩
            | inr hw1 =>
              refine ⟨t₃ + 1, by omega, ?_⟩
              rw [hw1]
              exact CR.subT (Nat.zero_le _) hcr₃
      | succ e' =>
        have hpe : ipow (e' + 1) = 2 * ipow e' := ipow_succ e'
        -- 2w = v' ± 2^{e'+1}，v' 仍为偶数 = 2w''
        have hw'' : ∃ w'', v' = 2 * w'' := by
          cases hcase with
          | inl hc => exact ⟨w - ipow e', by omega⟩
          | inr hc => exact ⟨w + ipow e', by omega⟩
        cases hw'' with
        | intro w'' hw''e =>
          rw [hw''e] at hr
          have ⟨t₃, ht₃, hcr₃⟩ := ih t (by omega) w'' hr
          cases hcase with
          | inl hc =>
              refine ⟨t₃ + 1, by omega, ?_⟩
              have hEq : w = w'' + ipow e' := by omega
              rw [hEq]
              exact CR.addT (e := e') (by omega) hcr₃
          | inr hc =>
              refine ⟨t₃ + 1, by omega, ?_⟩
              have hEq : w = w'' - ipow e' := by omega
              rw [hEq]
              exact CR.subT (e := e') (by omega) hcr₃

theorem CR_zero_le {v : Int} {t : Nat} (h : CR 0 v t) : v ≤ t := by
  induction h with
  | zero => omega
  | @addT v t e he r ih =>
    have he0 : e = 0 := by omega
    subst he0
    show v + 1 ≤ t + 1
    omega
  | @subT v t e he r ih =>
    have he0 : e = 0 := by omega
    subst he0
    show v - 1 ≤ t + 1
    omega

/-- **最小性定理**：若 v = q·2^d + r（0 ≤ r < 2^d），则任何 CR d v t 满足 q + nafW r ≤ t。
即 nafW 给出的项数是最少的。 -/
theorem CR_min : ∀ (d : Nat) {v : Int} {t : Nat}, CR d v t → ∀ (q : Int) (r : Nat),
    r < 2 ^ d → v = q * ipow d + r → q + nafW r ≤ t := by
  intro d
  induction d with
  | zero =>
    intro v t h q r hr hv
    have hr0 : r = 0 := by omega
    have hp0 : ipow 0 = 1 := rfl
    rw [hp0] at hv
    have hle := CR_zero_le h
    rw [hr0, nafW_zero]
    omega
  | succ d ih =>
    intro v t h q r hr hv
    rw [ipow_succ, ← Int.mul_assoc, Int.mul_comm q 2, Int.mul_assoc] at hv
    -- hv : v = 2 * (q * ipow d) + r
    have hB : 0 < ipow d := ipow_pos d
    have hpar : r % 2 = 0 ∨ r % 2 = 1 := by omega
    cases hpar with
    | inl heven =>
      have hrm : r = 2 * (r / 2) := by omega
      have hvE : v = 2 * ((q:Int) * ipow d + (r / 2 : Nat)) := by omega
      rw [hvE] at h
      have ⟨t', ht'le, hcr⟩ := CR_pair d t _ h
      have hmin := ih hcr q (r / 2) (by omega) (by omega)
      rw [hrm, nafW_two_mul]
      omega
    | inr hodd =>
      have hrm : r = 2 * (r / 2) + 1 := by omega
      have hvO : ∃ w, v = 2 * w + 1 := ⟨q * ipow d + (r / 2 : Nat), by omega⟩
      have ⟨s, t', hs, htle, hcr⟩ := CR_odd_ext h hvO
      cases hs with
      | inl hs1 =>
        rw [hs1] at hcr
        have hE : v - 1 = 2 * ((q:Int) * ipow d + (r / 2 : Nat)) := by omega
        rw [hE] at hcr
        have ⟨t'', ht''le, hcr''⟩ := CR_pair d t' _ hcr
        have hmin := ih hcr'' q (r / 2) (by omega) (by omega)
        rw [hrm, nafW_two_mul_add_one]
        omega
      | inr hs1 =>
        rw [hs1] at hcr
        have hE : v - (-1) = 2 * ((q:Int) * ipow d + ((r / 2 : Nat) + 1)) := by omega
        rw [hE] at hcr
        have hlt : (r / 2 : Nat) + 1 ≤ 2 ^ d := by omega
        by_cases hEq2 : (r / 2 : Nat) + 1 = 2 ^ d
        · have hB2 : (q + 1) * ipow d = q * ipow d + ipow d := by
            rw [Int.add_mul, Int.one_mul]
          have hE2 : 2 * ((q:Int) * ipow d + ((r / 2 : Nat) + 1)) = 2 * ((q + 1) * ipow d) := by
            have hc : ((2 ^ d : Nat) : Int) = ipow d := rfl
            have hq : ((r / 2 : Nat) : Int) + 1 = ipow d := by omega
            omega
          rw [hE2] at hcr
          have ⟨t'', ht''le, hcr''⟩ := CR_pair d t' _ hcr
          have hmin := ih hcr'' (q + 1) 0 (by omega) (by omega)
          have hnw : nafW r ≤ 2 := by
            have hrec := nafW_two_mul_add_one (r / 2)
            have hp1 := nafW_two_pow d
            rw [← hEq2] at hp1
            rw [hrm, hrec]
            omega
          omega
        · have ⟨t'', ht''le, hcr''⟩ := CR_pair d t' _ hcr
          have hmin := ih hcr'' q ((r / 2 : Nat) + 1) (by omega) (by omega)
          have hrec := nafW_two_mul_add_one (r / 2)
          rw [hrm, hrec]
          omega

/-- 次可加性：nafW (a + b) ≤ nafW a + nafW b。 -/
theorem nafW_subadd (a b : Nat) : nafW (a + b) ≤ nafW a + nafW b := by
  have key : ∀ (x : Nat), x < 2 ^ (x + 1) := by
    intro x
    have h1 := two_pow_ge (x + 1)
    have h2 : 2 ^ (x + 1) ≥ 2 ^ 1 := two_pow_mono (by omega : (1:Nat) ≤ x + 1)
    omega
  have ha : a < 2 ^ ((a + b) + 1) := by
    have h1 : 2 ^ (a + 1) ≤ 2 ^ ((a + b) + 1) := two_pow_mono (by omega)
    have h2 := key a
    omega
  have hb : b < 2 ^ ((a + b) + 1) := by
    have h1 : 2 ^ (b + 1) ≤ 2 ^ ((a + b) + 1) := two_pow_mono (by omega)
    have h2 := key b
    omega
  have hab : a + b < 2 ^ ((a + b) + 1) := key (a + b)
  have hrep1 : CR ((a + b) + 1) a (nafW a) := nafW_rep _ a ha
  have hrep2 : CR ((a + b) + 1) b (nafW b) := nafW_rep _ b hb
  have hj : CR ((a + b) + 1) ((a:Nat) + b) (nafW a + nafW b) := CR_join hrep1 hrep2
  have hmin := CR_min _ hj 0 (a + b) hab (by omega)
  omega

/-! ## 九、路径 ↔ 表示，下界与上界 -/

/-- 路径到表示：a 到 b 的 s 步路径给出某个 d，使 b − a·2^d 有 s − d 项表示。 -/
theorem reach_cr {a b s : Nat} (h : Reach a b s) :
    ∃ d t, d + t = s ∧ CR d ((b : Int) - (a : Int) * ipow d) t := by
  induction h with
  | refl x =>
    refine ⟨0, 0, rfl, ?_⟩
    have hp0 : ipow 0 = 1 := rfl
    have hE : ((x:Int) - (x:Int) * ipow 0) = 0 := by
      have hp0 : ipow 0 = 1 := rfl
      rw [hp0]
      omega
    rw [hE]
    exact .zero
  | @step x y z s hs r ih =>
    have ⟨d, t, hsum, hcr⟩ := ih
    cases hs
    next u =>
      -- y = x + 1（plus：x → x+1）
      refine ⟨d, t + 1, by omega, ?_⟩
      have hexp : (((x + 1 : Nat)) : Int) * ipow d
          = ((x : Nat) : Int) * ipow d + ipow d := by
        have hx1 : (((x + 1 : Nat)) : Int) = ((x : Nat) : Int) + 1 := by omega
        rw [hx1, Int.add_mul, Int.one_mul]
      have hE : ((z:Int) - ((x : Nat) : Int) * ipow d)
          = ((z:Int) - (((x + 1 : Nat)) : Int) * ipow d) + ipow d := by omega
      rw [hE]
      exact CR.addT (Nat.le_refl d) hcr
    next u =>
      -- x = y + 1（minus：y+1 → y）
      refine ⟨d, t + 1, by omega, ?_⟩
      have hexp : (((y + 1 : Nat)) : Int) * ipow d
          = ((y : Nat) : Int) * ipow d + ipow d := by
        have hy1 : (((y + 1 : Nat)) : Int) = ((y : Nat) : Int) + 1 := by omega
        rw [hy1, Int.add_mul, Int.one_mul]
      have hE : ((z:Int) - (((y + 1 : Nat)) : Int) * ipow d)
          = ((z:Int) - ((y : Nat) : Int) * ipow d) - ipow d := by omega
      rw [hE]
      exact CR.subT (Nat.le_refl d) hcr
    next u =>
      -- x = u + 1, y = 2 * (u + 1)
      refine ⟨d + 1, t, by omega, ?_⟩
      have hE : ((z:Int) - ((2 * (u + 1) : Nat) : Int) * ipow d)
          = ((z:Int) - (((u + 1 : Nat)) : Int) * ipow (d + 1)) := by
        have h1 : ipow (d + 1) = 2 * ipow d := ipow_succ d
        have h2 : ((2 * (u + 1) : Nat) : Int) = 2 * ((u:Int) + 1) := by omega
        have h3 : (((u + 1 : Nat)) : Int) = ((u:Int) + 1) := by omega
        rw [h1, h2, h3]
        rw [two_mul_comm_int]
      rw [← hE]
      exact CR_mono (Nat.le_succ d) hcr

/-- **下界**：任何 s 步路径都满足 cost(d) ≤ s（对某个 d），
其中 cost(d) = d + |a·2^d − b| / 2^d + nafW(|a·2^d − b| % 2^d)。 -/
def costOf (a b d : Nat) : Nat :=
  d + absg (a * 2 ^ d) b / 2 ^ d + nafW (absg (a * 2 ^ d) b % 2 ^ d)

theorem reach_ge_cost {a b s : Nat} (h : Reach a b s) :
    ∃ d, costOf a b d ≤ s := by
  have ⟨d, t, hsum, hcr⟩ := reach_cr h
  refine ⟨d, ?_⟩
  have hB : 0 < 2 ^ d := two_pow_pos d
  have hdm : 2 ^ d * (absg (a * 2 ^ d) b / 2 ^ d) + absg (a * 2 ^ d) b % 2 ^ d
      = absg (a * 2 ^ d) b := Nat.div_add_mod _ _
  have hlt : absg (a * 2 ^ d) b % 2 ^ d < 2 ^ d := Nat.mod_lt _ hB
  have hci : ((2 ^ d : Nat) : Int) = ipow d := rfl
  have hc2 : ((a * 2 ^ d : Nat) : Int) = ((a:Int) * ipow d) := cast_mul_pow a d
  -- 乘积桥接：q·ipow d 与 (2^d)·q 是同一个原子
  have hprod : (((absg (a * 2 ^ d) b / 2 ^ d : Nat) : Int)) * ipow d
      = ((2 ^ d : Nat) : Int) * ((absg (a * 2 ^ d) b / 2 ^ d : Nat) : Int) := by
    rw [← hci, Int.mul_comm]
  by_cases hcase : a * 2 ^ d ≤ b
  · have hab : absg (a * 2 ^ d) b = b - a * 2 ^ d := by
      unfold absg; rw [ite_eq_left hcase]
    have hv : ((b:Int) - (a:Int) * ipow d)
        = ((absg (a * 2 ^ d) b / 2 ^ d : Nat) : Int) * ipow d
          + ((absg (a * 2 ^ d) b % 2 ^ d : Nat) : Int) := by omega
    have hmin := CR_min d hcr ((absg (a * 2 ^ d) b / 2 ^ d : Nat) : Int)
      (absg (a * 2 ^ d) b % 2 ^ d) hlt hv
    unfold costOf
    omega
  · have hab : absg (a * 2 ^ d) b = a * 2 ^ d - b := by
      unfold absg; rw [ite_eq_right hcase]
    have hcr2 := CR_neg hcr
    have hv : -(((b:Int) - (a:Int) * ipow d))
        = ((absg (a * 2 ^ d) b / 2 ^ d : Nat) : Int) * ipow d
          + ((absg (a * 2 ^ d) b % 2 ^ d : Nat) : Int) := by omega
    have hmin := CR_min d hcr2 ((absg (a * 2 ^ d) b / 2 ^ d : Nat) : Int)
      (absg (a * 2 ^ d) b % 2 ^ d) hlt hv
    unfold costOf
    omega

/-- 追加操作。 -/
theorem reach_dbl {x s : Nat} {c : Nat} (h : Reach c x s) (hx : 0 < x) : Reach c (2 * x) (s + 1) := by
  cases x with
  | zero => omega
  | succ w => exact reach_snoc h (Step.dbl w)

theorem reach_plus1 {x s : Nat} {c : Nat} (h : Reach c x s) : Reach c (x + 1) (s + 1) :=
  reach_snoc h (Step.plus x)

theorem reach_minus1 {x s : Nat} {c : Nat} (h : Reach c x s) (hx : 0 < x) : Reach c (x - 1) (s + 1) := by
  cases x with
  | zero => omega
  | succ w => exact reach_snoc h (Step.minus w)

/-! ## 十、辅助分解引理 -/

theorem mul_two_pow (k2 d : Nat) : k2 * 2 ^ (d + 1) = 2 * (k2 * 2 ^ d) := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (k2 * 2 ^ d) 2]

theorem two_pow_succ_mul (d q : Nat) : 2 ^ (d + 1) * q = 2 * (2 ^ d * q) := by
  rw [Nat.mul_comm, mul_two_pow, Nat.mul_comm q (2 ^ d)]

theorem pow_mul_add (d q : Nat) : 2 ^ d * (q + 1) = 2 ^ d * q + 2 ^ d := by
  rw [Nat.mul_add, Nat.mul_one]

theorem div_mod_split {B q r : Nat} (hB : 0 < B) (hr : r < B) :
    (B * q + r) / B = q ∧ (B * q + r) % B = r := by
  constructor
  · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hr,
      Nat.zero_add]
  · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem absg_split_under {k2 d X q r' : Nat} (hr' : r' < 2 ^ d)
    (hX : X = k2 * 2 ^ d + (2 ^ d * q + r')) :
    absg (k2 * 2 ^ d) X = 2 ^ d * q + r' ∧
    absg (k2 * 2 ^ d) X / 2 ^ d = q ∧ absg (k2 * 2 ^ d) X % 2 ^ d = r' := by
  have h1 : k2 * 2 ^ d ≤ X := by omega
  have ⟨hdiv, hmod⟩ := div_mod_split (q := q) (two_pow_pos d) hr'
  have hEq : absg (k2 * 2 ^ d) X = 2 ^ d * q + r' := by
    unfold absg
    rw [ite_eq_left h1]
    omega
  rw [hEq]
  exact ⟨rfl, hdiv, hmod⟩

theorem absg_split_over {k2 d X q r' : Nat} (hr' : r' < 2 ^ d)
    (hX : X + (2 ^ d * q + r') = k2 * 2 ^ d) :
    absg (k2 * 2 ^ d) X = 2 ^ d * q + r' ∧
    absg (k2 * 2 ^ d) X / 2 ^ d = q ∧ absg (k2 * 2 ^ d) X % 2 ^ d = r' := by
  have h1 : X ≤ k2 * 2 ^ d := by omega
  have ⟨hdiv, hmod⟩ := div_mod_split (q := q) (two_pow_pos d) hr'
  have hEq : absg (k2 * 2 ^ d) X = 2 ^ d * q + r' := by
    unfold absg
    by_cases h : k2 * 2 ^ d ≤ X
    · rw [ite_eq_left h]; omega
    · rw [ite_eq_right h]; omega
  rw [hEq]
  exact ⟨rfl, hdiv, hmod⟩

/-! ## 十一、上界（构造性）：cost(d) 步内可达 -/

theorem cost_reach : ∀ (d k2 n : Nat), 0 < k2 → 0 < n →
    ∃ s, s ≤ costOf k2 n d ∧ Reach k2 n s := by
  intro d
  induction d with
  | zero =>
    intro k2 n hk2 hn
    by_cases hcase : k2 ≤ n
    · refine ⟨n - k2, ?_, reach_up n k2 hcase⟩
      unfold costOf absg
      rw [Nat.pow_zero, Nat.mul_one, ite_eq_left hcase, Nat.div_one, Nat.mod_one, nafW_zero]
      omega
    · refine ⟨k2 - n, ?_, reach_down k2 n (by omega)⟩
      unfold costOf absg
      rw [Nat.pow_zero, Nat.mul_one, ite_eq_right hcase, Nat.div_one, Nat.mod_one, nafW_zero]
      omega
  | succ d ih =>
    intro k2 n hk2 hn
    have hB2 : (2:Nat) ≤ 2 ^ (d + 1) := by
      have := two_pow_mono (show (1:Nat) ≤ d + 1 by omega)
      omega
    by_cases hn1 : n = 1
    · -- n = 1 特例：直接下行 k2 − 1 步
      subst hn1
      refine ⟨k2 - 1, ?_, reach_down k2 1 (by omega)⟩
      have hB : 0 < 2 ^ (d + 1) := two_pow_pos _
      have hdm : 2 ^ (d + 1) * ((k2 * 2 ^ (d + 1) - 1) / 2 ^ (d + 1))
          + (k2 * 2 ^ (d + 1) - 1) % 2 ^ (d + 1) = k2 * 2 ^ (d + 1) - 1 :=
        Nat.div_add_mod _ _
      have hge : (2:Nat) ≤ k2 * 2 ^ (d + 1) :=
        Nat.mul_le_mul hk2 hB2
      have hq : k2 - 1 ≤ (k2 * 2 ^ (d + 1) - 1) / 2 ^ (d + 1) := by
        apply (Nat.le_div_iff_mul_le hB).mpr
        have e1 : (k2 - 1) * 2 ^ (d + 1) = k2 * 2 ^ (d + 1) - 2 ^ (d + 1) := by
          rw [Nat.sub_mul, Nat.one_mul]
        omega
      unfold costOf absg
      rw [ite_eq_right (by omega)]
      omega
    · -- n ≥ 2
      have hn2 : 2 ≤ n := by omega
      have hnpos : 0 < n / 2 := by omega
      have hku : k2 * 2 ^ (d + 1) = 2 * (k2 * 2 ^ d) := mul_two_pow k2 d
      by_cases hcase : k2 * 2 ^ (d + 1) ≤ n
      · -- 欠冲：absg = n − k2·2^(d+1)
        have habs1 : absg (k2 * 2 ^ (d + 1)) n = n - k2 * 2 ^ (d + 1) := by
          unfold absg; rw [ite_eq_left hcase]
        have hdm1 : 2 ^ (d + 1) * ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1))
            + (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) = n - k2 * 2 ^ (d + 1) :=
          Nat.div_add_mod _ _
        have hlt1 : (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) < 2 ^ (d + 1) :=
          Nat.mod_lt _ (two_pow_pos _)
        have hD : n - k2 * 2 ^ (d + 1)
            = 2 ^ (d + 1) * ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1))
              + (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) := by omega
        have ⟨hdD, hmD⟩ := div_mod_split
          (q := (n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1)) (two_pow_pos _) hlt1
        have hnD : n = k2 * 2 ^ (d + 1)
            + 2 ^ (d + 1) * ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1))
            + (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) := by omega
        by_cases hpar : (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) % 2 = 0
        · -- 余数偶：n 偶，经 n/2 翻倍一步
          have e2 := two_pow_succ_mul d ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1))
          have hnE : n = 2 * (n / 2) := by omega
          have hrE : (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1)
              = 2 * ((n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) / 2) := by omega
          have hn2d : n / 2 = k2 * 2 ^ d
              + (2 ^ d * ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1))
                + (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) / 2) := by omega
          have hr1lt : (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) / 2 < 2 ^ d := by omega
          have ⟨hEq, hdiv, hmod⟩ :=
            absg_split_under hr1lt hn2d
          have ⟨s, hsle, hreach⟩ := ih k2 (n / 2) hk2 hnpos
          refine ⟨s + 1, ?_, ?_⟩
          · unfold costOf at hsle ⊢
            rw [hdiv, hmod] at hsle
            rw [habs1, hD, hdD, hmD, hrE, nafW_two_mul]
            omega
          · rw [show n = 2 * (n / 2) from by omega]
            exact reach_dbl hreach hnpos
        · -- 余数奇：n 奇
          have e2 := two_pow_succ_mul d ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1))
          have hnE : n = 2 * (n / 2) + 1 := by omega
          have hrE : (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1)
              = 2 * ((n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) / 2) + 1 := by omega
          have hn2d : n / 2 = k2 * 2 ^ d
              + (2 ^ d * ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1))
                + (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) / 2) := by omega
          have hr1lt : (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) / 2 < 2 ^ d := by omega
          by_cases hmin : nafW ((n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) / 2)
              ≤ nafW ((n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) / 2 + 1)
          · -- 下行分支：经 n/2，翻倍，+1
            have ⟨hEq, hdiv, hmod⟩ := absg_split_under hr1lt hn2d
            have ⟨s, hsle, hreach⟩ := ih k2 (n / 2) hk2 hnpos
            refine ⟨s + 2, ?_, ?_⟩
            · unfold costOf at hsle ⊢
              rw [hdiv, hmod] at hsle
              rw [habs1, hD, hdD, hmD, hrE, nafW_two_mul_add_one]
              omega
            · rw [show n = 2 * (n / 2) + 1 from by omega]
              exact reach_plus1 (reach_dbl hreach hnpos)
          · -- 上行分支（nafW (r1+1) 更小）：经 n/2 + 1，翻倍，−1
            by_cases hreq : (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) / 2 + 1 = 2 ^ d
            · -- 角落：r = 2^{d+1} − 1，用 (Q+1, 0) 分解
              have e3 := pow_mul_add d ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1))
              have hn2dc : n / 2 + 1 = k2 * 2 ^ d
                  + (2 ^ d * ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1) + 1) + 0) := by omega
              have ⟨hEq, hdiv, hmod⟩ := absg_split_under (by omega) hn2dc
              have ⟨s, hsle, hreach⟩ := ih k2 (n / 2 + 1) hk2 (by omega)
              have hne : nafW ((n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) / 2 + 1) = 1 := by
                rw [hreq]; exact nafW_two_pow d
              refine ⟨s + 2, ?_, ?_⟩
              · unfold costOf at hsle ⊢
                rw [hdiv, hmod] at hsle
                rw [habs1, hD, hdD, hmD, hrE, nafW_two_mul_add_one]
                have hnz := nafW_zero
                omega
              · rw [show n = 2 * (n / 2 + 1) - 1 from by omega]
                exact reach_minus1 (reach_dbl hreach (by omega)) (by omega)
            · -- 一般：分解 (Q, r1+1)
              have hn2d' : n / 2 + 1 = k2 * 2 ^ d
                  + (2 ^ d * ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1))
                    + ((n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) / 2 + 1)) := by omega
              have ⟨hEq, hdiv, hmod⟩ := absg_split_under (by omega) hn2d'
              have ⟨s, hsle, hreach⟩ := ih k2 (n / 2 + 1) hk2 (by omega)
              refine ⟨s + 2, ?_, ?_⟩
              · unfold costOf at hsle ⊢
                rw [hdiv, hmod] at hsle
                rw [habs1, hD, hdD, hmD, hrE, nafW_two_mul_add_one]
                omega
              · rw [show n = 2 * (n / 2 + 1) - 1 from by omega]
                exact reach_minus1 (reach_dbl hreach (by omega)) (by omega)
      · -- 过冲：absg = k2·2^(d+1) − n
        have habs1 : absg (k2 * 2 ^ (d + 1)) n = k2 * 2 ^ (d + 1) - n := by
          unfold absg; rw [ite_eq_right (by omega)]
        have hdm1 : 2 ^ (d + 1) * ((k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1))
            + (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) = k2 * 2 ^ (d + 1) - n :=
          Nat.div_add_mod _ _
        have hlt1 : (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) < 2 ^ (d + 1) :=
          Nat.mod_lt _ (two_pow_pos _)
        have hD : k2 * 2 ^ (d + 1) - n
            = 2 ^ (d + 1) * ((k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1))
              + (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) := by omega
        have ⟨hdD, hmD⟩ := div_mod_split
          (q := (k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1)) (two_pow_pos _) hlt1
        have hnD : k2 * 2 ^ (d + 1) = n
            + 2 ^ (d + 1) * ((k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1))
            + (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) := by omega
        by_cases hpar : (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) % 2 = 0
        · -- 余数偶：n 偶，经 n/2 翻倍
          have e2 := two_pow_succ_mul d ((k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1))
          have hnE : n = 2 * (n / 2) := by omega
          have hrE : (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1)
              = 2 * ((k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2) := by omega
          have hn2d : n / 2 + (2 ^ d * ((k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1))
                + (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2) = k2 * 2 ^ d := by omega
          have hr1lt : (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2 < 2 ^ d := by omega
          have ⟨hEq, hdiv, hmod⟩ := absg_split_over hr1lt hn2d
          have ⟨s, hsle, hreach⟩ := ih k2 (n / 2) hk2 hnpos
          refine ⟨s + 1, ?_, ?_⟩
          · unfold costOf at hsle ⊢
            rw [hdiv, hmod] at hsle
            rw [habs1, hD, hdD, hmD, hrE, nafW_two_mul]
            omega
          · rw [show n = 2 * (n / 2) from by omega]
            exact reach_dbl hreach hnpos
        · -- 余数奇：n 奇
          have e2 := two_pow_succ_mul d ((k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1))
          have e3 := pow_mul_add d ((k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1))
          have hnE : n = 2 * (n / 2) + 1 := by omega
          have hrE : (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1)
              = 2 * ((k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2) + 1 := by omega
          have hr1lt : (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2 < 2 ^ d := by omega
          by_cases hmin : nafW ((k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2 + 1)
              ≤ nafW ((k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2)
          · -- 上行分支（nafW (r1+1) 更小或并列）
            by_cases hreq : (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2 + 1 = 2 ^ d
            · -- 角落：r = 2^{d+1} − 1
              have hd0 : d ≠ 0 := by
                intro h; subst h
                have hA : nafW ((k2 * 2 ^ (0 + 1) - n) % 2 ^ (0 + 1) / 2) = 0 := by
                  have hz : (k2 * 2 ^ (0 + 1) - n) % 2 ^ (0 + 1) / 2 = 0 := by omega
                  rw [hz]; exact nafW_zero
                have hB : nafW ((k2 * 2 ^ (0 + 1) - n) % 2 ^ (0 + 1) / 2 + 1) = 1 := by
                  have hz : (k2 * 2 ^ (0 + 1) - n) % 2 ^ (0 + 1) / 2 + 1 = 1 := by omega
                  rw [hz]; exact nafW_one
                omega
              -- d ≥ 1：经 n/2 翻倍再 +1（用 (q+1, 0) 分解）
              have hn2d : n / 2 + (2 ^ d * ((k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1) + 1) + 0)
                  = k2 * 2 ^ d := by omega
              have ⟨hEq, hdiv, hmod⟩ := absg_split_over (by omega) hn2d
              have ⟨s, hsle, hreach⟩ := ih k2 (n / 2) hk2 hnpos
              have hne : nafW ((k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2 + 1) = 1 := by
                rw [hreq]; exact nafW_two_pow d
              have hminGe : (1:Nat)
                  ≤ min (nafW ((k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2))
                      (nafW ((k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2 + 1)) := by
                have hz : (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2 = 2 ^ d - 1 := by omega
                have h1 : (1:Nat) ≤ 2 ^ d - 1 := by
                  have := two_pow_mono (show (1:Nat) ≤ d by omega)
                  omega
                have h2 := nafW_pos (2 ^ d - 1) h1
                omega
              refine ⟨s + 2, ?_, ?_⟩
              · unfold costOf at hsle ⊢
                rw [hdiv, hmod] at hsle
                rw [habs1, hD, hdD, hmD, hrE, nafW_two_mul_add_one]
                have hnz := nafW_zero
                omega
              · rw [show n = 2 * (n / 2) + 1 from by omega]
                exact reach_plus1 (reach_dbl hreach hnpos)
            · -- 一般上行：经 n/2 翻倍再 +1（分解 (q, r1+1)）
              have hn2d : n / 2 + (2 ^ d * ((k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1))
                  + ((k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2 + 1)) = k2 * 2 ^ d := by omega
              have ⟨hEq, hdiv, hmod⟩ := absg_split_over (by omega) hn2d
              have ⟨s, hsle, hreach⟩ := ih k2 (n / 2) hk2 hnpos
              refine ⟨s + 2, ?_, ?_⟩
              · unfold costOf at hsle ⊢
                rw [hdiv, hmod] at hsle
                rw [habs1, hD, hdD, hmD, hrE, nafW_two_mul_add_one]
                omega
              · rw [show n = 2 * (n / 2) + 1 from by omega]
                exact reach_plus1 (reach_dbl hreach hnpos)
          · -- 下行分支（nafW r1 更小）：经 n/2 + 1 翻倍再 −1（分解 (q, r1)）
            have hn2d' : n / 2 + 1 + (2 ^ d * ((k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1))
                + (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) / 2) = k2 * 2 ^ d := by omega
            have ⟨hEq, hdiv, hmod⟩ := absg_split_over (by omega) hn2d'
            have ⟨s, hsle, hreach⟩ := ih k2 (n / 2 + 1) hk2 (by omega)
            refine ⟨s + 2, ?_, ?_⟩
            · unfold costOf at hsle ⊢
              rw [hdiv, hmod] at hsle
              rw [habs1, hD, hdD, hmD, hrE, nafW_two_mul_add_one]
              omega
            · rw [show n = 2 * (n / 2 + 1) - 1 from by omega]
              exact reach_minus1 (reach_dbl hreach (by omega)) (by omega)

/-- **上界**：dist k2 n ≤ costOf k2 n d。 -/
theorem dist_le_cost {k2 n d : Nat} (hk2 : 0 < k2) (hn : 0 < n) :
    dist k2 n ≤ costOf k2 n d := by
  have ⟨s, hsle, hreach⟩ := cost_reach d k2 n hk2 hn
  exact Nat.le_trans (dist_le_of_reach hreach) hsle
/-! ## 十二、nafW 的关键单调性与商余唯一性 -/

/-- 乘积的规范形式：2^{d+1}·q = 2·(2^d·q)（供各引理统一原子）。 -/
theorem pow_succ_mul_two (d q : Nat) : 2 ^ (d + 1) * q = 2 * (2 ^ d * q) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]

theorem mul_two_swap (d q : Nat) : 2 ^ d * (2 * q) = 2 * (2 ^ d * q) := by
  rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]

/-- 商余分解的唯一性（辅助）。 -/
theorem divmod_unique_aux {B a ra b rb : Nat} (_hB : 0 < B) (hra : ra < B) (_hrb : rb < B)
    (hab : a ≤ b) (h : B * a + ra = B * b + rb) : a = b ∧ ra = rb := by
  by_cases hb0 : b - a = 0
  · have habE : a = b := by omega
    subst habE
    exact ⟨rfl, by omega⟩
  · exfalso
    have hc : b = a + (b - a) := by omega
    rw [hc, Nat.mul_add] at h
    have hb0' : 1 ≤ b - a := by omega
    have hBle : B * 1 ≤ B * (b - a) := Nat.mul_le_mul_left _ hb0'
    omega

/-- 商余分解的唯一性。 -/
theorem divmod_unique {B a ra b rb : Nat} (hB : 0 < B) (hra : ra < B) (hrb : rb < B)
    (h : B * a + ra = B * b + rb) : a = b ∧ ra = rb := by
  by_cases hab : a ≤ b
  · exact divmod_unique_aux hB hra hrb hab h
  · have ⟨h1, h2⟩ := divmod_unique_aux hB hrb hra (by omega) h.symm
    exact ⟨h1.symm, h2.symm⟩

/-- **nafW 关键单调性**：x < 2^d 时 nafW x ≤ nafW (x + 2^d)。
这是「过冲侧 cost 随 d 单调不减」的核心。 -/
theorem nafW_add_pow : ∀ (d x : Nat), x < 2 ^ d → nafW x ≤ nafW (x + 2 ^ d) := by
  intro d
  induction d with
  | zero =>
    intro x hx
    rw [Nat.pow_zero] at hx
    have hx0 : x = 0 := by omega
    subst hx0
    rw [Nat.zero_add, Nat.pow_zero, nafW_zero, nafW_one]
    omega
  | succ d ih =>
    intro x hx
    have h2p : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2p] at hx ⊢
    by_cases hpar : x % 2 = 0
    · have hE1 : nafW x = nafW (x / 2) := by
        have hxm : x = 2 * (x / 2) := by omega
        rw [hxm, nafW_two_mul, show 2 * (x / 2) / 2 = x / 2 from by omega]
      have hE2 : nafW (x + 2 * 2 ^ d) = nafW (x / 2 + 2 ^ d) := by
        have hsplit : x + 2 * 2 ^ d = 2 * (x / 2 + 2 ^ d) := by omega
        rw [hsplit, nafW_two_mul]
      have hih := ih (x / 2) (by omega)
      omega
    · have hxm : x = 2 * (x / 2) + 1 := by omega
      rw [hxm, nafW_two_mul_add_one]
      have hsplit : 2 * (x / 2) + 1 + 2 * 2 ^ d = 2 * (x / 2 + 2 ^ d) + 1 := by omega
      rw [hsplit, nafW_two_mul_add_one]
      rw [show x / 2 + 2 ^ d + 1 = x / 2 + 1 + 2 ^ d from by omega]
      by_cases hcorner : x / 2 + 1 = 2 ^ d
      · have hE2 : x / 2 + 1 + 2 ^ d = 2 ^ (d + 1) := by omega
        rw [hE2]
        have hEq : x / 2 + 2 ^ d = 2 ^ (d + 1) - 1 := by omega
        rw [hEq, hcorner]
        have t1 : nafW (2 ^ d) = 1 := nafW_two_pow d
        have t2 : nafW (2 ^ (d + 1)) = 1 := nafW_two_pow _
        have t3 : 0 < nafW (2 ^ (d + 1) - 1) := by
          have h0 := nafW_pos (2 ^ (d + 1) - 1) (by rw [h2p]; omega)
          exact h0
        omega
      · have hih1 := ih (x / 2) (by omega)
        have hih2 := ih (x / 2 + 1) (by omega)
        omega

/-! ## 十三、cost 关于 d 的单调性 -/

/-- 欠冲核（纯算术）：m₁ = 2·(2^d·q₁) + r₁，m₀ = m₁ + k₂·2^d 时
    d+1+q₁+nafW r₁ ≤ d+q₀+nafW r₀，其中 (q₀, r₀) 是 m₀ 在 2^d 下的商余。 -/
theorem under_kernel (d k2 q1 r1 q0 r0 : Nat) (hk2 : 0 < k2)
    (hr1 : r1 < 2 * 2 ^ d) (hr0 : r0 < 2 ^ d)
    (hrel : 2 * (2 ^ d * q1) + r1 + k2 * 2 ^ d = 2 ^ d * q0 + r0) :
    d + 1 + q1 + nafW r1 ≤ d + q0 + nafW r0 := by
  by_cases hcmp : r1 < 2 ^ d
  · have hsec : 2 ^ d * (2 * q1 + k2) + r1 = 2 ^ d * q0 + r0 := by
      have hexp : 2 ^ d * (2 * q1 + k2) = 2 * (2 ^ d * q1) + k2 * 2 ^ d := by
        rw [Nat.mul_add, mul_two_swap, Nat.mul_comm (2 ^ d) k2]
      omega
    have ⟨hu1, hu2⟩ := divmod_unique (two_pow_pos d) hcmp hr0 hsec
    rw [hu2]
    omega
  · have hsec : 2 ^ d * (2 * q1 + k2 + 1) + (r1 - 2 ^ d) = 2 ^ d * q0 + r0 := by
      have hexp : 2 ^ d * (2 * q1 + k2 + 1)
          = 2 * (2 ^ d * q1) + k2 * 2 ^ d + 2 ^ d := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, mul_two_swap, Nat.mul_comm (2 ^ d) k2]
      omega
    have ⟨hu1, hu2⟩ := divmod_unique (two_pow_pos d) (by omega) hr0 hsec
    have hsub : nafW r1 ≤ nafW (r1 - 2 ^ d) + 1 := by
      have h1 := nafW_subadd (r1 - 2 ^ d) (2 ^ d)
      have h2 : nafW (2 ^ d) = 1 := nafW_two_pow d
      have hL : (r1 - 2 ^ d) + 2 ^ d = r1 := by omega
      rw [hL] at h1
      omega
    rw [← hu2]
    omega

/-- **欠冲侧单调性**：k₂·2^{d+1} < n 时 cost(d+1) ≤ cost(d)。 -/
theorem costOf_mono_under (k2 n d : Nat) (hk2 : 0 < k2) (hU : k2 * 2 ^ (d + 1) < n) :
    costOf k2 n (d + 1) ≤ costOf k2 n d := by
  have hB : 0 < 2 ^ d := two_pow_pos d
  have hmul : k2 * 2 ^ (d + 1) = 2 * (k2 * 2 ^ d) := mul_two_pow k2 d
  have hm1 : absg (k2 * 2 ^ (d + 1)) n = n - k2 * 2 ^ (d + 1) := by
    unfold absg; rw [ite_eq_left (by omega)]
  have hm0 : absg (k2 * 2 ^ d) n = n - k2 * 2 ^ d := by
    unfold absg; rw [ite_eq_left (by omega)]
  have hdm1raw := Nat.div_add_mod (n - k2 * 2 ^ (d + 1)) (2 ^ (d + 1))
  rw [pow_succ_mul_two] at hdm1raw
  have hdm0 := Nat.div_add_mod (n - k2 * 2 ^ d) (2 ^ d)
  have hlt1 : (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) < 2 * 2 ^ d := by
    have h := Nat.mod_lt (n - k2 * 2 ^ (d + 1)) (two_pow_pos (d + 1))
    have h2p : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have hlt0 : (n - k2 * 2 ^ d) % 2 ^ d < 2 ^ d := Nat.mod_lt _ hB
  have hrel : 2 * (2 ^ d * ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1)))
      + (n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1) + k2 * 2 ^ d
      = 2 ^ d * ((n - k2 * 2 ^ d) / 2 ^ d) + (n - k2 * 2 ^ d) % 2 ^ d := by omega
  have hker := under_kernel d k2 ((n - k2 * 2 ^ (d + 1)) / 2 ^ (d + 1))
      ((n - k2 * 2 ^ (d + 1)) % 2 ^ (d + 1)) ((n - k2 * 2 ^ d) / 2 ^ d)
      ((n - k2 * 2 ^ d) % 2 ^ d) hk2 hlt1 hlt0 hrel
  unfold costOf
  rw [hm1, hm0]
  exact hker

/-- 过冲核（纯算术）。 -/
theorem over_kernel (d n k2 q0 r0 q1 r1 e : Nat) (hnle : n ≤ k2 * 2 ^ d) (hB : 0 < 2 ^ d)
    (hr0 : r0 < 2 ^ d) (hr1 : r1 < 2 * 2 ^ d)
    (hd0 : 2 ^ d * q0 + r0 = k2 * 2 ^ d - n)
    (hd1 : 2 * (2 ^ d * q1) + r1 = k2 * 2 ^ (d + 1) - n)
    (he1 : n + r0 = 2 ^ d * e) (he2 : e + q0 = k2) :
    d + q0 + nafW r0 ≤ d + 1 + q1 + nafW r1 := by
  have hexp : 2 ^ d * (2 * q0 + e) = 2 * (2 ^ d * q0) + 2 ^ d * e := by
    rw [Nat.mul_add, mul_two_swap]
  have hrelm : 2 * (2 ^ d * q1) + r1 = 2 * (2 ^ d * q0) + 2 * r0 + n := by
    have hkm : k2 * 2 ^ (d + 1) = 2 * (k2 * 2 ^ d) := mul_two_pow k2 d
    omega
  by_cases hcmp : r1 < 2 ^ d
  · have hsec1 : 2 ^ d * (2 * q1) + r1 = 2 ^ d * (2 * q0 + e) + r0 := by
      rw [mul_two_swap]
      omega
    have ⟨hu1, hu2⟩ := divmod_unique hB hcmp hr0 hsec1
    rw [hu2]
    omega
  · have hexp2 : 2 ^ d * (2 * q1 + 1) = 2 * (2 ^ d * q1) + 2 ^ d := by
      rw [Nat.mul_add, Nat.mul_one, mul_two_swap]
    have hsec1' : 2 ^ d * (2 * q1 + 1) + (r1 - 2 ^ d) = 2 ^ d * (2 * q0 + e) + r0 := by
      rw [hexp2]
      omega
    have ⟨hu1, hu2⟩ := divmod_unique hB (by omega) hr0 hsec1'
    have hnap : nafW r0 ≤ nafW (r0 + 2 ^ d) := nafW_add_pow d r0 hr0
    have hEq : r0 + 2 ^ d = r1 := by omega
    rw [hEq] at hnap
    omega

/-- **过冲侧单调性**：n ≤ k₂·2^d 时 cost(d) ≤ cost(d+1)。 -/
theorem costOf_mono_over (k2 n d : Nat) (hO : n ≤ k2 * 2 ^ d) :
    costOf k2 n d ≤ costOf k2 n (d + 1) := by
  have hB : 0 < 2 ^ d := two_pow_pos d
  have hO1 : n ≤ k2 * 2 ^ (d + 1) := by
    rw [mul_two_pow]
    have := Nat.mul_le_mul_right (2 ^ d) hO
    omega
  have hm0 : absg (k2 * 2 ^ d) n = k2 * 2 ^ d - n := by
    unfold absg
    by_cases h : k2 * 2 ^ d ≤ n
    · rw [ite_eq_left h]; omega
    · rw [ite_eq_right h]
  have hm1 : absg (k2 * 2 ^ (d + 1)) n = k2 * 2 ^ (d + 1) - n := by
    unfold absg
    by_cases h : k2 * 2 ^ (d + 1) ≤ n
    · rw [ite_eq_left h]; omega
    · rw [ite_eq_right h]
  have hdm0 := Nat.div_add_mod (k2 * 2 ^ d - n) (2 ^ d)
  have hdm1raw := Nat.div_add_mod (k2 * 2 ^ (d + 1) - n) (2 ^ (d + 1))
  rw [pow_succ_mul_two] at hdm1raw
  have hlt0 : (k2 * 2 ^ d - n) % 2 ^ d < 2 ^ d := Nat.mod_lt _ hB
  have hlt1 : (k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1) < 2 * 2 ^ d := by
    have h := Nat.mod_lt (k2 * 2 ^ (d + 1) - n) (two_pow_pos (d + 1))
    have h2p : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have hq0le : (k2 * 2 ^ d - n) / 2 ^ d ≤ k2 := by
    have hX : 2 ^ d * ((k2 * 2 ^ d - n) / 2 ^ d) ≤ 2 ^ d * k2 := by
      have hcm : 2 ^ d * k2 = k2 * 2 ^ d := Nat.mul_comm _ _
      omega
    exact Nat.le_of_mul_le_mul_left hX hB
  have hE1 : n + (k2 * 2 ^ d - n) % 2 ^ d
      = 2 ^ d * (k2 - (k2 * 2 ^ d - n) / 2 ^ d) := by
    have hk2e : (k2 * 2 ^ d - n) / 2 ^ d + (k2 - (k2 * 2 ^ d - n) / 2 ^ d) = k2 := by omega
    have hsplit := Nat.mul_add (2 ^ d) ((k2 * 2 ^ d - n) / 2 ^ d)
      (k2 - (k2 * 2 ^ d - n) / 2 ^ d)
    have hL : 2 ^ d * ((k2 * 2 ^ d - n) / 2 ^ d + (k2 - (k2 * 2 ^ d - n) / 2 ^ d))
        = 2 ^ d * k2 := by rw [hk2e]
    have hcm : 2 ^ d * k2 = k2 * 2 ^ d := Nat.mul_comm _ _
    omega
  unfold costOf
  rw [hm0, hm1]
  exact over_kernel d n k2 ((k2 * 2 ^ d - n) / 2 ^ d) ((k2 * 2 ^ d - n) % 2 ^ d)
    ((k2 * 2 ^ (d + 1) - n) / 2 ^ (d + 1)) ((k2 * 2 ^ (d + 1) - n) % 2 ^ (d + 1))
    (k2 - (k2 * 2 ^ d - n) / 2 ^ d) hO hB hlt0 hlt1 hdm0 hdm1raw hE1 (by omega)

/-- 欠冲链：k₂·2^{d+m} < n 时 cost(d+m) ≤ cost(d)。 -/
theorem costOf_under_min (k2 n : Nat) (hk2 : 0 < k2) : ∀ (m d : Nat), k2 * 2 ^ (d + m) < n →
    costOf k2 n (d + m) ≤ costOf k2 n d := by
  intro m
  induction m with
  | zero => intro d _; rw [Nat.add_zero]; exact Nat.le_refl _
  | succ m ih =>
    intro d h
    have hp : 2 ^ (d + m) ≤ 2 ^ (d + (m + 1)) := two_pow_mono (by omega)
    have hprev : k2 * 2 ^ (d + m) < n := by
      have hle := Nat.mul_le_mul_left k2 hp
      omega
    have h1 := costOf_mono_under k2 n (d + m) hk2 h
    have h2 := ih d hprev
    show costOf k2 n (d + m + 1) ≤ costOf k2 n d
    omega

/-- 过冲链：n ≤ k₂·2^c 时 cost(c) ≤ cost(c+m)。 -/
theorem costOf_over_min (k2 n : Nat) : ∀ (m c : Nat), n ≤ k2 * 2 ^ c →
    costOf k2 n c ≤ costOf k2 n (c + m) := by
  intro m
  induction m with
  | zero => intro c _; rw [Nat.add_zero]; exact Nat.le_refl _
  | succ m ih =>
    intro c h
    have hm : n ≤ k2 * 2 ^ (c + m) := by
      have hp : 2 ^ c ≤ 2 ^ (c + m) := two_pow_mono (by omega)
      have hle := Nat.mul_le_mul_left k2 hp
      omega
    have h1 := costOf_mono_over k2 n (c + m) hm
    have h2 := ih c h
    show costOf k2 n c ≤ costOf k2 n (c + m + 1)
    omega

/-! ## 十四、倍增次数 c 与闭式解 -/

theorem cdbl_ex (target k2 : Nat) : ∃ c, max k2 1 * 2 ^ c ≥ target := by
  refine ⟨target, ?_⟩
  have h1 : 1 * 2 ^ target ≤ max k2 1 * 2 ^ target :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : target ≤ 2 ^ target := two_pow_ge target
  omega

theorem cdbl_min_witness (target k2 : Nat) :
    ∃ c, max k2 1 * 2 ^ c ≥ target ∧ ∀ d, max k2 1 * 2 ^ d ≥ target → c ≤ d := by
  have ⟨s0, hs0⟩ := cdbl_ex target k2
  have ⟨c, hc, hmin⟩ := exists_min (P := fun c => max k2 1 * 2 ^ c ≥ target) s0 hs0
  exact ⟨c, hc, fun d hd => hmin d hd⟩

/-- C++ 中 countDoublesToReach(k2, target)：最小的 c 使 k₂·2^c ≥ target。 -/
noncomputable def cdbl (target k2 : Nat) : Nat :=
  Classical.choose (cdbl_min_witness target k2)

theorem cdbl_ge (target k2 : Nat) : max k2 1 * 2 ^ cdbl target k2 ≥ target :=
  (Classical.choose_spec (cdbl_min_witness target k2)).1

theorem cdbl_min (target k2 d : Nat) (h : max k2 1 * 2 ^ d ≥ target) : cdbl target k2 ≤ d :=
  (Classical.choose_spec (cdbl_min_witness target k2)).2 d h

/-- **闭式解主定理**（k₂ < target，k₂ ≥ 1）：
最少步数 = min( cost(c), cost(c−1) )，其中 c 是最小倍增次数。 -/
theorem dist_closed_of (k2 target c : Nat) (hk2 : 0 < k2) (hlt : k2 < target)
    (hge : k2 * 2 ^ c ≥ target) (hmin : ∀ d, k2 * 2 ^ d ≥ target → c ≤ d) :
    dist k2 target = min (costOf k2 target c) (costOf k2 target (c - 1)) := by
  have htarget : 0 < target := by omega
  have hcpos : 1 ≤ c := by
    cases c with
    | zero =>
      exfalso
      rw [Nat.pow_zero] at hge
      omega
    | succ c => omega
  have hc1under : k2 * 2 ^ (c - 1) < target := by
    by_cases hge1 : k2 * 2 ^ (c - 1) ≥ target
    · exfalso
      have := hmin (c - 1) hge1
      omega
    · omega
  have hge' : min (costOf k2 target c) (costOf k2 target (c - 1)) ≥ dist k2 target := by
    have h1 : dist k2 target ≤ costOf k2 target c := dist_le_cost hk2 htarget
    have h2 : dist k2 target ≤ costOf k2 target (c - 1) := dist_le_cost hk2 htarget
    omega
  have hle : min (costOf k2 target c) (costOf k2 target (c - 1)) ≤ dist k2 target := by
    have ⟨d0, hd0⟩ := reach_ge_cost (dist_reach k2 target)
    by_cases hcase : c ≤ d0
    · have hchain := costOf_over_min k2 target (d0 - c) c hge
      have hEq : c + (d0 - c) = d0 := by omega
      rw [hEq] at hchain
      omega
    · have hEq2 : d0 + (c - 1 - d0) = c - 1 := by omega
      have hm : k2 * 2 ^ (d0 + (c - 1 - d0)) < target := by rw [hEq2]; exact hc1under
      have hchain := costOf_under_min k2 target hk2 (c - 1 - d0) d0 hm
      rw [hEq2] at hchain
      omega
  omega

theorem dist_closed (k2 target : Nat) (hk2 : 0 < k2) (hlt : k2 < target) :
    dist k2 target = min (costOf k2 target (cdbl target k2))
        (costOf k2 target (cdbl target k2 - 1)) := by
  have hmax : max k2 1 = k2 := by omega
  refine dist_closed_of k2 target (cdbl target k2) hk2 hlt ?_ ?_
  · have hge := cdbl_ge target k2
    rw [hmax] at hge
    exact hge
  · intro d hd
    refine cdbl_min target k2 d ?_
    rw [hmax]
    exact hd

/-! ## 十五、起点为 0 的特例与最终求解函数 -/

theorem reach_first {x z t : Nat} (h : Reach x z (t + 1)) :
    ∃ y, Step x y ∧ Reach y z t :=
  match h with | .step hs r => ⟨_, hs, r⟩

theorem step_zero_inv {y : Nat} (h : Step 0 y) : y = 1 := by
  have hb : BwdStep y 0 := h
  have hinv := bwdStep_inv hb
  omega

/-- dist(0, n) = 1 + dist(1, n)（n ≥ 1；从 0 出发第一步只能是 0 → 1）。 -/
theorem dist_zero_succ (n : Nat) (hn : 0 < n) : dist 0 n = 1 + dist 1 n := by
  have hle : dist 0 n ≤ dist 1 n + 1 :=
    dist_le_of_reach (Reach.step (Step.plus 0) (dist_reach 1 n))
  have hge : 1 + dist 1 n ≤ dist 0 n := by
    cases hD : dist 0 n with
    | zero =>
      exfalso
      have hr := dist_reach 0 n
      rw [hD] at hr
      have h0 := reach_zero hr
      omega
    | succ t =>
      have hr := dist_reach 0 n
      rw [hD] at hr
      have ⟨y, hs1, hs2⟩ := reach_first hr
      have hy : y = 1 := step_zero_inv hs1
      rw [hy] at hs2
      have h1 : dist 1 n ≤ t := dist_le_of_reach hs2
      omega
  omega

/-- 与 C++ `solve(k, n)` 结构完全一致的求解函数（start = 农夫位置，target = 牛位置）：
  * start ≥ target：答案 start − target；
  * 否则令 k₂ = max(start,1)（k=0 时先走到 1，额外 +1 步），c = 最小倍增次数，
    答案 = min(target − start, min(cost(c), cost(c−1)))。 -/
noncomputable def solve (start target : Nat) : Nat :=
  if start ≥ target then start - target
  else
    min (target - start)
      (min ((if start = 0 then 1 else 0) + costOf (max start 1) target (cdbl target (max start 1)))
        (if cdbl target (max start 1) = 0 then target - start
         else (if start = 0 then 1 else 0)
             + costOf (max start 1) target (cdbl target (max start 1) - 1)))

/-- **主定理：solve 的输出就是最少步数。** -/
theorem solve_eq_dist (start target : Nat) : solve start target = dist start target := by
  unfold solve
  by_cases hge : start ≥ target
  · rw [ite_eq_left hge]
    exact (dist_eq_of_ge start target hge).symm
  · rw [ite_eq_right hge]
    have htarget : 0 < target := by omega
    by_cases hz : start = 0
    · subst hz
      have hmax : max 0 1 = 1 := by decide
      rw [hmax]
      have hz' : dist 0 target = 1 + dist 1 target := dist_zero_succ target htarget
      have hup : dist 0 target ≤ target - 0 :=
        dist_le_of_reach (reach_up target 0 (by omega))
      by_cases ht1 : target = 1
      · -- 特例：target = 1，此时 c = 0
        subst ht1
        have hc0 : cdbl 1 1 = 0 := by
          have hle := cdbl_min 1 1 0 (by omega)
          omega
        rw [hc0]
        simp only [ite_true, Nat.sub_zero]
        have hc : costOf 1 1 0 = 0 := by
          simp [costOf, absg]
        have hd : dist 0 1 = 1 := by
          rw [dist_zero_succ 1 (by omega), dist_eq_of_ge 1 1 (by omega)]
        rw [hc]
        omega
      · have hM : dist 1 target = min (costOf 1 target (cdbl target 1))
            (costOf 1 target (cdbl target 1 - 1)) := dist_closed 1 target (by omega) (by omega)
        have hc1 : 1 ≤ cdbl target 1 := by
          cases hc : cdbl target 1 with
          | zero =>
            exfalso
            have hge1 := cdbl_ge target 1
            rw [hc] at hge1
            omega
          | succ c => omega
        rw [ite_eq_right (show ¬(cdbl target 1 = 0) from by omega), ite_eq_left rfl]
        omega
    · have hmax : max start 1 = start := Nat.max_eq_left (by omega)
      rw [hmax]
      have hM : dist start target = min (costOf start target (cdbl target start))
          (costOf start target (cdbl target start - 1)) :=
        dist_closed start target (by omega) (by omega)
      have hc1 : 1 ≤ cdbl target start := by
        cases hc : cdbl target start with
        | zero =>
          exfalso
          have hge1 := cdbl_ge target start
          rw [hc] at hge1
          omega
        | succ c => omega
      rw [ite_eq_right (show ¬(cdbl target start = 0) from by omega),
          ite_eq_right (show ¬(start = 0) from by omega)]
      have hup : dist start target ≤ target - start :=
        dist_le_of_reach (reach_up target start (by omega))
      omega

/-! ## 十六、样例验证 -/

-- POJ 样例：农夫在 5，牛在 17，答案 4（与 verify_out.txt 的 BFS 对照一致）。
example : f 5 17 = 4 := by native_decide

example : solve 5 17 = 4 := by
  rw [solve_eq_dist, ← f_eq_dist]
  native_decide

-- solve(0, 3) = 3（0→1→2→3）。
example : solve 0 3 = 3 := by
  rw [solve_eq_dist, ← f_eq_dist]
  native_decide

-- 任意位置对上 solve 与 O(log) 递归解 f 一致（机器可计算的小抽查）。
example : solve 45 290 = f 45 290 := by
  rw [solve_eq_dist, f_eq_dist]

end Poj3278

section AxiomCheck
open Poj3278
#print axioms solve_eq_dist
#print axioms dist_closed
#print axioms cost_reach
#print axioms reach_ge_cost
#print axioms f_is_minimal
#print axioms CR_min
#print axioms nafW_add_pow
end AxiomCheck
