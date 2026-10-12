# POJ 3278 · Catch That Cow — O(log) 解法与机器验证

> POJ 3278 "Catch That Cow" 的 **O(log k) 数学解法**，正确性由两条独立途径机器验证：
> C++ 全范围穷举对照 BFS（最大范围 687 亿对全部一致），以及 **Lean 4 形式化证明**
> （仅核心库、无 Mathlib、零 `sorry`）。
>
> An O(log k) closed-form solution to POJ 3278 "Catch That Cow", verified two independent ways:
> exhaustive checking against BFS in C++ (up to 6.87 × 10¹⁰ pairs), and a complete
> machine-checked Lean 4 proof (core library only, no Mathlib, no `sorry`).

## 题目

农夫约翰位于数轴上的 `n`，牛位于 `k`（`0 ≤ n, k ≤ 100000`）。每一步他可以移动到
`n − 1`、`n + 1` 或 `2n`（`−1` 与 `×2` 要求当前位置大于 0）。求抓到牛的最少步数。

样例：`n = 5, k = 17`，答案 `4` —— 路径 5 → 4 → 8 → 16 → 17（`−1, ×2, ×2, +1`）。

## 解法

本题的标准做法是 BFS，复杂度 O(值域)。本仓库给出一个 **O(log k)** 的直接解法 `solve()`。
最优策略总可以写成三段：

1. 先做 `d` 次翻倍（起点为 0 时必须先走一步到 1）；
2. 在原尺度上整段走 `q` 个 `±1` —— 翻倍后折算为 `2^d · q` 的距离；
3. 剩下小于 `2^d` 的零头 `r`，写成**带符号二进制表示（NAF，非相邻形式）**，
   代价为 `r` 的 NAF 权重（非零项数）。

总代价为 `d + q + naf(r)`。只需考察 `d` 的最小值（使 `n · 2^d ≥ k`）及其减一两个候选，
与"全程不翻倍、直接走 `|n − k|`"取最小即可。实现见
[`poj3278.cpp`](poj3278.cpp)（约 100 行，含 BFS 参考实现）。

## 机器验证

### 1. 穷举验证（C++）

[`verify.cpp`](verify.cpp) 通过宏改名 `main` 后**原样包含** `poj3278.cpp`
（被测代码一字不改），将 `solve()` 与 BFS 参考实现逐对对照，20 线程穷举：

| 阶段 | 穷举范围 | 对数 | 结果 |
| --- | --- | --- | --- |
| B | [0, 4096]² | 16,785,409 | ✅ 全部一致（约 5 s） |
| C | [0, 100000]²（题目全值域） | 10,000,200,001 | ✅ 全部一致（约 10 s） |
| E | [0, 262144]²（约 2.6 倍值域） | 68,720,001,025 | ✅ 全部一致（约 220 s） |

另有小范围逐对、随机绑定及两倍宽边界的 BFS 自检，完整日志见
[`verify_out.txt`](verify_out.txt)。

### 2. 形式化证明（Lean 4）

[`Poj3278.lean`](Poj3278.lean) 用**仅核心库（无 Mathlib）**的 Lean 4 从零形式化了该解法：
归纳定义移动规则 `Step` 与 `s` 步可达 `Reach`，严格定义最少步数 `dist`，
证明 O(log) 递归解 `f` 及与 C++ `solve()` 对应的实现确实给出最少步数。核心定理：

```lean
/-- 最少步数的完整刻画：f n k 步确实可达，且任何路径步数都不小于它。 -/
theorem f_is_minimal (n k : Nat) :
    Reach n k (f n k) ∧ ∀ s, Reach n k s → f n k ≤ s

/-- O(log) 递归解 f 的输出就是最少步数。 -/
theorem f_eq_dist (n k : Nat) : f n k = dist n k

/-- 与 C++ solve() 对应的实现（d 与 d−1 两候选 + 直接走，取最小）等于最少步数。 -/
theorem solve_eq_dist (start target : Nat) : solve start target = dist start target
```

文件末尾的 `#print axioms` 确认关键定理仅依赖 Lean 的三个标准逻辑公理
（`propext`、`Classical.choice`、`Quot.sound`）——**无自定义公理、无 `sorry`**。

## 仓库结构

| 文件 | 说明 |
| --- | --- |
| [`poj3278.cpp`](poj3278.cpp) | C++ 解法：BFS 参考实现 + O(log) `solve()`，POJ 提交入口 |
| [`verify.cpp`](verify.cpp) | 穷举验证器（原样包含被测代码，与 BFS 全范围对照） |
| [`verify_out.txt`](verify_out.txt) | 最近一次全量验证日志 |
| [`Poj3278.lean`](Poj3278.lean) | Lean 4 完整形式化证明 + 公理检查 |
| `lean-toolchain` | Lean 工具链版本（v4.34.1，供 elan 自动安装） |

## 构建与运行

**C++ 解法**

```bash
g++ -O2 -o poj3278 poj3278.cpp
echo "5 17" | ./poj3278        # 输出 4
```

**穷举验证**（20 线程，全程约 4 分钟）

```bash
g++ -O2 -o verify verify.cpp
./verify
```

**Lean 证明**（安装 [elan](https://github.com/leanprover/elan) 后会按 `lean-toolchain`
自动使用 v4.34.1；无需 Mathlib）

```bash
lean Poj3278.lean
```

## 许可

[MIT](LICENSE)
