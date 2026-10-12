// poj3278.cpp —— POJ 3278 "Catch That Cow"
//
// 题意：农夫位于 n，牛位于 k（0 ≤ n, k ≤ 100000）。每步可执行三种移动之一：
//       n → n−1（n > 0）、n → n+1、n → 2n（n > 0）。求最少多少步能抓到牛。
//
// 本文件提供两个实现（参数约定一致：n 为起点，k 为终点）：
//   * bfs(n, k)   经典 BFS 参考实现，O(值域)，供 verify.cpp 做对照；
//   * solve(n, k) O(log k) 数学解法，本题提交入口。思路：
//       最优策略形如「先做 d 次翻倍（起点为 0 时须先走一步到 1），
//       在原尺度上整段走 q 个 ±1（翻倍后折算为 2^d·q 的距离），
//       再用带符号二进制表示（NAF）补上小于 2^d 的零头 r」，
//       代价为 d + q + naf(r)；只需考察 d 的最小值及其减一两个候选，
//       与「全程不翻倍直接走 |n − k|」取最小。
//       正确性由同仓库 Poj3278.lean 的形式化证明（solve_eq_dist）
//       与 verify.cpp 的全范围穷举验证共同保证。
//
// 编译：g++ -O2 -o poj3278 poj3278.cpp
// 输入：一行两个整数 n k；输出：最少步数。

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <queue>

using namespace std;

/// 题目值域上界（BFS 的移动边界，含 100000 本身）。
const int kBound = 100000;

/// 经典 BFS 参考实现：三种移动 x−1 / x+1 / 2x，边界 [0, kBound]。
int bfs(int n, int k) {
    if (n >= k) return n - k;  // 起点在终点右侧时只能逐步走回

    static int dist[kBound + 1];
    static bool visited[kBound + 1];
    fill(dist, dist + kBound + 1, 0);
    fill(visited, visited + kBound + 1, false);

    queue<int> q;
    q.push(n);
    visited[n] = true;

    while (!q.empty()) {
        int curr = q.front();
        q.pop();

        if (curr == k) return dist[k];

        int moves[3] = {curr - 1, curr + 1, curr * 2};
        for (int next : moves) {
            if (next >= 0 && next <= kBound && !visited[next]) {
                visited[next] = true;
                dist[next] = dist[curr] + 1;
                q.push(next);
            }
        }
    }
    return -1;  // 不可达（在题目约束下不会发生）
}

/// 把 a 的所有低位 smear 成 1，得到掩码 2^bitlen(a) − 1。
static int bitMask(int x) {
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    return x;
}

/// n 的 NAF（非相邻形式）权重：把 n 写成 ±2^e 之和所需的最少项数。
static int nafWeight(long long n) {
    if (n < 0) n = -n;
    int count = 0;
    while (n > 0) {
        if (n % 2 == 1) {
            // 末两位为 11（n % 4 == 3）时进位 n+1，否则借位 n−1，
            // 使非零位互不相邻，项数从而最少。
            if (n % 4 == 3) n += 1;
            else n -= 1;
            ++count;
        }
        n /= 2;
    }
    return count;
}

/// 将 a 连续翻倍直到不小于 b 所需的最少次数。
static int doublingsToReach(int a, int b) {
    int count = 0;
    while (a < b) {
        a <<= 1;
        ++count;
    }
    return count;
}

/// O(log k) 数学解法（本题提交入口，详细思路见文件头注释）。
int solve(int n, int k) {
    if (n >= k) return n - k;

    int base = n, extra = 0;  // 起点为 0 时 −1 / ×2 均不可行，先走一步到 1
    if (n == 0) {
        extra = 1;
        base = 1;
    }

    int d = doublingsToReach(base, k);  // 最小 d 使 base·2^d ≥ k
    int best = k - n;                   // 候选：不做翻倍，全程直接走

    for (int i = 0; i < 2; ++i) {  // 考察 d 与 d−1 两种翻倍次数
        int doubled = base << d;
        int gap = abs(doubled - k);
        int quot = gap / (1 << d);                   // 原尺度上整段的 ±1 步数
        int rem = gap & bitMask((1 << d) >> 1);      // 小于 2^d 的零头
        best = min(best, d + quot + extra + nafWeight(rem));
        if (d == 0) break;
        --d;
    }
    return best;
}

int main() {
    int n, k;
    cin >> n >> k;
    cout << solve(n, k) << '\n';
    return 0;
}
