// verify.cpp —— 对 poj3278.cpp 的 solve() 做全范围验证
// 通过宏改名 main 后直接包含原文件，被测代码一字不改。
#define main poj3278_original_main
#include "poj3278.cpp"
#undef main

#include <chrono>
#include <thread>
#include <atomic>
#include <random>
#include <vector>
#include <string>
#include <cstdio>
#include <mutex>
#include <algorithm>
using namespace std;

typedef long long ll;
typedef unsigned long long ull;

static int g_bound = 100000;        // BFS 边界（= 目标领域上界）
static const int WIDE_FACTOR = 2;   // 自检用的宽边界倍数

static double now_sec() {
    using namespace chrono;
    return duration<double>(steady_clock::now().time_since_epoch()).count();
}

// 独立参考 BFS：一次性算出起点 s 到 [0,g_bound] 内所有位置的最短步数。
// （与原版 bfs() 逻辑等价：边界 [0,g_bound]、三种移动 x-1/x+1/2x；
//   区别只是跑完整个队列而不是弹出目标即返回，以便复用给所有终点。）
static void refBFS(int s, int bound, vector<int>& d, vector<int>& q) {
    fill(d.begin(), d.end(), -1);
    int head = 0, tail = 0;
    d[s] = 0; q[tail++] = s;
    while (head < tail) {
        int cur = q[head++];
        int nd = d[cur] + 1;
        if (cur - 1 >= 0       && d[cur - 1] < 0) { d[cur - 1] = nd; q[tail++] = cur - 1; }
        if (cur + 1 <= bound   && d[cur + 1] < 0) { d[cur + 1] = nd; q[tail++] = cur + 1; }
        int dbl = cur << 1;
        if (dbl <= bound       && d[dbl]     < 0) { d[dbl]     = nd; q[tail++] = dbl; }
    }
}

struct Mismatch { int k, n, bfs, solve; };

// 多线程穷举：起点 [0,limStart] × 终点 [0,limTgt]，BFS 边界 = g_bound
static void verifyRangeMT(int limStart, int limTgt, unsigned T, const char* tag) {
    if (T == 0) T = 8;
    printf("[%s] 穷举 [0,%d]^2 = %lld 对, %u 线程 (BFS 边界 %d) ...\n",
           tag, limStart, (ll)(limStart + 1) * (limTgt + 1), T, g_bound);
    fflush(stdout);
    double t0 = now_sec();
    int bound = g_bound;
    atomic<ll> startsDone{0};
    atomic<ll> mismatchCount{0};
    atomic<bool> stopMonitor{false};
    vector<Mismatch> allBad;
    mutex badMutex;

    auto worker = [&, bound](ll kFrom, ll kTo) {
        vector<int> d(bound + 1), q(bound + 1);
        for (ll k = kFrom; k < kTo; k++) {
            refBFS((int)k, bound, d, q);
            for (int n = 0; n <= limTgt; n++) {
                int sv = solve((int)k, n);
                if (sv != d[n]) {
                    mismatchCount++;
                    lock_guard<mutex> lk(badMutex);
                    if (allBad.size() < 30) allBad.push_back({(int)k, n, d[n], sv});
                }
            }
            startsDone++;
        }
    };
    auto monitor = [&]() {
        while (!stopMonitor.load()) {
            this_thread::sleep_for(chrono::seconds(5));
            if (stopMonitor.load()) break;
            ll done = startsDone.load();
            double el = now_sec() - t0;
            double rate = done / max(el, 1e-9);
            double eta = ((ll)limStart + 1 - done) / max(rate, 1e-9);
            printf("\r  [%s] 起点 %lld/%d (%.0f%%), 不一致 %lld, 已用 %.0fs, ETA %.0fs   ",
                   tag, done, limStart + 1, 100.0 * done / (limStart + 1), mismatchCount.load(), el, eta);
            fflush(stdout);
        }
    };

    vector<thread> threads;
    thread mon(monitor);
    ll total = limStart + 1;
    ll chunk = (total + T - 1) / T;
    for (unsigned t = 0; t < T; t++) {
        ll kFrom = (ll)t * chunk;
        ll kTo = min(total, kFrom + chunk);
        if (kFrom >= kTo) break;
        threads.emplace_back(worker, kFrom, kTo);
    }
    for (auto& th : threads) th.join();
    stopMonitor = true;
    mon.join();

    double dt = now_sec() - t0;
    printf("\r  [%s] 完成: 不一致 %lld, 用时 %.1fs                     \n",
           tag, mismatchCount.load(), dt);
    if (!allBad.empty()) {
        printf("  [%s] 不一致样本 (最多 30 个):\n", tag);
        for (auto& m : allBad)
            printf("    起点=%d 终点=%d bfs=%d solve=%d\n", m.k, m.n, m.bfs, m.solve);
    } else {
        printf("  [%s] 通过 —— 全部 %lld 对一致\n", tag, (ll)(limStart + 1) * (limTgt + 1));
    }
    fflush(stdout);
}

// 宽边界自检：对随机+对抗样本，确认 g_bound 边界的 BFS 没有漏掉更优解
static void wideSelfCheck(int bound, unsigned seed, int trials) {
    int wide = bound * WIDE_FACTOR;
    printf("[自检@%d] 宽边界(%d) BFS 抽查 %d 对 ... ", bound, wide, trials);
    fflush(stdout);
    mt19937 rng(seed);
    uniform_int_distribution<int> uid(0, bound);
    uniform_int_distribution<int> hi(bound / 2, bound);   // 对抗: 大起点
    uniform_int_distribution<int> hn(bound * 9 / 10, bound); // 对抗: 大终点
    vector<int> dw(wide + 1), qw(wide + 1), d2(bound + 1), q2(bound + 1);
    int badWideVsRef = 0, badWideVsSolve = 0;
    for (int t = 0; t < trials; t++) {
        int k, n;
        if (t % 2) { k = hi(rng); n = hn(rng); }
        else { k = uid(rng); n = uid(rng); }
        refBFS(k, wide, dw, qw);       // 宽边界距离
        refBFS(k, bound, d2, q2);      // 窄边界距离
        if (dw[n] != d2[n]) badWideVsRef++;
        if (dw[n] != solve(k, n)) badWideVsSolve++;
    }
    if (badWideVsRef == 0 && badWideVsSolve == 0)
        printf("通过 (宽vs窄、宽vs solve 均一致)\n");
    else
        printf("发现问题: 宽vs窄不一致 %d, 宽vs solve 不一致 %d\n", badWideVsRef, badWideVsSolve);
    fflush(stdout);
}

int main() {
    unsigned T = thread::hardware_concurrency();
    if (T == 0) T = 8;
    if (T > 20) T = 20;

    g_bound = 100000;
    printf("POJ3278 solve() 验证器（BFS 参考, 边界 [0,%d], %u 线程）\n", g_bound, T);

    // ---------- 阶段A：小范围，直接逐对调用【原版 bfs()】 vs solve() ----------
    printf("[阶段A] [0,64]^2 逐对调用原版 bfs() vs solve() ... ");
    fflush(stdout);
    {
        int bad = 0;
        ull checked = 0;
        for (int i = 0; i <= 64; i++)
            for (int j = 0; j <= 64; j++) {
                int b = bfs(i, j);       // 原版 bfs(起点, 终点)
                int s = solve(i, j);     // 原版 solve(起点, 终点)
                checked++;
                if (b != s) {
                    if (bad < 20) printf("\n  不一致: 起点=%d 终点=%d bfs=%d solve=%d", i, j, b, s);
                    bad++;
                }
            }
        if (bad == 0) printf("通过 (%llu 对一致)\n", checked);
        else          printf("  阶段A: 共 %d 处不一致 / %llu 对\n", bad, checked);
        fflush(stdout);
    }

    // ---------- 阶段A2：把参考 refBFS 与原版 bfs() 绑定（随机抽查全范围） ----------
    printf("[阶段A2] refBFS 与原版 bfs() 随机绑定 400 对 ... ");
    fflush(stdout);
    {
        mt19937 rng(12345);
        uniform_int_distribution<int> uid(0, g_bound);
        vector<int> d(g_bound + 1), q(g_bound + 1);
        int bad = 0;
        for (int t = 0; t < 400; t++) {
            int i = uid(rng), j = uid(rng);
            refBFS(i, g_bound, d, q);
            if (bfs(i, j) != d[j]) bad++;
        }
        if (bad == 0) printf("通过\n");
        else          printf("失败: %d 处不一致\n", bad);
        fflush(stdout);
    }

    printf("  样例 (5,17): bfs=%d solve=%d (POJ 期望 4)\n", bfs(5, 17), solve(5, 17));

    // ---------- 阶段B：中等范围穷举（每起点一次 BFS, 多线程） ----------
    verifyRangeMT(4096, 4096, T, "阶段B");

    // ---------- 阶段C：POJ 全范围 [0,100000]^2 穷举 ----------
    verifyRangeMT(100000, 100000, T, "阶段C");

    // ---------- 阶段D：参考自检（宽边界 200000） ----------
    wideSelfCheck(100000, 777, 300);

    // ---------- 阶段E（加码, 超出 POJ 领域）：[0,262144]^2 穷举 ----------
    g_bound = 262144;
    verifyRangeMT(262144, 262144, T, "阶段E");
    wideSelfCheck(262144, 999, 200);

    printf("验证结束。\n");
    return 0;
}
