/* ==========================================================================
 *  动物消消乐 · C 语言控制台版
 *
 *  规则与网页版 v2 一致：
 *   - 三连及以上消除，上方掉落补充，可连锁；连消倍率 1 / 1.5 / 2 / 2.5 ...
 *   - 横向四连 → 直线光（清整行）；纵向四连 → 直线光（清整列）
 *   - L 形 / T 形五连 → 炸弹（只炸自己周围 3×3）
 *   - 五连一线 → 彩虹（与任意动物交换清全场该种；与直线/炸弹交换则
 *     全场该种全部变成对应特效再一起引爆；两只彩虹交换清全场）
 *   - 直线光和炸弹仍是原动物，必须被同类三连带上才引爆
 *
 *  编译： tcc match3.c -o match3.exe
 *         gcc match3.c -o match3.exe
 *  运行： match3.exe            正常游戏
 *         match3.exe --test     引擎自测（不需要键盘）
 * ========================================================================== */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <windows.h>
#include <conio.h>

#define N 8
#define EMPTY (-1)
#define MAXT 6

/* 特效编号 */
#define SP_NONE 0
#define SP_H    1   /* 清整行 */
#define SP_V    2   /* 清整列 */
#define SP_BOMB 3   /* 3x3 */
#define SP_RB   4   /* 彩虹 */

/* 目标类型 */
#define G_SCORE   0
#define G_COLLECT 1
#define G_ICE     2
#define G_COMBO   3
#define G_SPECIAL 4

#define MAX_CRE 8
#define QCAP    256

/* 过关后，每一步没用掉的步数折算成多少分 */
#define BONUS_PER_MOVE 100

typedef struct {
    int moves, types, ng;
    int gk[3], ga[3], gn[3];
} Level;

static const Level LEVELS[] = {
    {22, 5, 1, {G_SCORE},   {0},           {2200}},
    {18, 5, 1, {G_COLLECT}, {0},           {56}},
    {24, 5, 1, {G_ICE},     {0},           {12}},
    {24, 5, 1, {G_COMBO},   {0},           {5}},
    {24, 6, 2, {G_COLLECT, G_COLLECT},     {1, 4},        {25, 17}},
    {24, 6, 1, {G_SPECIAL}, {0},           {6}},
    {28, 6, 2, {G_ICE, G_COLLECT},         {0, 5},        {9, 10}},
    {30, 5, 1, {G_SCORE},   {0},           {3100}},
    {26, 6, 1, {G_COLLECT}, {3},           {26}},
    {26, 6, 1, {G_COMBO},   {0},           {4}},
    {28, 6, 1, {G_ICE},     {0},           {14}},
    {28, 6, 1, {G_SPECIAL}, {0},           {8}},
    {30, 6, 1, {G_COLLECT}, {2},           {29}},
    {30, 6, 2, {G_ICE, G_COLLECT},         {0, 5},        {8, 10}},
    {28, 6, 1, {G_COMBO},   {0},           {4}},
    {30, 6, 1, {G_SCORE},   {0},           {1750}},
    {30, 6, 3, {G_COLLECT, G_COLLECT, G_COLLECT}, {0, 3, 5}, {25, 18, 25}},
    {32, 6, 2, {G_ICE, G_SPECIAL},         {0, 0},        {12, 4}},
    {34, 6, 1, {G_SCORE},   {0},           {1900}},
    {36, 6, 3, {G_ICE, G_COLLECT, G_SCORE}, {0, 5, 0},    {14, 12, 1800}}
};
#define LEVEL_COUNT ((int)(sizeof(LEVELS) / sizeof(LEVELS[0])))

/* ---------------- 全局状态 ---------------- */
static int type[N][N];      /* 动物种类，EMPTY 表示空格 */
static int sp[N][N];        /* 特效 */
static int ice[N][N];       /* 冰块层数 0/1/2 */

static int cur_r, cur_c;    /* 光标 */
static int sel_r = -1, sel_c = -1;

static int score, moves, combo_max, special_made;
static int collected[MAXT];
static int level_idx, types_now, level_over, level_win;
static int g_headless = 0;

static char g_msg[160];

/* 交换的两格，用于决定新特效生成在哪 */
static int sw1r, sw1c, sw2r, sw2c;

/* 每轮结算用的临时缓冲 */
static int clr[N][N];
static int creR[MAX_CRE], creC[MAX_CRE], creS[MAX_CRE], nCre = 0;

static const int DR[4] = {1, -1, 0, 0};
static const int DC[4] = {0, 0, 1, -1};

static const char ANIMAL_CH[MAXT] = {'A', 'B', 'C', 'D', 'E', 'F'};
static const int  ANIMAL_BG[MAXT] = {224, 223, 194, 189, 229, 159};
static const char *ANIMAL_CN[MAXT] = {"兔", "狐", "蛙", "猴", "熊", "虎"};

static const double MULT[] = {1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0, 6.0, 8.0};

/* ---------------- 基础工具 ---------------- */
static int rnd_type(void) { return rand() % types_now; }

static void swap_cells(int r1, int c1, int r2, int c2)
{
    int t = type[r1][c1], s = sp[r1][c1];
    type[r1][c1] = type[r2][c2]; sp[r1][c1] = sp[r2][c2];
    type[r2][c2] = t;            sp[r2][c2] = s;
}

/* 找出所有三连及以上的格子，mark 为 1；返回是否有可消 */
static int find_matches(int mark[N][N])
{
    int r, c, e, i, any = 0;
    memset(mark, 0, sizeof(int) * N * N);

    for (r = 0; r < N; r++) {
        c = 0;
        while (c < N) {
            if (type[r][c] == EMPTY) { c++; continue; }
            e = c;
            while (e + 1 < N && type[r][e + 1] == type[r][c]) e++;
            if (e - c >= 2) { for (i = c; i <= e; i++) mark[r][i] = 1; any = 1; }
            c = e + 1;
        }
    }
    for (c = 0; c < N; c++) {
        r = 0;
        while (r < N) {
            if (type[r][c] == EMPTY) { r++; continue; }
            e = r;
            while (e + 1 < N && type[e + 1][c] == type[r][c]) e++;
            if (e - r >= 2) { for (i = r; i <= e; i++) mark[i][c] = 1; any = 1; }
            r = e + 1;
        }
    }
    return any;
}

/* 某特效的影响范围 */
static int blast_cells(int r, int c, int out[][2])
{
    int n = 0, i, dr, dc, rr, cc;
    switch (sp[r][c]) {
    case SP_H:
        for (i = 0; i < N; i++) { out[n][0] = r; out[n][1] = i; n++; }
        break;
    case SP_V:
        for (i = 0; i < N; i++) { out[n][0] = i; out[n][1] = c; n++; }
        break;
    case SP_BOMB:
        for (dr = -1; dr <= 1; dr++) for (dc = -1; dc <= 1; dc++) {
            rr = r + dr; cc = c + dc;
            if (rr >= 0 && rr < N && cc >= 0 && cc < N) { out[n][0] = rr; out[n][1] = cc; n++; }
        }
        break;
    case SP_RB:
        for (rr = 0; rr < N; rr++) for (cc = 0; cc < N; cc++)
            if (type[rr][cc] == type[r][c]) { out[n][0] = rr; out[n][1] = cc; n++; }
        break;
    }
    return n;
}

/* ---------------- 生成特效判定 ---------------- */
static void detect_creations(int mark[N][N], int r1, int c1, int r2, int c2)
{
    int vis[N][N], ing[N][N];
    int qr[64], qc[64], crs[64], ccs[64];
    int r, c, i, d;

    memset(vis, 0, sizeof vis);
    nCre = 0;

    for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
        int qh = 0, qt = 0, n = 0, has_sp = 0;
        int sameRow = 1, sameCol = 1, mh = 0, mv = 0, s = -1;
        int pr = -1, pc = -1;

        if (!mark[r][c] || vis[r][c]) continue;

        qr[qt] = r; qc[qt] = c; qt++; vis[r][c] = 1;
        while (qh < qt) {
            int rr = qr[qh], cc = qc[qh]; qh++;
            crs[n] = rr; ccs[n] = cc; n++;
            for (d = 0; d < 4; d++) {
                int nr = rr + DR[d], nc = cc + DC[d];
                if (nr >= 0 && nr < N && nc >= 0 && nc < N &&
                    mark[nr][nc] && !vis[nr][nc]) {
                    vis[nr][nc] = 1; qr[qt] = nr; qc[qt] = nc; qt++;
                }
            }
        }

        for (i = 0; i < n; i++) if (sp[crs[i]][ccs[i]]) has_sp = 1;
        if (has_sp) continue;              /* 已经带特效的一组只爆不再造 */

        for (i = 1; i < n; i++) {
            if (crs[i] != crs[0]) sameRow = 0;
            if (ccs[i] != ccs[0]) sameCol = 0;
        }

        memset(ing, 0, sizeof ing);
        for (i = 0; i < n; i++) ing[crs[i]][ccs[i]] = 1;
        for (i = 0; i < n; i++) {
            int rr = crs[i], cc = ccs[i];
            int h = 1, x = cc + 1;
            while (x < N && ing[rr][x]) { h++; x++; }
            int v = 1, y = rr + 1;
            while (y < N && ing[y][cc]) { v++; y++; }
            if (h > mh) mh = h;
            if (v > mv) mv = v;
        }

        if (sameRow || sameCol) {
            if (n >= 5) s = SP_RB;
            else if (n == 4) s = sameRow ? SP_H : SP_V;
        } else {
            if (mh >= 3 && mv >= 3) s = SP_BOMB;
            else if (mh >= 4) s = SP_H;
            else if (mv >= 4) s = SP_V;
        }
        if (s < 0) continue;

        for (i = 0; i < n && pr < 0; i++)
            if ((crs[i] == r1 && ccs[i] == c1) || (crs[i] == r2 && ccs[i] == c2)) {
                pr = crs[i]; pc = ccs[i];
            }
        if (pr < 0) {
            double ar = 0, ac = 0, bd = 1e9;
            int bi = 0;
            for (i = 0; i < n; i++) { ar += crs[i]; ac += ccs[i]; }
            ar /= n; ac /= n;
            for (i = 0; i < n; i++) {
                double dd = (crs[i] - ar) * (crs[i] - ar) + (ccs[i] - ac) * (ccs[i] - ac);
                if (dd < bd) { bd = dd; bi = i; }
            }
            pr = crs[bi]; pc = ccs[bi];
        }
        if (nCre < MAX_CRE) { creR[nCre] = pr; creC[nCre] = pc; creS[nCre] = s; nCre++; }
    }
}

/* ---------------- 重力与补充 ---------------- */
static void gravity(void)
{
    int c, r;
    for (c = 0; c < N; c++) {
        int w = N - 1;
        for (r = N - 1; r >= 0; r--) {
            if (type[r][c] != EMPTY) {
                if (w != r) {
                    type[w][c] = type[r][c]; sp[w][c] = sp[r][c];
                    type[r][c] = EMPTY;      sp[r][c] = 0;
                }
                w--;
            }
        }
        for (r = w; r >= 0; r--) { type[r][c] = rnd_type(); sp[r][c] = SP_NONE; }
    }
}

/* ---------------- 绘制 ---------------- */
static void draw(void)
{
    int r, c, i;
    const Level *lv;

    if (g_headless) return;
    lv = &LEVELS[level_idx];

    printf("\x1b[H");
    printf("  \x1b[1m动物消消乐 · C 语言版\x1b[0m              第 %d / %d 关\n", level_idx + 1, LEVEL_COUNT);
    printf("  分数 \x1b[1;31m%d\x1b[0m     剩余步数 \x1b[1;34m%d\x1b[0m     最高连消 \x1b[1;33m%s%d\x1b[0m\n",
           score, moves, combo_max > 1 ? "x" : "", combo_max > 1 ? combo_max : 0);
    printf("  任务: ");
    for (i = 0; i < lv->ng; i++) {
        int done = 0, have = 0;
        if (lv->gk[i] == G_SCORE)   { have = score; done = score >= lv->gn[i]; printf("达到%d分", lv->gn[i]); }
        else if (lv->gk[i] == G_COLLECT) { have = collected[lv->ga[i]]; done = have >= lv->gn[i]; printf("收集%s x%d", ANIMAL_CN[lv->ga[i]], lv->gn[i]); }
        else if (lv->gk[i] == G_ICE)     { have = 0; done = 0; printf("清冰x%d", lv->gn[i]); }
        else if (lv->gk[i] == G_COMBO)   { have = combo_max; done = have >= lv->gn[i]; printf("连消x%d", lv->gn[i]); }
        else if (lv->gk[i] == G_SPECIAL) { have = special_made; done = have >= lv->gn[i]; printf("造特效x%d", lv->gn[i]); }
        if (done) printf("\x1b[32m(完成)\x1b[0m");
        else {
            if (lv->gk[i] == G_ICE) {
                int left = 0, rr, cc;
                for (rr = 0; rr < N; rr++) for (cc = 0; cc < N; cc++) if (ice[rr][cc] > 0) left++;
                printf("(%d/%d)", lv->gn[i] - left, lv->gn[i]);
            } else printf("(%d/%d)", have, lv->gn[i]);
        }
        if (i + 1 < lv->ng) printf("  ");
    }
    printf("\n\n");

    for (r = 0; r < N; r++) {
        printf("  ");
        for (c = 0; c < N; c++) {
            char ch = ANIMAL_CH[type[r][c] < 0 ? 0 : type[r][c]];
            int  bg = ANIMAL_BG[type[r][c] < 0 ? 0 : type[r][c]];
            char lb = ' ', rb = ' ';
            if (sp[r][c] == SP_H) ch = '=';
            else if (sp[r][c] == SP_V) ch = '|';
            else if (sp[r][c] == SP_BOMB) ch = '*';
            else if (sp[r][c] == SP_RB) ch = '@';
            if (ice[r][c] > 0) { lb = '['; rb = ']'; bg = 159; }
            if (sel_r == r && sel_c == c) printf("\x1b[7m");
            printf("\x1b[48;5;%dm\x1b[38;5;16m%c%c%c\x1b[0m ", bg, lb, ch, rb);
        }
        printf("\n");
    }

    printf("\n  \x1b[90m");
    for (i = 0; i < types_now; i++) printf("%c=%s ", ANIMAL_CH[i], ANIMAL_CN[i]);
    printf("\x1b[0m\n");
    printf("  \x1b[90m= 清行  | 清列  * 炸弹(3x3)  @ 彩虹  [ ] 冰\x1b[0m\n");
    printf("  \x1b[1m方向键\x1b[0m 移动   \x1b[1m空格\x1b[0m 选中/交换   \x1b[1mh\x1b[0m 提示   \x1b[1mr\x1b[0m 重开   \x1b[1mq\x1b[0m 退出   \x1b[90m过关时每剩 1 步 = %d 分\x1b[0m\n", BONUS_PER_MOVE);
    if (g_msg[0]) printf("  \x1b[1;35m%s\x1b[0m\n", g_msg);
    else printf("\n");
    fflush(stdout);
}

/* ---------------- 结算：连锁、特效、掉落 ---------------- */
static int is_creation_cell(int r, int c)
{
    int i;
    for (i = 0; i < nCre; i++) if (creR[i] == r && creC[i] == c) return 1;
    return 0;
}

static void resolve(int preclr[N][N])
{
    int cascade = 0, first = 1;

    while (1) {
        int fromMatch = 0, any, r, c, i;

        memset(clr, 0, sizeof clr);
        if (first && preclr) { memcpy(clr, preclr, sizeof clr); any = 1; }
        else { any = find_matches(clr); }
        first = 0;
        if (!any) break;

        cascade++;
        if (cascade > 20) break;

        nCre = 0;
        fromMatch = (preclr == NULL);
        if (fromMatch) detect_creations(clr, sw1r, sw1c, sw2r, sw2c);

        /* 特效连锁激活 */
        {
            int act[N][N];
            int qr[QCAP], qc[QCAP], qh = 0, qt = 0;
            int cells[128][2], nb, activated = 0, cleared = 0;
            double mult;
            int gain;

            memset(act, 0, sizeof act);
            for (r = 0; r < N; r++) for (c = 0; c < N; c++)
                if (clr[r][c] && sp[r][c] && !act[r][c]) {
                    act[r][c] = 1; qr[qt] = r; qc[qt] = c; qt++;
                }
            while (qh < qt) {
                int rr = qr[qh], cc = qc[qh]; qh++;
                nb = blast_cells(rr, cc, cells);
                for (i = 0; i < nb; i++) {
                    int r2 = cells[i][0], c2 = cells[i][1];
                    clr[r2][c2] = 1;
                    if (sp[r2][c2] && !act[r2][c2]) {
                        act[r2][c2] = 1;
                        if (qt < QCAP) { qr[qt] = r2; qc[qt] = c2; qt++; }
                    }
                }
            }

            for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
                if (clr[r][c]) cleared++;
                if (act[r][c]) activated++;
            }

            mult = MULT[cascade - 1 < 9 ? cascade - 1 : 8];
            gain = (int)(cleared * 8 * mult) + activated * 35;
            score += gain;
            if (cascade > combo_max) combo_max = cascade;

            sprintf(g_msg, "+%d", gain);
            if (cascade > 1) sprintf(g_msg, "连消 x%d  +%d", cascade, gain);

            if (!g_headless) { draw(); Sleep(cascade > 1 ? 220 : 150); }

            /* 移除 */
            for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
                if (!clr[r][c]) continue;
                if (is_creation_cell(r, c)) continue;
                if (type[r][c] == EMPTY) continue;
                if (type[r][c] < MAXT) collected[type[r][c]]++;
                if (ice[r][c] > 0) ice[r][c]--;
                type[r][c] = EMPTY;
                sp[r][c] = SP_NONE;
            }

            /* 落地生成特效 */
            for (i = 0; i < nCre; i++) {
                int rr = creR[i], cc = creC[i];
                if (type[rr][cc] != EMPTY && sp[rr][cc] == SP_NONE) {
                    sp[rr][cc] = creS[i];
                    special_made++;
                }
            }
        }

        gravity();
        if (!g_headless) { draw(); Sleep(200); }
    }
}

/* ---------------- 彩虹等组合 ---------------- */
static void fire_combo(int r1, int c1, int r2, int c2)
{
    static int pre[N][N];
    int s1 = sp[r1][c1], s2 = sp[r2][c2];
    int r, c;

    memset(pre, 0, sizeof pre);

    if (s1 == SP_RB && s2 == SP_RB) {
        for (r = 0; r < N; r++) for (c = 0; c < N; c++) pre[r][c] = 1;
        sprintf(g_msg, "双彩虹！全屏清空");
        resolve(pre);
        return;
    }

    if (s1 == SP_RB || s2 == SP_RB) {
        int rbr, rbc, otr, otc, ott, otsp;
        if (s1 == SP_RB) { rbr = r1; rbc = c1; otr = r2; otc = c2; }
        else             { rbr = r2; rbc = c2; otr = r1; otc = c1; }
        ott = type[otr][otc];
        otsp = sp[otr][otc];

        pre[rbr][rbc] = 1;
        sp[rbr][rbc] = SP_NONE;     /* 彩虹自己消掉，不再额外清它那一类 */

        if (otsp == SP_NONE) {
            for (r = 0; r < N; r++) for (c = 0; c < N; c++)
                if (type[r][c] == ott) pre[r][c] = 1;
            sprintf(g_msg, "彩虹：清掉全场 %c", ANIMAL_CH[ott]);
        } else {
            int flip = 0;
            for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
                if (r == rbr && c == rbc) continue;
                if (type[r][c] == ott) {
                    if (sp[r][c] == SP_NONE) {
                        if (otsp == SP_BOMB) sp[r][c] = SP_BOMB;
                        else sp[r][c] = (flip++ % 2) ? SP_V : SP_H;
                    }
                    pre[r][c] = 1;
                }
            }
            sprintf(g_msg, "彩虹 + %s：全场同类变特效！", otsp == SP_BOMB ? "炸弹" : "直线光");
        }
        resolve(pre);
        return;
    }

    /* 两个普通特效互撞 */
    pre[r1][c1] = 1;
    pre[r2][c2] = 1;
    sprintf(g_msg, "特效组合！");
    resolve(pre);
}

/* ---------------- 交换 ---------------- */
static int try_swap(int r1, int c1, int r2, int c2)
{
    int s1, s2, probe[N][N];

    if (abs(r1 - r2) + abs(c1 - c2) != 1) return 0;

    swap_cells(r1, c1, r2, c2);
    s1 = sp[r1][c1];
    s2 = sp[r2][c2];

    if (s1 == SP_RB || s2 == SP_RB || (s1 && s2)) {
        moves--;
        fire_combo(r1, c1, r2, c2);
        return 1;
    }

    if (!find_matches(probe)) {          /* 凑不出三连，换回去 */
        swap_cells(r1, c1, r2, c2);
        sprintf(g_msg, "这两个换不出三连");
        return 0;
    }

    moves--;
    sw1r = r1; sw1c = c1; sw2r = r2; sw2c = c2;
    resolve(NULL);
    return 1;
}

/* ---------------- 死局与提示 ---------------- */
static int has_move(void)
{
    int r, c, probe[N][N];
    for (r = 0; r < N; r++) for (c = 0; c < N; c++)
        if (sp[r][c] == SP_RB) return 1;
    for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
        if (c + 1 < N) {
            swap_cells(r, c, r, c + 1);
            if (find_matches(probe)) { swap_cells(r, c, r, c + 1); return 1; }
            swap_cells(r, c, r, c + 1);
        }
        if (r + 1 < N) {
            swap_cells(r, c, r + 1, c);
            if (find_matches(probe)) { swap_cells(r, c, r + 1, c); return 1; }
            swap_cells(r, c, r + 1, c);
        }
    }
    return 0;
}

static void shuffle_board(void)
{
    int r, c, guard = 0, probe[N][N];
    do {
        for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
            type[r][c] = rnd_type();
            sp[r][c] = SP_NONE;
        }
    } while ((find_matches(probe) || !has_move()) && guard++ < 200);
}

static int find_hint(int *r1, int *c1, int *r2, int *c2)
{
    int r, c, probe[N][N];

    for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
        if (sp[r][c] == SP_RB) {
            *r1 = r; *c1 = c;
            if (c + 1 < N) { *r2 = r; *c2 = c + 1; return 1; }
            if (r + 1 < N) { *r2 = r + 1; *c2 = c; return 1; }
        }
    }
    for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
        if (sp[r][c] && c + 1 < N && sp[r][c + 1]) { *r1 = r; *c1 = c; *r2 = r; *c2 = c + 1; return 1; }
        if (sp[r][c] && r + 1 < N && sp[r + 1][c]) { *r1 = r; *c1 = c; *r2 = r + 1; *c2 = c; return 1; }
    }
    for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
        if (c + 1 < N) {
            swap_cells(r, c, r, c + 1);
            if (find_matches(probe)) { swap_cells(r, c, r, c + 1); *r1 = r; *c1 = c; *r2 = r; *c2 = c + 1; return 1; }
            swap_cells(r, c, r, c + 1);
        }
        if (r + 1 < N) {
            swap_cells(r, c, r + 1, c);
            if (find_matches(probe)) { swap_cells(r, c, r + 1, c); *r1 = r; *c1 = c; *r2 = r + 1; *c2 = c; return 1; }
            swap_cells(r, c, r + 1, c);
        }
    }
    return 0;
}

/* ---------------- 关卡 ---------------- */
static void new_board(void)
{
    int r, c, t, guard;
    do {
        for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
            guard = 0;
            do {
                t = rnd_type();
            } while (guard++ < 60 &&
                     ((c >= 2 && type[r][c - 1] == t && type[r][c - 2] == t) ||
                      (r >= 2 && type[r - 1][c] == t && type[r - 2][c] == t)));
            type[r][c] = t;
            sp[r][c] = SP_NONE;
        }
    } while (!has_move());
}

static void place_ice(int n)
{
    int cells = N * N, i, k, idx, rr, cc;
    int order[64];
    for (i = 0; i < cells; i++) order[i] = i;
    for (i = cells - 1; i > 0; i--) {
        k = rand() % (i + 1);
        idx = order[i]; order[i] = order[k]; order[k] = idx;
    }
    if (n > cells) n = cells;
    for (i = 0; i < n; i++) {
        rr = order[i] / N; cc = order[i] % N;
        ice[rr][cc] = 1;
    }
    for (i = 0; i < n / 5; i++) {
        rr = order[rand() % n] / N; cc = order[rand() % n] % N;
        ice[rr][cc] = 2;
    }
}

static void start_level(int idx)
{
    int i, r, c;
    const Level *lv;

    level_idx = idx;
    lv = &LEVELS[idx];
    types_now = lv->types;
    moves = lv->moves;
    score = 0; combo_max = 0; special_made = 0;
    level_over = 0; level_win = 0;
    sel_r = -1; sel_c = -1;
    g_msg[0] = 0;

    for (i = 0; i < MAXT; i++) collected[i] = 0;
    for (r = 0; r < N; r++) for (c = 0; c < N; c++) ice[r][c] = 0;

    new_board();

    for (i = 0; i < lv->ng; i++)
        if (lv->gk[i] == G_ICE) place_ice(lv->gn[i]);

    cur_r = 0; cur_c = 0;
}

static int ice_left(void)
{
    int r, c, n = 0;
    for (r = 0; r < N; r++) for (c = 0; c < N; c++) if (ice[r][c] > 0) n++;
    return n;
}

/* 过关结算：没用完的步数一步步折算成分数，返回原剩余步数（星级用） */
static int settle_bonus(void)
{
    int left = moves, bonus = 0;
    while (moves > 0) {
        moves--;
        score += BONUS_PER_MOVE;
        bonus += BONUS_PER_MOVE;
        sprintf(g_msg, "结算剩余步数   +%d   累计 +%d", BONUS_PER_MOVE, bonus);
        if (!g_headless) { draw(); Sleep(55); }
    }
    if (left > 0) sprintf(g_msg, "剩余 %d 步，额外奖励 +%d 分", left, bonus);
    else g_msg[0] = 0;
    return left;
}

static int goals_done(void)
{
    const Level *lv = &LEVELS[level_idx];
    int i;
    for (i = 0; i < lv->ng; i++) {
        int need = lv->gn[i];
        switch (lv->gk[i]) {
        case G_SCORE:   if (score < need) return 0; break;
        case G_COLLECT: if (collected[lv->ga[i]] < need) return 0; break;
        case G_ICE:     if (ice_left() > 0) return 0; break;
        case G_COMBO:   if (combo_max < need) return 0; break;
        case G_SPECIAL: if (special_made < need) return 0; break;
        }
    }
    return 1;
}

/* ---------------- 存档 ---------------- */
static int unlocked = 1;
static int best_stars[LEVEL_COUNT];   /* 每关历史最好星级 0~5 */

static void load_progress(void)
{
    FILE *f = fopen("save.txt", "r");
    int i;
    for (i = 0; i < LEVEL_COUNT; i++) best_stars[i] = 0;
    if (f) {
        if (fscanf(f, "%d", &unlocked) != 1) unlocked = 1;
        for (i = 0; i < LEVEL_COUNT; i++)
            if (fscanf(f, "%d", &best_stars[i]) != 1) best_stars[i] = 0;
        fclose(f);
    }
    if (unlocked < 1) unlocked = 1;
    if (unlocked > LEVEL_COUNT) unlocked = LEVEL_COUNT;
    for (i = 0; i < LEVEL_COUNT; i++) {
        if (best_stars[i] < 0) best_stars[i] = 0;
        if (best_stars[i] > 5) best_stars[i] = 5;
    }
}
static void save_progress(void)
{
    FILE *f = fopen("save.txt", "w");
    int i;
    if (!f) return;
    fprintf(f, "%d\n", unlocked);
    for (i = 0; i < LEVEL_COUNT; i++) fprintf(f, "%d ", best_stars[i]);
    fprintf(f, "\n");
    fclose(f);
}

/* 星级：看过关时省下多少步（五档） */
static int calc_stars(int left, int total)
{
    int r;
    if (total <= 0) return 1;
    r = left * 100 / total;
    if (r >= 55) return 5;
    if (r >= 42) return 4;
    if (r >= 30) return 3;
    if (r >= 15) return 2;
    return 1;
}

static const char *star_word(int s)
{
    switch (s) {
    case 5: return "优秀";
    case 4: return "很棒";
    case 3: return "不错";
    case 2: return "良好";
    default: return "及格";
    }
}

/* ---------------- 自测 ---------------- */

/* 贪心选一步：优先彩虹、双特效，其次消得最多；
   g_focus_type >= 0 时额外偏好"能消掉任务动物"的走法（更像真人运营） */
static int g_focus_type = -1;
static int g_focus_ice = 0;

static int best_move(int *r1, int *c1, int *r2, int *c2)
{
    int r, c, d, best = -1, probe[N][N];
    int br1 = -1, bc1 = -1, br2 = -1, bc2 = -1;

    for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
        int dirs[2][2] = {{0, 1}, {1, 0}};
        for (d = 0; d < 2; d++) {
            int r2i = r + dirs[d][0], c2i = c + dirs[d][1];
            int cnt = 0, fcnt = 0, icnt = 0, rr, cc, sc;
            if (r2i >= N || c2i >= N) continue;
            if (sp[r][c] && sp[r2i][c2i]) { *r1 = r; *c1 = c; *r2 = r2i; *c2 = c2i; return 1; }
            if (sp[r][c] == SP_RB || sp[r2i][c2i] == SP_RB) { *r1 = r; *c1 = c; *r2 = r2i; *c2 = c2i; return 1; }
            swap_cells(r, c, r2i, c2i);
            if (find_matches(probe))
                for (rr = 0; rr < N; rr++) for (cc = 0; cc < N; cc++)
                    if (probe[rr][cc]) {
                        cnt++;
                        if (type[rr][cc] == g_focus_type) fcnt++;
                        if (g_focus_ice && ice[rr][cc] > 0) icnt++;
                    }
            swap_cells(r, c, r2i, c2i);
            if (cnt <= 0) continue;
            sc = cnt * 10 + fcnt * 30 + icnt * 30;
            if (sc > best) { best = sc; br1 = r; bc1 = c; br2 = r2i; bc2 = c2i; }
        }
    }
    if (best < 0) return 0;
    *r1 = br1; *c1 = bc1; *r2 = br2; *c2 = bc2;
    return 1;
}

static void selftest(void)
{
    int L, total_win = 0;

    g_headless = 1;
    srand((unsigned)time(NULL));

    for (L = 0; L < LEVEL_COUNT; L++) {
        int guard = 0, r1, c1, r2, c2;
        start_level(L);
        g_focus_type = -1; g_focus_ice = 0;
        { int gi; for (gi = 0; gi < LEVELS[L].ng; gi++) {
              if (LEVELS[L].gk[gi] == G_ICE) g_focus_ice = 1;
              if (LEVELS[L].gk[gi] == G_COLLECT && g_focus_type < 0) g_focus_type = LEVELS[L].ga[gi];
          } }
        while (!level_over && guard++ < 300) {
            if (!best_move(&r1, &c1, &r2, &c2)) break;
            try_swap(r1, c1, r2, c2);
            if (goals_done()) { level_over = 1; level_win = 1; break; }
            if (moves <= 0) { level_over = 1; break; }
            if (!has_move()) shuffle_board();
        }
        if (level_win) {
            int used = LEVELS[L].moves - moves;
            int left = settle_bonus();
            int st = calc_stars(left, LEVELS[L].moves);
            total_win++;
            printf("L%-2d 过关 %d星 %s  分数 %-5d（含剩余 %d 步 +%d） 用步 %-2d 连消 %-2d 特效 %-2d\n",
                   L + 1, st, star_word(st), score, left, left * BONUS_PER_MOVE, used, combo_max, special_made);
        } else {
            printf("L%-2d 失败  分数 %-5d 用步 %-2d 连消 %-2d 特效 %-2d\n",
                   L + 1, score, LEVELS[L].moves - moves, combo_max, special_made);
        }
    }
    printf("\n自测结束：%d/%d 关通过\n", total_win, LEVEL_COUNT);
}

/* ---------------- 单关压测（调难度用） ---------------- */
static void grind(int lv, int runs)
{
    int i, win = 0, maxcol = 0, sumcol = 0, sumice = 0, maxice = 0, icegoal = 0;
    int sumscore = 0, maxscore = 0, scoregoal = 0;

    g_headless = 1;
    if (lv < 1) lv = 1;
    if (lv > LEVEL_COUNT) lv = LEVEL_COUNT;
    if (runs < 1) runs = 40;

    for (i = 0; i < LEVELS[lv - 1].ng; i++) {
        if (LEVELS[lv - 1].gk[i] == G_ICE) icegoal = LEVELS[lv - 1].gn[i];
        if (LEVELS[lv - 1].gk[i] == G_SCORE) scoregoal = LEVELS[lv - 1].gn[i];
    }

    for (i = 0; i < runs; i++) {
        int guard = 0, r1, c1, r2, c2;
        start_level(lv - 1);
        g_focus_type = -1;
        { int gi; for (gi = 0; gi < LEVELS[lv - 1].ng; gi++)
              if (LEVELS[lv - 1].gk[gi] == G_COLLECT && g_focus_type < 0) g_focus_type = LEVELS[lv - 1].ga[gi]; }
        g_focus_ice = (icegoal > 0) ? 1 : 0;
        while (!level_over && guard++ < 300) {
            if (!best_move(&r1, &c1, &r2, &c2)) break;
            try_swap(r1, c1, r2, c2);
            if (goals_done()) { level_over = 1; level_win = 1; break; }
            if (moves <= 0) { level_over = 1; break; }
            if (!has_move()) shuffle_board();
        }
        if (level_win) win++;
        if (LEVELS[lv - 1].gk[0] == G_COLLECT) {
            int got = collected[LEVELS[lv - 1].ga[0]];
            sumcol += got;
            if (got > maxcol) maxcol = got;
        }
        if (icegoal > 0) {
            int got = icegoal - ice_left();
            sumice += got;
            if (got > maxice) maxice = got;
        }
        sumscore += score;
        if (score > maxscore) maxscore = score;
    }
    printf("第 %d 关  %d 局：通过 %d 局（%.0f%%）", lv, runs, win, win * 100.0 / runs);
    if (LEVELS[lv - 1].gk[0] == G_COLLECT)
        printf("   收集量 平均 %.1f / 最高 %d（目标 %d）",
               (double)sumcol / runs, maxcol, LEVELS[lv - 1].gn[0]);
    if (icegoal > 0)
        printf("   清冰 平均 %.1f / 最高 %d（目标 %d）",
               (double)sumice / runs, maxice, icegoal);
    if (scoregoal > 0)
        printf("   分数 平均 %d / 最高 %d（目标 %d）",
               sumscore / runs, maxscore, scoregoal);
    printf("\n");
}


static void set_cell(int r, int c, int t, int s) { type[r][c] = t; sp[r][c] = s; }

static void make_checker(void)
{
    int r, c;
    for (r = 0; r < N; r++) for (c = 0; c < N; c++) {
        type[r][c] = (r + c) % 2;
        sp[r][c] = SP_NONE;
        ice[r][c] = 0;
    }
}

static void rule_test(void)
{
    int fails = 0, cells[128][2], n, i, ok;
    int mark[N][N];

    g_headless = 1;
    srand(12345);
    types_now = 6;
    level_idx = 0;

    /* 1. 炸弹只影响周围 3x3 */
    make_checker();
    set_cell(4, 4, 0, SP_BOMB);
    n = blast_cells(4, 4, cells);
    ok = (n == 9);
    for (i = 0; i < n; i++)
        if (abs(cells[i][0] - 4) > 1 || abs(cells[i][1] - 4) > 1) ok = 0;
    printf("[%s] 炸弹只炸周围 3x3（%d 格）\n", ok ? "PASS" : "FAIL", n);
    if (!ok) fails++;

    /* 2. 横向直线清整行 */
    make_checker();
    set_cell(3, 3, 0, SP_H);
    n = blast_cells(3, 3, cells);
    ok = (n == 8);
    for (i = 0; i < n; i++) if (cells[i][0] != 3) ok = 0;
    printf("[%s] 横向直线清整行（%d 格）\n", ok ? "PASS" : "FAIL", n);
    if (!ok) fails++;

    /* 3. 纵向直线清整列 */
    make_checker();
    set_cell(5, 5, 0, SP_V);
    n = blast_cells(5, 5, cells);
    ok = (n == 8);
    for (i = 0; i < n; i++) if (cells[i][1] != 5) ok = 0;
    printf("[%s] 纵向直线清整列（%d 格）\n", ok ? "PASS" : "FAIL", n);
    if (!ok) fails++;

    /* 4. 横向四连生成横线特效 */
    make_checker();
    memset(mark, 0, sizeof mark);
    mark[7][0] = mark[7][1] = mark[7][2] = mark[7][3] = 1;
    detect_creations(mark, 7, 3, 7, 3);
    ok = (nCre == 1 && creS[0] == SP_H && creR[0] == 7 && creC[0] == 3);
    printf("[%s] 横向四连 -> 清行的直线光\n", ok ? "PASS" : "FAIL");
    if (!ok) fails++;

    /* 5. 纵向四连生成竖线特效 */
    make_checker();
    memset(mark, 0, sizeof mark);
    mark[0][7] = mark[1][7] = mark[2][7] = mark[3][7] = 1;
    detect_creations(mark, 3, 7, 3, 7);
    ok = (nCre == 1 && creS[0] == SP_V && creR[0] == 3 && creC[0] == 7);
    printf("[%s] 纵向四连 -> 清列的直线光\n", ok ? "PASS" : "FAIL");
    if (!ok) fails++;

    /* 6. 彩虹 + 普通动物 = 清掉全场该种 */
    make_checker();
    set_cell(0, 0, 0, SP_RB);
    moves = 99;
    {
        int before = collected[1];
        try_swap(0, 0, 0, 1);
        ok = (collected[1] - before) >= 30;
        printf("[%s] 彩虹 + 普通动物，清掉全场同类（%d 只）\n", ok ? "PASS" : "FAIL", collected[1] - before);
        if (!ok) fails++;
    }

    /* 7. 直线/炸弹配普通动物，凑不出三连就不许炸 */
    make_checker();
    set_cell(0, 0, 0, SP_BOMB);
    {
        int mv = moves;
        try_swap(0, 0, 0, 1);
        ok = (moves == mv && sp[0][0] == SP_BOMB);
        printf("[%s] 炸弹配普通动物凑不出三连，原样弹回\n", ok ? "PASS" : "FAIL");
        if (!ok) fails++;
    }

    printf("\n规则验证：%d 项失败\n", fails);
}


/* ---------------- 主循环 ---------------- */
static int read_key(void)
{
    int k = _getch();
    if (k == 0 || k == 224) {
        k = _getch();
        if (k == 72) return 'U';
        if (k == 80) return 'D';
        if (k == 75) return 'L';
        if (k == 77) return 'R';
        return 0;
    }
    if (k == 13) return ' ';
    return k;
}

static void show_menu(void)
{
    int i, k;
    printf("\x1b[2J\x1b[H");
    printf("\n   \x1b[1;31m动物消消乐 · C 语言版\x1b[0m\n\n");
    printf("   输入关卡号开始（已解锁 1 - %d），直接回车进第 1 关，q 退出\n\n   ", unlocked);
    for (i = 0; i < LEVEL_COUNT; i++) {
        if (i + 1 <= unlocked) {
            printf("\x1b[1;33m%2d\x1b[0m ", i + 1);
            for (k = 0; k < 5; k++)
                printf(k < best_stars[i] ? "\x1b[33m★\x1b[0m" : "\x1b[90m☆\x1b[0m");
        } else {
            printf("\x1b[90m%2d ·····\x1b[0m", i + 1);
        }
        if ((i + 1) % 4 == 0) printf("\n   ");
        else printf("  ");
    }
    printf("\n\n   选择 > ");
    fflush(stdout);
}

int main(int argc, char **argv)
{
    int running = 1, L;

    SetConsoleOutputCP(65001);
    SetConsoleTitleA("动物消消乐 - C");
    srand((unsigned)time(NULL));

    if (argc > 1 && strcmp(argv[1], "--test") == 0) { selftest(); return 0; }
    if (argc > 1 && strcmp(argv[1], "--rule") == 0) { rule_test(); return 0; }
    if (argc > 1 && strcmp(argv[1], "--grind") == 0) {
        int lv = (argc > 2) ? atoi(argv[2]) : 1;
        int runs = (argc > 3) ? atoi(argv[3]) : 40;
        grind(lv, runs);
        return 0;
    }
    if (argc > 1 && strcmp(argv[1], "--demo") == 0) {
        int i;
        for (i = 0; i < MAXT; i++) collected[i] = 0;
        start_level(0);
        printf("\x1b[2J");
        draw();
        return 0;
    }

    {
        HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
        DWORD mode = 0;
        if (GetConsoleMode(h, &mode)) SetConsoleMode(h, mode | 0x0004);
    }
    setvbuf(stdout, NULL, _IONBF, 0);

    load_progress();

    /* 选关 */
    while (running) {
        char buf[8];
        int n;
        show_menu();
        if (!fgets(buf, sizeof buf, stdin)) { running = 0; break; }
        if (buf[0] == 'q' || buf[0] == 'Q') { running = 0; break; }
        n = atoi(buf);
        if (n <= 0) n = 1;
        if (n > unlocked) n = unlocked;
        if (n < 1) n = 1;

        start_level(n - 1);
        printf("\x1b[2J");
        draw();

        /* 关卡内循环 */
        while (!level_over) {
            int k = read_key();
            if (k == 'q' || k == 'Q') { level_over = 1; running = 0; break; }
            if (k == 'r' || k == 'R') { start_level(level_idx); printf("\x1b[2J"); draw(); continue; }
            if (k == 'h' || k == 'H') {
                int r1, c1, r2, c2;
                if (find_hint(&r1, &c1, &r2, &c2)) {
                    sprintf(g_msg, "试试 (%d,%d) 和 (%d,%d)", r1, c1, r2, c2);
                } else sprintf(g_msg, "没有可走的了，自动洗牌");
                draw();
                continue;
            }
            if (k == 'U' && cur_r > 0) cur_r--;
            else if (k == 'D' && cur_r < N - 1) cur_r++;
            else if (k == 'L' && cur_c > 0) cur_c--;
            else if (k == 'R' && cur_c < N - 1) cur_c++;
            else if (k == ' ') {
                if (sel_r < 0) { sel_r = cur_r; sel_c = cur_c; g_msg[0] = 0; }
                else if (sel_r == cur_r && sel_c == cur_c) { sel_r = -1; sel_c = -1; }
                else if (abs(sel_r - cur_r) + abs(sel_c - cur_c) == 1) {
                    int op_r = sel_r, op_c = sel_c;
                    sel_r = -1; sel_c = -1;
                    g_msg[0] = 0;
                    if (try_swap(op_r, op_c, cur_r, cur_c)) {
                        if (goals_done()) { level_over = 1; level_win = 1; }
                        else if (moves <= 0) level_over = 1;
                        if (!has_move()) { shuffle_board(); sprintf(g_msg, "没有可消的了，自动洗牌"); }
                    }
                } else { sel_r = cur_r; sel_c = cur_c; }
            }
            if (!level_over) draw();
        }

        draw();
        if (level_win) {
            int left = settle_bonus();
            int st = calc_stars(left, LEVELS[level_idx].moves);

            if (st > best_stars[level_idx]) best_stars[level_idx] = st;
            if (level_idx + 1 < LEVEL_COUNT && level_idx + 1 >= unlocked) {
                unlocked = level_idx + 2;
                if (unlocked > LEVEL_COUNT) unlocked = LEVEL_COUNT;
            }
            save_progress();

            draw();
            printf("\n  \x1b[1;32m过关！\x1b[0m  总分 \x1b[1;31m%d\x1b[0m（含剩余 %d 步奖励 +%d）\n",
                   score, left, left * BONUS_PER_MOVE);
            printf("  ");
            for (L = 0; L < 5; L++)
                printf(L < st ? "\x1b[1;33m★\x1b[0m " : "\x1b[90m☆\x1b[0m ");
            printf("   %d 星 · %s\n", st, star_word(st));
            if (st == 5)
                printf("\n   \x1b[41m\x1b[97m\x1b[1m  优秀  \x1b[0m  \x1b[1;31m红旗评定 · 表现满分！\x1b[0m\n");
        } else {
            printf("\n  \x1b[1;31m步数用完\x1b[0m  得分 %d\n", score);
        }
        printf("  按任意键回到选关...");
        fflush(stdout);
        _getch();
    }

    printf("\n  再见\n");
    return 0;
}
