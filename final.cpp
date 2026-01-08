/*
 * 程序名称：健身房会员管理系统（链表 + 文件持久化版本）
 *
 * 程序整体功能说明：
 *  1) 会员信息管理：新增会员、修改联系方式（电话）、删除会员（仅限过期/注销）、列表显示
 *  2) 查询功能：按卡号精确查询、按姓名关键字模糊查询
 *  3) 状态管理：自动到期同步（依据系统日期判断）、手动注销/标记过期（处理特殊管理场景）
 *  4) 续费/延长：未到期会员仅允许同类型续费（通过 bonus_days 叠加延长有效期，避免“超长月卡”等类型歧义）；
 *             过期/注销会员允许从今天重新购买任意类型
 *  5) 统计分析：有效会员数量、类型占比、30天内到期提醒
 *  6) 数据持久化：启动读取 members.txt；增删改/续费后写回文件；退出时再次保存
 *
 * 数据文件格式（文本，UTF-8）：每行一个会员记录，字段用 '|' 分隔：
 *  card_id|name|gender|age|phone|join_date|membership_type|is_active|bonus_days
 *
 * 说明：
 *  - Member 保存会员基础信息；Node 结点额外保存 bonus_days（同类型续费累计延长天数）
 *  - 写文件使用临时文件 members.tmp，写入成功后覆盖 members.txt，降低写入中断造成数据损坏风险
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

#define MAX_MEMBERS 100
#define DATA_FILE "members.txt"
#define TEMP_FILE "members.tmp"

/* 表格列宽（按“视觉宽度”计；用于中英文混排对齐输出） */
#define W_CARD   8
#define W_NAME   14
#define W_GENDER 6
#define W_AGE    6
#define W_PHONE  13
#define W_DATE   12
#define W_TYPE   8
#define W_STATUS 8
#define W_LEFT   10

/* 会员基本信息结构体 */
typedef struct {
    int card_id;                 /* 会员卡号（唯一） */
    char name[30];               /* 姓名（不含空格） */
    char gender[10];             /* 性别：男/女 */
    int age;                     /* 年龄：18~80 */
    char phone[15];              /* 手机号：11位数字 */
    char join_date[12];          /* 入会日期：YYYY-MM-DD */
    char membership_type[10];    /* 会员类型：月卡/季卡/年卡 */
    int is_active;               /* 状态：1=有效，0=过期/注销 */
} Member;

/*
 * 链表节点结构体：
 *  - data 保存会员基础信息
 *  - bonus_days 保存同类型续费累计延长天数（用于延长有效期而不改变会员类型含义）
 */
typedef struct Node {
    Member data;
    long bonus_days;
    struct Node* next;
} Node;

/* 全局链表指针与计数器（链表存储全部会员数据） */
static Node* head = NULL;
static Node* tail = NULL;
static int member_count = 0;
static int next_card_id = 1001;

/* ======= 菜单与业务函数声明 ======= */
void printMainMenu();
void printManageMenu();
void printSearchMenu();

void showAllMembers();
void addMember();
void updateMemberPhone();
void deleteExpiredMember();
void renewMember();               /* 续费/延长 */
void searchByCardID();
void searchByName();
void updateMemberStatus();        /* 手动注销/过期标记（不可逆） */
void showStatistics();

/* ======= 输入清理、校验、日期计算 ======= */
void clearInputBuffer();
void getSystemDate(char *buffer);

int isValidAge(int age);
int isValidPhone(const char *phone);

long dateToDays(const char* date);       /* 含闰年处理 */
int getDurationDays(const char* type);

void syncAutoExpire();                   /* 自动到期同步 */

/* ======= UTF-8 对齐输出辅助函数 ======= */
void printWithPad(const char *str, int target_width);
void printSeparator();
static uint32_t utf8_decode(const char *s, int *bytes);
static int char_width(uint32_t u);
static int is_cjk_wide(uint32_t u);

/* ======= 链表与文件持久化辅助函数 ======= */
Node* createNode(const Member* m);
void appendNode(Node* node);
Node* findByCardID(int id);
void freeAllMembers();

int loadFromFile(const char* filename);
int saveToFile(const char* filename);

/* ======= 初次运行测试数据 ======= */
void initTestData();

/* 计算会员到期日（累计：入会日期 + 套餐天数 + bonus_days） */
static long calcExpireDays(Node* p);

/* =========================================================
 *  输入缓冲清理与合法性校验
 * ========================================================= */

/* 清理输入缓冲区：用于处理 scanf 读入失败或残留的换行符 */
void clearInputBuffer() {
    int c;
    while ((c = getchar()) != '\n' && c != EOF);
}

/* 年龄合法性校验：要求 18~80 岁 */
int isValidAge(int age) {
    return (age >= 18 && age <= 80);
}

/* 手机号合法性校验：要求 11 位且全部为数字字符 */
int isValidPhone(const char *phone) {
    int len = (int)strlen(phone);
    if (len != 11) return 0;
    for (int i = 0; i < len; i++) {
        if (phone[i] < '0' || phone[i] > '9') return 0;
    }
    return 1;
}

/* 获取系统当前日期，格式：YYYY-MM-DD（用于自动到期同步与默认入会日期生成） */
void getSystemDate(char *buffer) {
    time_t t = time(NULL);
    struct tm *tm_info = localtime(&t);
    sprintf(buffer, "%04d-%02d-%02d", tm_info->tm_year + 1900, tm_info->tm_mon + 1, tm_info->tm_mday);
}

/* =========================================================
 *  日期换算（含闰年）：将 YYYY-MM-DD 映射到累计天数轴
 *  目的：保证天数差值等于真实天数差，用于跨月/跨年到期计算
 * ========================================================= */

static int isLeapYear(int y) {
    return (y % 4 == 0 && y % 100 != 0) || (y % 400 == 0);
}

static int daysInMonth(int y, int m) {
    static const int mdays[] = {0,31,28,31,30,31,30,31,31,30,31,30,31};
    if (m == 2) return mdays[m] + (isLeapYear(y) ? 1 : 0);
    return mdays[m];
}

/*
 * dateToDays：日期字符串 -> 累计天数
 * 关键语句说明：
 *  - 先累加整年天数 + 闰年修正
 *  - 再累加月份天数
 *  - 最后加上当月日
 */
long dateToDays(const char* date) {
    int y, m, d;
    if (sscanf(date, "%d-%d-%d", &y, &m, &d) != 3) return 0;
    if (m < 1 || m > 12) return 0;
    if (d < 1 || d > daysInMonth(y, m)) return 0;

    long days = 0;

    /* 计算 0..(y-1) 年中闰年的数量，用于修正累计天数 */
    long y1 = y - 1;
    long leapCount = y1 / 4 - y1 / 100 + y1 / 400;

    days += (long)y * 365 + leapCount;

    for (int i = 1; i < m; i++) days += daysInMonth(y, i);

    days += d;
    return days;
}

/* 会员类型对应的有效期天数 */
int getDurationDays(const char* type) {
    if (strcmp(type, "月卡") == 0) return 30;
    if (strcmp(type, "季卡") == 0) return 90;
    if (strcmp(type, "年卡") == 0) return 365;
    return 0;
}

/* =========================================================
 *  UTF-8 中英文混排对齐输出
 *  目的：printf 宽度按字节计算，中文在 UTF-8 下会造成列错位；
 *       本程序按“视觉宽度”计算并手动补空格，实现表格对齐。
 * ========================================================= */

/* utf8_decode：将一个 UTF-8 字符解码为 Unicode 码点，并返回占用字节数 */
static uint32_t utf8_decode(const char *s, int *bytes) {
    unsigned char c = (unsigned char)s[0];

    if (c < 0x80) { *bytes = 1; return c; }
    if ((c & 0xE0) == 0xC0) {
        *bytes = 2;
        return ((uint32_t)(c & 0x1F) << 6) | ((uint32_t)((unsigned char)s[1] & 0x3F));
    }
    if ((c & 0xF0) == 0xE0) {
        *bytes = 3;
        return ((uint32_t)(c & 0x0F) << 12) |
               ((uint32_t)((unsigned char)s[1] & 0x3F) << 6) |
               ((uint32_t)((unsigned char)s[2] & 0x3F));
    }
    if ((c & 0xF8) == 0xF0) {
        *bytes = 4;
        return ((uint32_t)(c & 0x07) << 18) |
               ((uint32_t)((unsigned char)s[1] & 0x3F) << 12) |
               ((uint32_t)((unsigned char)s[2] & 0x3F) << 6) |
               ((uint32_t)((unsigned char)s[3] & 0x3F));
    }
    *bytes = 1;
    return c;
}

/* 判断常见 CJK 宽字符范围：宽字符在控制台一般占 2 列 */
static int is_cjk_wide(uint32_t u) {
    return
        (u >= 0x1100 && u <= 0x115F) ||
        (u >= 0x2E80 && u <= 0xA4CF) ||
        (u >= 0xAC00 && u <= 0xD7A3) ||
        (u >= 0xF900 && u <= 0xFAFF) ||
        (u >= 0xFE10 && u <= 0xFE19) ||
        (u >= 0xFE30 && u <= 0xFE6F) ||
        (u >= 0xFF00 && u <= 0xFF60) ||
        (u >= 0xFFE0 && u <= 0xFFE6) ||
        (u >= 0x20000 && u <= 0x3FFFD);
}

static int char_width(uint32_t u) {
    if (u == 0) return 0;
    return is_cjk_wide(u) ? 2 : 1;
}

/*
 * printWithPad：按视觉宽度输出字符串，并补齐空格至 target_width
 * 关键处理：
 *  - 若字符串超过列宽，进行截断，避免挤占后续列导致错位
 */
void printWithPad(const char *str, int target_width) {
    int used = 0;
    for (int i = 0; str[i]; ) {
        int b = 0;
        uint32_t u = utf8_decode(str + i, &b);
        if (b <= 0) b = 1;

        int cw = char_width(u);
        if (used + cw > target_width) break;

        fwrite(str + i, 1, (size_t)b, stdout);
        used += cw;
        i += b;
    }
    for (int k = used; k < target_width; k++) putchar(' ');
}

/* 输出分隔线长度与表格列宽一致，保证整体格式规整 */
void printSeparator() {
    int total = W_CARD + 1 + W_NAME + 1 + W_GENDER + 1 + W_AGE + 1 + W_PHONE + 1
              + W_DATE + 1 + W_TYPE + 1 + W_STATUS + 1 + W_LEFT;
    for (int i = 0; i < total; i++) putchar('-');
    putchar('\n');
}

/* =========================================================
 *  链表管理：创建、追加、查找、释放
 * ========================================================= */

/* createNode：为一个会员记录分配链表结点并初始化 bonus_days=0 */
Node* createNode(const Member* m) {
    Node* node = (Node*)malloc(sizeof(Node));
    if (!node) return NULL;
    node->data = *m;
    node->bonus_days = 0;
    node->next = NULL;
    return node;
}

/* appendNode：尾插法追加结点；维护 tail 指针并更新 member_count */
void appendNode(Node* node) {
    if (!node) return;
    if (!head) head = tail = node;
    else { tail->next = node; tail = node; }
    member_count++;
}

/* findByCardID：按卡号在链表中查找会员结点；未找到返回 NULL */
Node* findByCardID(int id) {
    for (Node* p = head; p; p = p->next) {
        if (p->data.card_id == id) return p;
    }
    return NULL;
}

/* freeAllMembers：释放链表所有结点并清空全局状态 */
void freeAllMembers() {
    Node* p = head;
    while (p) {
        Node* nxt = p->next;
        free(p);
        p = nxt;
    }
    head = tail = NULL;
    member_count = 0;
}

/* calcExpireDays：计算会员到期日（入会日 + 套餐天数 + bonus_days） */
static long calcExpireDays(Node* p) {
    long join_days = dateToDays(p->data.join_date);
    int duration = getDurationDays(p->data.membership_type);
    return join_days + duration + p->bonus_days;
}

/* =========================================================
 *  自动到期同步：确保状态与系统日期一致
 * ========================================================= */

/*
 * syncAutoExpire：
 *  - 对 is_active==1 的会员计算剩余天数
 *  - 若剩余天数 < 0，则自动标记为过期（is_active=0）
 * 设计意义：避免依赖人工维护状态，保证列表/统计/查询的时效性
 */
void syncAutoExpire() {
    if (!head) return;

    char current_date_str[12];
    getSystemDate(current_date_str);
    long current_days = dateToDays(current_date_str);

    for (Node* p = head; p; p = p->next) {
        if (p->data.is_active == 1) {
            long expire_days = calcExpireDays(p);
            if (expire_days - current_days < 0) {
                p->data.is_active = 0;
            }
        }
    }
}

/* =========================================================
 *  文件持久化：读取与写回 members.txt
 * ========================================================= */

static void trim_newline(char* s) {
    s[strcspn(s, "\r\n")] = '\0';
}

/*
 * loadFromFile：读取 members.txt 并重建链表
 * 关键点：
 *  - 每行按 '|' 分割字段，并进行基本合法性校验
 *  - 读取完成后更新 next_card_id，避免新增卡号重复
 *  - 最后执行一次 syncAutoExpire，确保状态与当前时间一致
 */
int loadFromFile(const char* filename) {
    FILE* fp = fopen(filename, "rb");
    if (!fp) return 0;

    freeAllMembers();

    char line[512];
    int loaded = 0;
    int max_id = 1000;

    while (fgets(line, sizeof(line), fp)) {
        trim_newline(line);
        if (line[0] == '\0') continue;

        char buf[512];
        strcpy(buf, line);

        char* tok = strtok(buf, "|"); if (!tok) continue; int card_id = atoi(tok);
        tok = strtok(NULL, "|"); if (!tok) continue; char name[30]; strncpy(name, tok, sizeof(name)); name[29] = '\0';
        tok = strtok(NULL, "|"); if (!tok) continue; char gender[10]; strncpy(gender, tok, sizeof(gender)); gender[9] = '\0';
        tok = strtok(NULL, "|"); if (!tok) continue; int age = atoi(tok);
        tok = strtok(NULL, "|"); if (!tok) continue; char phone[15]; strncpy(phone, tok, sizeof(phone)); phone[14] = '\0';
        tok = strtok(NULL, "|"); if (!tok) continue; char join_date[12]; strncpy(join_date, tok, sizeof(join_date)); join_date[11] = '\0';
        tok = strtok(NULL, "|"); if (!tok) continue; char mtype[10]; strncpy(mtype, tok, sizeof(mtype)); mtype[9] = '\0';
        tok = strtok(NULL, "|"); if (!tok) continue; int is_active = atoi(tok);
        tok = strtok(NULL, "|"); if (!tok) continue; long bonus_days = atol(tok);

        /* 基本数据合法性校验：避免错误数据进入系统 */
        if (card_id <= 0) continue;
        if (!isValidAge(age)) continue;
        if (!isValidPhone(phone)) continue;
        if (!(strcmp(gender, "男") == 0 || strcmp(gender, "女") == 0)) continue;
        if (getDurationDays(mtype) == 0) continue;
        if (!(is_active == 0 || is_active == 1)) continue;
        if (dateToDays(join_date) == 0) continue;

        if (member_count >= MAX_MEMBERS) break;

        Member m;
        m.card_id = card_id;
        strcpy(m.name, name);
        strcpy(m.gender, gender);
        m.age = age;
        strcpy(m.phone, phone);
        strcpy(m.join_date, join_date);
        strcpy(m.membership_type, mtype);
        m.is_active = is_active;

        Node* node = createNode(&m);
        if (!node) break;
        node->bonus_days = bonus_days;

        appendNode(node);
        loaded++;

        if (card_id > max_id) max_id = card_id;
    }

    fclose(fp);

    next_card_id = max_id + 1;
    syncAutoExpire();
    return loaded;
}

/*
 * saveToFile：将链表数据写入 members.txt
 * 关键语句说明：
 *  - 先写 TEMP_FILE，再 rename 覆盖 DATA_FILE
 *  - 这种策略可降低写入过程中断导致的文件损坏风险
 */
int saveToFile(const char* filename) {
    FILE* fp = fopen(TEMP_FILE, "wb");
    if (!fp) return 0;

    for (Node* p = head; p; p = p->next) {
        fprintf(fp, "%d|%s|%s|%d|%s|%s|%s|%d|%ld\n",
                p->data.card_id,
                p->data.name,
                p->data.gender,
                p->data.age,
                p->data.phone,
                p->data.join_date,
                p->data.membership_type,
                p->data.is_active,
                p->bonus_days);
    }

    fclose(fp);

    remove(filename);
    if (rename(TEMP_FILE, filename) != 0) {
        remove(TEMP_FILE);
        return 0;
    }
    return 1;
}

/* =========================================================
 *  菜单显示函数：负责交互入口显示
 * ========================================================= */

void printMainMenu() {
    printf("\n=============================\n");
    printf("    健身房会员管理系统\n");
    printf("=============================\n");
    printf("1. 显示所有会员\n");
    printf("2. 会员信息管理\n");
    printf("3. 查询会员\n");
    printf("4. 会员状态更新(注销/过期)\n");
    printf("5. 统计分析\n");
    printf("0. 退出系统\n");
    printf("=============================\n");
}

void printManageMenu() {
    printf("\n------- 会员信息管理 -------\n");
    printf("1. 新增会员\n");
    printf("2. 修改会员信息 (仅限联系方式)\n");
    printf("3. 删除会员 (仅限已过期/已注销)\n");
    printf("4. 会员续费/延长 (月卡/季卡/年卡)\n");
    printf("0. 返回主菜单\n");
    printf("---------------------------\n");
}

void printSearchMenu() {
    printf("\n------- 查询会员 -------\n");
    printf("1. 按卡号查询\n");
    printf("2. 按姓名查询 (模糊)\n");
    printf("0. 返回主菜单\n");
    printf("-----------------------\n");
}

/* =========================================================
 *  业务功能函数实现
 * ========================================================= */

/*
 * showAllMembers：列表显示全部会员
 * 关键点：
 *  - 先同步到期状态（syncAutoExpire）
 *  - 对有效会员计算剩余天数；对过期会员显示 ---
 *  - 使用 printWithPad 实现中英文混排对齐
 */
void showAllMembers() {
    syncAutoExpire();

    if (member_count == 0) {
        printf("\n暂无会员信息。\n");
        return;
    }

    char current_date_str[12];
    getSystemDate(current_date_str);
    long current_days = dateToDays(current_date_str);

    printf("\n>>> 会员列表 (当前日期: %s)\n", current_date_str);
    printSeparator();

    printWithPad("卡号", W_CARD);       putchar(' ');
    printWithPad("姓名", W_NAME);       putchar(' ');
    printWithPad("性别", W_GENDER);     putchar(' ');
    printWithPad("年龄", W_AGE);        putchar(' ');
    printWithPad("电话", W_PHONE);      putchar(' ');
    printWithPad("入会日期", W_DATE);   putchar(' ');
    printWithPad("类型", W_TYPE);       putchar(' ');
    printWithPad("状态", W_STATUS);     putchar(' ');
    printWithPad("剩余天数", W_LEFT);   putchar('\n');

    printSeparator();

    for (Node* p = head; p; p = p->next) {
        char remain_str[32] = "---";
        if (p->data.is_active == 1) {
            long expire_days = calcExpireDays(p);
            long days_left = expire_days - current_days;
            sprintf(remain_str, "%ld 天", days_left);
        }

        printf("%-*d ", W_CARD, p->data.card_id);
        printWithPad(p->data.name, W_NAME);                         putchar(' ');
        printWithPad(p->data.gender, W_GENDER);                     putchar(' ');
        printf("%-*d ", W_AGE, p->data.age);
        printf("%-*s ", W_PHONE, p->data.phone);
        printf("%-*s ", W_DATE, p->data.join_date);
        printWithPad(p->data.membership_type, W_TYPE);              putchar(' ');
        printWithPad(p->data.is_active ? "有效" : "过期", W_STATUS); putchar(' ');
        printWithPad(remain_str, W_LEFT);                           putchar('\n');
    }

    printSeparator();
}

/*
 * addMember：新增会员
 * 输入约束：
 *  - 性别：仅允许“男/女”
 *  - 年龄：18~80
 *  - 电话：11位纯数字
 * 关键语句说明：
 *  - 卡号使用 next_card_id 自增生成，保证唯一性
 *  - 入会日期使用系统日期自动生成
 *  - 添加完成后立即写回文件，确保数据持久化
 */
void addMember() {
    if (member_count >= MAX_MEMBERS) {
        printf("会员库已满！\n");
        return;
    }

    Member m;
    m.card_id = next_card_id++;

    printf("\n--- 新增会员 (卡号: %d) ---\n", m.card_id);

    printf("请输入姓名: ");
    scanf("%29s", m.name);

    while (1) {
        printf("请输入性别 (男/女): ");
        scanf("%9s", m.gender);
        if (strcmp(m.gender, "男") == 0 || strcmp(m.gender, "女") == 0) break;
        printf("输入错误！只能输入 '男' 或 '女'。\n");
    }

    do {
        printf("请输入年龄 (18-80): ");
        if (scanf("%d", &m.age) != 1) {
            printf("输入非法！\n");
            clearInputBuffer();
            m.age = 0;
            continue;
        }
        if (!isValidAge(m.age)) printf("错误：年龄需在18-80之间！\n");
    } while (!isValidAge(m.age));

    do {
        printf("请输入电话 (11位手机号): ");
        scanf("%14s", m.phone);
        if (!isValidPhone(m.phone)) printf("错误：必须是11位纯数字，请重输！\n");
    } while (!isValidPhone(m.phone));

    getSystemDate(m.join_date);
    printf("入会日期: %s (系统自动生成)\n", m.join_date);

    int typeChoice;
    while (1) {
        printf("请选择会员类型:\n");
        printf("  1. 月卡\n  2. 季卡\n  3. 年卡\n");
        printf("请输入序号 (1-3): ");
        if (scanf("%d", &typeChoice) != 1) {
            printf("请输入数字！\n");
            clearInputBuffer();
            continue;
        }
        if (typeChoice == 1) { strcpy(m.membership_type, "月卡"); break; }
        if (typeChoice == 2) { strcpy(m.membership_type, "季卡"); break; }
        if (typeChoice == 3) { strcpy(m.membership_type, "年卡"); break; }
        printf("输入错误，请输入 1、2 或 3！\n");
    }

    m.is_active = 1;

    Node* node = createNode(&m);
    if (!node) {
        printf("内存分配失败，添加会员失败！\n");
        return;
    }
    appendNode(node);

    saveToFile(DATA_FILE);
    printf(">>> 会员添加成功！(已保存)\n");
}

/*
 * updateMemberPhone：修改会员联系方式（电话）
 * 输入约束：
 *  - 新电话必须为 11 位纯数字
 * 关键语句说明：
 *  - 通过卡号查找结点后只修改 phone 字段，保证其他信息不被误改
 *  - 修改完成后写回文件
 */
void updateMemberPhone() {
    int id;
    printf("请输入要修改的会员卡号: ");
    if (scanf("%d", &id) != 1) { printf("输入错误！\n"); clearInputBuffer(); return; }

    Node* p = findByCardID(id);
    if (!p) { printf("未找到该卡号。\n"); return; }

    printf("当前电话: %s\n", p->data.phone);

    char newPhone[15];
    do {
        printf("请输入新电话 (11位手机号): ");
        scanf("%14s", newPhone);
        if (!isValidPhone(newPhone)) printf("错误：必须是11位纯数字，请重输！\n");
    } while (!isValidPhone(newPhone));

    strcpy(p->data.phone, newPhone);

    saveToFile(DATA_FILE);
    printf("修改成功！(已保存)\n");
}

/*
 * deleteExpiredMember：删除会员（仅限过期/注销）
 * 关键语句说明：
 *  - 删除前先 syncAutoExpire，避免状态过时
 *  - 若 is_active==1，则拒绝删除，防止误删有效会员
 *  - 删除结点时维护 head/tail 指针与 member_count
 *  - 删除后写回文件
 */
void deleteExpiredMember() {
    syncAutoExpire();

    int id;
    printf("请输入要删除的会员卡号 (必须已过期/已注销): ");
    if (scanf("%d", &id) != 1) { printf("输入错误！\n"); clearInputBuffer(); return; }

    Node* prev = NULL;
    Node* cur = head;
    while (cur) {
        if (cur->data.card_id == id) break;
        prev = cur;
        cur = cur->next;
    }

    if (!cur) { printf("未找到该会员。\n"); return; }
    if (cur->data.is_active == 1) { printf("删除失败！会员仍有效。\n"); return; }

    if (!prev) head = cur->next;
    else prev->next = cur->next;

    if (cur == tail) tail = prev;

    free(cur);
    member_count--;

    saveToFile(DATA_FILE);
    printf("会员已删除。(已保存)\n");
}

/*
 * renewMember：会员续费/延长
 * 规则设计说明：
 *  1) 未到期且有效：仅允许同类型续费，通过 bonus_days 累加延长天数，不修改 membership_type
 *     （避免出现“390天月卡”等类型歧义，保持类型字段语义明确）
 *  2) 过期/注销：允许选择任意类型，从今天重新生效（更新 join_date，清空 bonus_days）
 *  3) 续费完成后写回文件
 */
void renewMember() {
    syncAutoExpire();

    int id;
    printf("请输入要续费的会员卡号: ");
    if (scanf("%d", &id) != 1) { printf("输入错误！\n"); clearInputBuffer(); return; }

    Node* p = findByCardID(id);
    if (!p) { printf("未找到该会员。\n"); return; }

    int typeChoice;
    char newType[10];
    int newDuration = 0;

    while (1) {
        printf("请选择续费类型:\n");
        printf("  1. 月卡(30天)\n  2. 季卡(90天)\n  3. 年卡(365天)\n");
        printf("请输入序号 (1-3): ");
        if (scanf("%d", &typeChoice) != 1) {
            printf("请输入数字！\n");
            clearInputBuffer();
            continue;
        }
        if (typeChoice == 1) { strcpy(newType, "月卡"); newDuration = 30; break; }
        if (typeChoice == 2) { strcpy(newType, "季卡"); newDuration = 90; break; }
        if (typeChoice == 3) { strcpy(newType, "年卡"); newDuration = 365; break; }
        printf("输入错误，请输入 1、2 或 3！\n");
    }

    char current_date_str[12];
    getSystemDate(current_date_str);
    long current_days = dateToDays(current_date_str);

    long expire_days = calcExpireDays(p);

    /* 过期/注销：从今天重新购买并生效，允许切换类型 */
    if (p->data.is_active == 0 || expire_days < current_days) {
        strcpy(p->data.join_date, current_date_str);
        p->bonus_days = 0;
        strcpy(p->data.membership_type, newType);
        p->data.is_active = 1;

        saveToFile(DATA_FILE);
        printf(">>> 续费成功！已从今天(%s)重新生效，类型：%s (已保存)\n",
               current_date_str, p->data.membership_type);
        return;
    }

    /* 未到期：仅允许同类型续费，类型不同则拒绝 */
    if (strcmp(newType, p->data.membership_type) != 0) {
        printf("续费失败：该会员仍在有效期内，不能更换类型。\n");
        printf("当前类型：%s。若需更换类型，请等待到期或先手动注销后再购买新类型。\n",
               p->data.membership_type);
        return;
    }

    p->bonus_days += newDuration;
    p->data.is_active = 1;

    saveToFile(DATA_FILE);
    printf(">>> 续费成功！已延长 %d 天，类型仍为：%s (已保存)\n",
           newDuration, p->data.membership_type);
}

/*
 * searchByCardID：按卡号精确查询
 * 关键点：
 *  - 查询前先 syncAutoExpire 确保状态实时
 *  - 有效会员额外输出剩余天数；过期会员显示 ---
 */
void searchByCardID() {
    syncAutoExpire();

    int id;
    printf("请输入查询卡号: ");
    if (scanf("%d", &id) != 1) { printf("输入错误！\n"); clearInputBuffer(); return; }

    Node* p = findByCardID(id);
    if (!p) { printf("未找到卡号 %d\n", id); return; }

    printf("\n>>> 查询结果:\n");
    printf("卡号: %d\n", p->data.card_id);
    printf("姓名: %s\n", p->data.name);
    printf("类型: %s\n", p->data.membership_type);
    printf("状态: %s\n", p->data.is_active ? "有效" : "过期");
    printf("入会日期: %s\n", p->data.join_date);

    char current_date_str[12];
    getSystemDate(current_date_str);
    long current_days = dateToDays(current_date_str);

    if (p->data.is_active == 1) {
        long days_left = calcExpireDays(p) - current_days;
        printf("剩余天数: %ld 天\n", days_left);
    } else {
        printf("剩余天数: ---\n");
    }
}

/*
 * searchByName：按姓名关键字模糊查询
 * 关键点：
 *  - 使用 strstr 实现子串匹配
 *  - 输出简表，便于管理员快速定位
 */
void searchByName() {
    syncAutoExpire();

    char key[30];
    printf("请输入姓名关键字: ");
    scanf("%29s", key);

    int found = 0;
    printf("\n>>> 搜索结果:\n");
    printSeparator();
    printWithPad("卡号", W_CARD);   putchar(' ');
    printWithPad("姓名", W_NAME);   putchar(' ');
    printWithPad("类型", W_TYPE);   putchar(' ');
    printWithPad("状态", W_STATUS); putchar('\n');
    printSeparator();

    for (Node* p = head; p; p = p->next) {
        if (strstr(p->data.name, key)) {
            printf("%-*d ", W_CARD, p->data.card_id);
            printWithPad(p->data.name, W_NAME);                    putchar(' ');
            printWithPad(p->data.membership_type, W_TYPE);         putchar(' ');
            printWithPad(p->data.is_active ? "有效" : "过期", W_STATUS);
            putchar('\n');
            found = 1;
        }
    }

    if (!found) printf("未找到。\n");
    printSeparator();
}

/*
 * updateMemberStatus：手动注销/标记过期（不可逆）
 * 设计意义：处理“退会/违规停用”等非自然到期场景，与自动到期同步互补
 * 关键点：
 *  - 仅修改 is_active 字段为 0
 *  - 修改后写回文件
 */
void updateMemberStatus() {
    int id;
    printf("请输入要注销/标记过期的卡号: ");
    if (scanf("%d", &id) != 1) { printf("输入错误！\n"); clearInputBuffer(); return; }

    Node* p = findByCardID(id);
    if (!p) { printf("未找到该会员。\n"); return; }

    if (p->data.is_active == 0) {
        printf("该会员已是过期/注销状态。\n");
        return;
    }

    p->data.is_active = 0;

    saveToFile(DATA_FILE);
    printf("会员 %s 已注销/标记为过期。(已保存)\n", p->data.name);
}

/*
 * showStatistics：统计分析
 * 输出内容：
 *  - 有效会员总数
 *  - 月卡/季卡/年卡数量与占比
 *  - 30天内到期提醒（依据剩余天数筛选）
 */
void showStatistics() {
    syncAutoExpire();

    if (member_count == 0) { printf("暂无数据。\n"); return; }

    int active_count = 0;
    int type_month = 0, type_season = 0, type_year = 0;

    char current_date_str[12];
    getSystemDate(current_date_str);
    long current_days = dateToDays(current_date_str);

    printf("\n======= 统计分析报表 =======\n");
    printf("系统当前日期: %s\n", current_date_str);

    for (Node* p = head; p; p = p->next) {
        if (p->data.is_active == 1) {
            active_count++;
            if (strcmp(p->data.membership_type, "月卡") == 0) type_month++;
            else if (strcmp(p->data.membership_type, "季卡") == 0) type_season++;
            else if (strcmp(p->data.membership_type, "年卡") == 0) type_year++;
        }
    }

    printf("---------------------------\n");
    printf("有效会员总数: %d 人\n", active_count);
    if (active_count > 0) {
        printf("  - 月卡: %d (%.1f%%)\n", type_month, (float)type_month / active_count * 100);
        printf("  - 季卡: %d (%.1f%%)\n", type_season, (float)type_season / active_count * 100);
        printf("  - 年卡: %d (%.1f%%)\n", type_year, (float)type_year / active_count * 100);
    }

    printf("---------------------------\n");
    printf(">>> 即将到期会员提示 (30天内):\n");

    int warning_count = 0;
    for (Node* p = head; p; p = p->next) {
        if (p->data.is_active == 1) {
            long days_left = calcExpireDays(p) - current_days;
            if (days_left >= 0 && days_left <= 30) {
                printf("  [警告] 卡号:%d 姓名:%s 还有 %ld 天到期！\n",
                       p->data.card_id, p->data.name, days_left);
                warning_count++;
            }
        }
    }

    if (warning_count == 0) printf("  暂无即将到期的会员。\n");
    printf("=============================\n");
}

/* =========================================================
 *  初次运行测试数据：当 members.txt 不存在/无有效数据时使用
 * ========================================================= */

/*
 * initTestData：生成初始演示数据并保存至 members.txt
 * 说明：用于首次运行或测试环境缺少数据文件时保证程序可直接演示
 */
void initTestData() {
    freeAllMembers();

    Member m1 = {1001, "张三", "男", 25, "13800138000", "2025-12-01", "年卡", 1};
    Member m2 = {1002, "李四", "女", 30, "13912345678", "2024-06-15", "月卡", 0};
    Member m3 = {1003, "王五", "男", 45, "13666666666", "2026-01-01", "月卡", 1};
    Member m4 = {1004, "赵六", "女", 22, "13777777777", "2025-11-01", "季卡", 1};

    Node* n1 = createNode(&m1);
    Node* n2 = createNode(&m2);
    Node* n3 = createNode(&m3);
    Node* n4 = createNode(&m4);

    if (!n1 || !n2 || !n3 || !n4) return;

    appendNode(n1);
    appendNode(n2);
    appendNode(n3);
    appendNode(n4);

    next_card_id = 1005;
    syncAutoExpire();
    saveToFile(DATA_FILE);
}

/* =========================================================
 *  主函数：程序入口
 * ========================================================= */

/*
 * main：
 *  - Windows 下切换控制台为 UTF-8（防止中文乱码）
 *  - 启动时优先读取 members.txt；若读取失败则生成测试数据
 *  - 主菜单循环驱动各模块
 *  - 退出前保存数据并释放链表内存
 */
int main() {
#ifdef _WIN32
    system("chcp 65001");
#endif

    int loaded = loadFromFile(DATA_FILE);
    if (loaded <= 0) {
        printf("提示：未检测到有效数据文件，已生成初始测试数据。\n");
        initTestData();
    } else {
        printf("提示：已从 %s 加载 %d 条会员数据。\n", DATA_FILE, loaded);
    }

    int choice;
    while (1) {
        printMainMenu();
        printf("请选择 (0-5): ");
        if (scanf("%d", &choice) != 1) {
            printf("输入错误，请输入数字！\n");
            clearInputBuffer();
            continue;
        }

        switch (choice) {
            case 1: showAllMembers(); break;

            case 2: {
                int subChoice;
                while (1) {
                    printManageMenu();
                    printf("请选择 (0-4): ");
                    if (scanf("%d", &subChoice) != 1) {
                        printf("输入错误，请输入数字！\n");
                        clearInputBuffer();
                        continue;
                    }
                    if (subChoice == 0) break;

                    switch (subChoice) {
                        case 1: addMember(); break;
                        case 2: updateMemberPhone(); break;
                        case 3: deleteExpiredMember(); break;
                        case 4: renewMember(); break;
                        default: printf("无效选项！\n");
                    }
                }
            } break;

            case 3: {
                int subChoice;
                while (1) {
                    printSearchMenu();
                    printf("请选择 (0-2): ");
                    if (scanf("%d", &subChoice) != 1) {
                        printf("输入错误，请输入数字！\n");
                        clearInputBuffer();
                        continue;
                    }
                    if (subChoice == 0) break;

                    switch (subChoice) {
                        case 1: searchByCardID(); break;
                        case 2: searchByName(); break;
                        default: printf("无效选项！\n");
                    }
                }
            } break;

            case 4: updateMemberStatus(); break;
            case 5: showStatistics(); break;

            case 0:
                saveToFile(DATA_FILE);
                printf("退出系统。(数据已保存)\n");
                freeAllMembers();
                return 0;

            default:
                printf("无效选项，请重新输入！\n");
        }
    }
}
